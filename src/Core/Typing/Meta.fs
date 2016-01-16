(*
 * Lw
 * Typing/Meta.fs: kind inference, type evaluation etc.
 * (C) 2000-2014 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Meta

open FSharp.Common.Prelude
open FSharp.Common.Log
open FSharp.Common
open Lw.Core
open Lw.Core.Absyn
open Lw.Core.Globals
open Lw.Core.Typing.Defs
open Lw.Core.Typing.StateMonad
open Lw.Core.Typing.Utils


type [< NoComparison; NoEquality >] mgu_context =
    { 
        loc            : location
        γ              : kjenv
    }


// kind unification
//

let rec kmgu (ctx : mgu_context) k1_ k2_ =
    let ( ** ) = compose_ksubst
    let loc = ctx.loc
    let rec R k1 k2 =
        match k1, k2 with
        | k1, k2 when k1 = k2 ->
            ksubst.empty
                                     
        | K_Cons (x1, ks1), K_Cons (x2, ks2) when x1 = x2 && ks1.Length = ks2.Length ->
            List.fold2 (fun θ t t' -> let θ' = R t t' in θ' ** θ) ksubst.empty ks1 ks2

        | K_Var α, k
        | k, K_Var α ->
            if Set.contains α k.fv then Report.Error.kind_circularity loc k1_ k2_ α k
            else new ksubst (α, k)

        | _ ->
            Report.Error.kind_mismatch loc k1_ k2_ k1 k2
    in
        R k1_ k2_

type basic_builder with
    member M.kunify loc (k1 : kind) (k2 : kind) =
        M {
            let! { Θ = Θ; γ = γ } = M.get_state
            let Θ = kmgu { loc = loc; γ = γ } (subst_kind Θ k1) (subst_kind Θ k2)
            L.mgu "[kU] %O == %O [%O]" k1 k2 Θ
            do! M.update_subst (tsubst.empty, Θ)
        }

let private prompt_inferred_kind, prompt_evaluated_type = 
    let m = new System.Collections.Generic.Dictionary<_, _> (HashIdentity.Structural)
    let f1 ctx ss x ς = m.Add (x, (ctx, ss, ς))
    let f2 x t = let ctx, ss, ς = m.[x] in Report.prompt ctx ss x ς (Some t)
    in
        f1, f2


// type evaluation
//

module private Eval =

    let rec eval_ty_expr (ctx : context) (τ : ty_expr) =
        let M = new translator_typing_builder<_, _> (τ)
        M {            
            let! _, Θ = M.get_Σ
            τ.typed <- subst_kind Θ τ.typed // apply latest subst to each typed node
            let! t = eval_ty_expr' ctx τ
            L.debug Min "[t::K] %O\n :: %O\n[T*]   %O" τ τ.typed t
            return t
        } 

    and eval_ty_expr' (ctx : context) (τ0 : ty_expr) =
        let M = new translator_typing_builder<_, _> (τ0)
        let E = eval_ty_expr ctx
        M {
            let k0 = τ0.typed
            match τ0.value with
            | Te_PolyVar x ->
                let! α = M.add_named_tyvar x
                yield T_Var (α, k0)

            | Te_Id x ->
                yield T_Cons (x, k0)

            | Te_Lambda ((x, _), τ) ->
                let! Δ = M.get_Δ
                yield T_Closure (x, ref Δ, τ, k0)

            | Te_App (τ1, τ2) ->
                let! t1 = E τ1
                let! t2 = E τ2
                match t1 with
                | T_Closure (x, Δr, τ, _) ->
                    return! M.fork_Δ <| M {
                        do! M.set_Δ !Δr
                        do! M.bind_Δ x t2
                        yield! E τ
                    }

                | _ ->
                    yield T_App (t1, t2)
                        
            | Te_Annot (τ, _) ->
                yield! E τ

            | Te_Forall (((x, _), τo1), τ2) ->
                let! t1 = M.Option.something (fun τ1 -> M { return! E τ1 }) T_Bottom τo1
                let! α = M.add_named_tyvar x
                let! t2 = E τ2                
                yield T_Forall ((α, t1), t2)

            | Te_Let (d, τ1) ->
                yield! M.fork_Δ <| M {
                    do! eval_ty_decl ctx d
                    yield! E τ1
                }

            | Te_Row (xτs, τo) ->
                let! xts = M.List.map (fun (x, τ) -> M { let! t = E τ in yield x, t }) xτs
                let! too = M.Option.map (fun τ -> M { yield! E τ }) τo
                match too with
                | Some (T_Row_Var α)        -> yield T_Row (xts, Some α)
                | Some (T_Row (xts', o))    -> yield T_Row (xts @ xts', o)
                | None                      -> yield T_Row (xts, None)
                | _                         -> return unexpected "non-row type in extension part of row type expression: %O" __SOURCE_FILE__ __LINE__ too

            | Te_HTuple ([] | [_]) -> return unexpected "empty or unary htuple type expression" __SOURCE_FILE__ __LINE__
            | Te_HTuple τs ->
                let! ts = M.List.map (fun τ -> M { yield! E τ }) τs
                yield T_HTuple ts

            | Te_Match (τ1, cases) ->
                let! t1 = E τ1
                yield! M.fork_Δ <| M {
                    let! τo = M.List.tryPick (fun (p, _, τ) -> M { let! b = eval_ty_patt ctx p t1 in if b then return Some τ else return None }) cases
                    match τo with
                    | None   -> return Report.Error.type_patterns_not_exhaustive τ1.loc t1
                    | Some τ -> yield! E τ
                }
        }

    and eval_ty_decl ctx d =
        let M = new basic_builder (d.loc)
        M {
            match d.value with
            | Td_Bind bs ->
                do! eval_ty_bindings ctx d.loc bs

            | Td_Rec bs ->
                do! eval_ty_rec_bindings ctx d.loc bs

            | Td_Kind _ ->
                return not_implemented "%O" __SOURCE_FILE__ __LINE__ d
        }

    and eval_ty_bindings (ctx : context) loc bs =
        let M = new basic_builder (loc)
        M {
            for { patt = p; expr = τ } in bs do
                let! t = eval_ty_expr ctx τ
                do! M.ignore <| eval_ty_patt ctx p t
                // prompt evaluated types
                let! Δ = M.get_Δ
                for x in vars_in_ty_patt p do
                    prompt_evaluated_type x (Δ.lookup x)
        }

    and eval_ty_rec_bindings (ctx : context) loc bs =
        let M = new basic_builder (loc)
        M {
            let! Δ = M.get_Δ
            let Δr = ref Env.empty
            Δr := List.fold (fun (Δ : tenv) { par = x, _; expr = τ } ->
                        let t = T_Closure (x, Δr, τ, τ.typed)
                        prompt_evaluated_type x t
                        Δ.bind x t) Δ bs
            do! M.set_Δ !Δr
        }

    and eval_ty_patt ctx (p : ty_patt) t =
        let M = new basic_builder (p.loc)
        let R = eval_ty_patt ctx
        M {
            match p.value, t with
            | Tp_Var x, t ->
                do! M.bind_Δ x t
                return true

            | Tp_Or (p1, p2), t ->
                let! b1 = R p1 t
                let! b2 = R p2 t
                return b1 || b2

            | Tp_And (p1, p2), t ->
                let! b1 = R p1 t
                let! b2 = R p2 t
                return b1 && b2

            | Tp_Cons x, T_Cons (x', _) when x = x' ->
                return true

            | Tp_Annot (p, _), v ->
                return! R p v

            | Tp_As (p, x), v ->
                let! b = R p v
                if b then do! M.bind_Δ x v
                return b

            | Tp_Wildcard, _ ->
                return true

            | Tp_App (p1, p2), T_App (t1, t2) ->
                let! b1 = R p1 t1
                let! b2 = R p2 t2
                return b1 && b2

            | Tp_HTuple ps, T_HTuple ts when ps.Length = ts.Length ->
                return! M.List.fold2 (fun b p t -> M {
                                let! b' = R p t
                                return b && b'
                            }) true ps ts          

            | Tp_Row (xps, po), T_Row (xts, αo) when List.forall (fun (x, _) -> List.exists (fun (x', _) -> x = x') xts) xps ->
                let! b = M.List.fold (fun b (x, p) -> M {
                                let t = X.List.find_assoc_fst x xts
                                let! b' = R p t
                                return b && b'
                            }) true xps
                match po, αo with
                | Some p, Some α -> let! b' = R p (T_Row_Var α) in return b' && b
                | None, None     -> return b
                | _              -> return false

            | _ ->
                return false 
        }



// kind inference
//

//#region kind inference

let rec pk_ty_expr (ctx : context) (τ0 : ty_expr) =
    let K = new kinding_builder<_> (τ0)
    K {
        let! k = pk_ty_expr' ctx τ0
        L.debug Min "[t::K] %O\n      :: %O\n" τ0 k
        return k
    }

and pk_ty_expr' (ctx : context) (τ0 : ty_expr) =
    let K = new kinding_builder<_> (τ0)
    let R = pk_ty_expr ctx
    K {
        match τ0.value with
        | Te_PolyVar x ->
            let! o = K.search_γ x
            match o with
            | Some (KUngeneralized k) ->
                yield k

            | None ->
                let α = K_Var var.fresh
                let! _ = K.bind_γ x (KUngeneralized α)
                yield α

        | Te_Id x ->
            let! ς = K.lookup_γ x
            yield kinstantiate ς

        | Te_Lambda ((x, ko), τ) ->
            let kx = either kind.fresh_var ko
            return! K.fork_γ <| K {
                let! _ = K.bind_γ x (KUngeneralized kx)
                let! k = R τ
                yield K_Arrow (kx, k)
            }

        | Te_HTuple ([] | [_]) -> return unexpected "empty or unary tupled type expression" __SOURCE_FILE__ __LINE__
        | Te_HTuple τs ->
            let! ks = K.List.map (fun τ -> K { yield! R τ }) τs
            yield K_HTuple ks
                                
        | Te_App (τ1, τ2) ->
            let! k1 = R τ1
            let! k2 = R τ2
            let α = kind.fresh_var
            do! K.kunify τ1.loc (K_Arrow (k2, α)) k1
            yield α

        // TODO: design the kind inference of forall term more carefully
        | Te_Forall (((x, ko), τo1), τ2) ->
            let kx = either kind.fresh_var ko
            match τo1 with
            | None -> ()
            | Some τ1 -> do! K.ignore <| R τ1  // nothing to do with k1?
            return! K.fork_γ <| K {
                let! _ = K.bind_γ x (KUngeneralized kx)
                yield! R τ2
            }

        | Te_Annot (τ, k) ->
            let! kτ = R τ
            do! K.kunify τ.loc k kτ
            yield k

        | Te_Let (d, τ) ->
            yield! K.fork_γ <| K {
                do! pk_ty_decl { ctx with top_level_decl = false } d
                yield! R τ
            }                 

        | Te_Match (_, []) -> return unexpected "empty case list in match expression" __SOURCE_FILE__ __LINE__ 
        | Te_Match (τ1, cases) ->
            let! k1 = R τ1
            let kr0 = kind.fresh_var
            for p, _, τ in cases do
                do! K.fork_γ <| K {
                    let! kp = pk_ty_patt ctx p
                    do! K.kunify p.loc k1 kp
                    let! tr = pk_ty_expr ctx τ
                    do! K.kunify τ.loc kr0 tr
                }
            yield kr0

        | Te_Row (xτs, τo) ->
            for _, τ in xτs do
                let! k = R τ
                do! K.kunify τ.loc K_Star k
            do! K.Option.iter (fun τ -> K {
                        let! k = R τ
                        do! K.kunify τ.loc K_Row k
                    }) τo
            yield K_Row
    }

and pk_ty_decl ctx d =
    let M = new basic_builder (d.loc)
    M {
        match d.value with
        | Td_Bind bs ->
            return! pk_ty_bindings ctx d.loc bs

        | Td_Rec bs ->
            return! pk_ty_rec_bindings ctx d.loc bs

        | Td_Kind _ ->
            return not_implemented "%O" __SOURCE_FILE__ __LINE__ d
    }

// TODO: deal with kindvars scoping; should resemble tyvars scoping, with restriction when generalization occurs etc.
and pk_ty_bindings (ctx : context) loc bs =
    let M = new basic_builder (loc)
    M {
        let! l = M.List.collect (fun { patt = p; expr = τ } -> M {
                    let! ke = pk_ty_expr ctx τ
                    return! M.fork_γ <| M {
                        let! kp = pk_ty_patt ctx p
                        do! M.kunify p.loc kp ke
                        return! M.List.map (fun x -> M { let! (KUngeneralized k) = M.lookup_γ x in return x, k }) (vars_in_ty_patt p |> Set.toList)
                    }
                }) bs
        for x, k in l do
            let! ς = M.gen_bind_γ x k
            prompt_inferred_kind ctx Config.Printing.Prompt.type_decl_prefixes x ς
    }   

and pk_ty_rec_bindings (ctx : context) loc bs  =
    let M = new basic_builder (loc)
    M {
        let! bs = M.fork_γ <| M {
                for { par = x, ko } in bs do
                    let kx = either kind.fresh_var ko
                    do! M.ignore <| M.bind_γ x (KUngeneralized kx)
                return! M.List.map (fun { par = x, _; expr = τ } -> M {
                                let! KUngeneralized kx = M.lookup_γ x
                                let! k = pk_ty_expr ctx τ
                                do! M.kunify τ.loc kx k
                                return x, kx
                        }) bs
            }
        for x, kx in bs do
            let! ς = M.gen_bind_γ x kx
            // TODO: all type definitions should be implicitly recursive
            prompt_inferred_kind ctx Config.Printing.Prompt.rec_type_decl_prefixes x ς
    }

and pk_ty_patt ctx (p0 : ty_patt) =
    let K = new kinding_builder<_> (p0)
    let R = pk_ty_patt ctx
    K {
        match p0.value with
        | Tp_Cons x ->
            let! ς = K.lookup_γ x
            yield kinstantiate ς

        | Tp_Var x ->
            let α = kind.fresh_var
            let! _ = K.bind_γ x (KUngeneralized α)
            yield α

        | Tp_Or (p1, p2) ->
            let! k1 = R p1
            let! k2 = R p2
            do! K.kunify p2.loc k1 k2
            let xs1 = vars_in_ty_patt p1
            let xs2 = vars_in_ty_patt p2
            let missing = (xs1 + xs2) - Set.intersect xs1 xs2
            if not (Set.isEmpty missing) then Report.Error.different_vars_in_sides_of_or_pattern p0.loc missing
            yield k1

        | Tp_And (p1, p2) ->
            let! k1 = R p1
            let! k2 = R p2
            do! K.kunify p1.loc k1 k2
            yield k1

        | Tp_HTuple ([] | [_]) -> return unexpected "empty or unary tuple type pattern" __SOURCE_FILE__ __LINE__
        | Tp_HTuple ps ->
            let! ks = K.List.map R ps
            yield K_HTuple ks

        | Tp_App (p1, p2) ->
            let! k1 = R p1
            let! k2 = R p2
            let α = kind.fresh_var
            do! K.kunify p1.loc (K_Arrow (k2, α)) k1
            yield α

        | Tp_Wildcard ->
            yield kind.fresh_var

        | Tp_Row (xps, po) ->
            for _, τ in xps do
                let! k = R τ
                do! K.kunify τ.loc K_Star k
            match po with
            | None -> ()
            | Some τ ->
                let! k = R τ
                do! K.kunify τ.loc K_Row k
            yield K_Row

        | Tp_As (p, x) ->
            let! kp = R p
            let! _ = K.bind_γ x (KUngeneralized kp)
            yield kp

        | Tp_Annot (p, k) ->
            let! kp = R p
            do! K.kunify p.loc k kp
            yield k         
    }

//#endregion

// kind inference and type evaluation in one shot
//

let pk_and_eval_ty_expr (ctx : context) τ =
    let M = new translator_typing_builder<_, _> (τ)
    M {
        let! k = pk_ty_expr ctx τ
        let! t = Eval.eval_ty_expr ctx τ
        return t, k                         
    }

let pk_and_eval_ty_bindings (ctx : context) loc bs =
    let M = new basic_builder (loc)
    M {
        do! pk_ty_bindings ctx loc bs
        do! Eval.eval_ty_bindings ctx loc bs
    }

let pk_and_eval_ty_rec_bindings (ctx : context) loc bs =
    let M = new basic_builder (loc)
    M {
        do! pk_ty_rec_bindings ctx loc bs
        do! Eval.eval_ty_rec_bindings ctx loc bs
    }






 