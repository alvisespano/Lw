(*
 * Lw
 * Typing/Meta.fs: kind inference, type evaluation etc.
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Meta


open FSharp.Common.Log
open FSharp.Common
open Lw.Core
open Lw.Core.Absyn
open Lw.Core.Globals
open Lw.Core.Typing.Defs
open Lw.Core.Typing.StateMonad
open Lw.Core.Typing.Ops


// kind unification
//

let rec kmgu (ctx : uni_context) k1_ k2_ =
    let ( ** ) = compose_ksubst
    let loc = ctx.loc
    let rec R k1 k2 =
      #if DEBUG_UNI && DEBUG_UNI_DEEP
      L.uni Low "[kmgu] %O == %O" k1 k2
      let θ as r =
      #endif
        match k1, k2 with
//        | k1, k2 when k1 = k2 ->
//            ksubst.empty
                                     
        | K_Cons (x1, ks1), K_Cons (x2, ks2) when x1 = x2 && ks1.Length = ks2.Length ->
            List.fold2 (fun tθ t t' -> let tθ' = R t t' in tθ' ** tθ) ksubst.empty ks1 ks2

        | K_Var α, k
        | k, K_Var α ->
            if Set.contains α k.fv then Report.Error.kind_circularity loc k1_ k2_ α k
            else new ksubst (α, k)

        | _ ->
            Report.Error.kind_mismatch loc k1_ k2_ k1 k2
      #if DEBUG_UNI && DEBUG_UNI_DEEP
      L.uni Low "[kmgu=] %O == %O\n        %O" k1 k2 θ
      r
      #endif
    in
        #if DEBUG_UNI && !DEBUG_UNI_DEEP
        L.uni Low "[kmgu] %O == %O" k1_ k2_
        #endif
        let θ as r = R k1_ k2_
        #if DEBUG_UNI && !DEBUG_UNI_DEEP
        L.uni Low "[kmgu=] %O == %O\n        %O" k1_ k2_ θ
        #endif                    
        r

type basic_builder with
    member M.kunify loc (k1 : kind) (k2 : kind) =
        M {
            let! θ = M.get_θ
            let kθ = θ.k
            let! ctx = M.get_uni_context loc
            let kθ = kmgu ctx (subst_kind kθ k1) (subst_kind kθ k2)
            do! M.update_θ (!> kθ)
        }

let private prompt_inferred_kind, prompt_evaluated_type = 
    let m = new System.Collections.Generic.Dictionary<_, _> (HashIdentity.Structural)
    let f1 ctx ss x kσ = m.Add (x, (ctx, ss, kσ))
    let f2 x t = let ctx, ss, kσ = m.[x] in Report.prompt ctx ss x kσ (Some (Config.Printing.type_evaluation_sep, t))
    in
        f1, f2


// type evaluation
//

[< RequireQualifiedAccess >]
module internal Eval =

    let rec ty_expr (ctx : context) (τ0 : ty_expr) =
        let M = new type_eval_builder<_> (τ0)
        M {            
            let rule =
                    match τ0.value with
                    | Te_Var _  -> "(E-VAR)"
                    | Te_App _      -> "(E-APP)"
                    | _             -> "[T]"
            let! θ = M.get_θ
            τ0.typed <- subst_kind θ.k τ0.typed // apply latest subst to each typed node
            let! ϕ = ty_expr' ctx τ0
            L.debug Min "%-7s %O\n[::k]   %O\n[T*]    %O" rule τ0 τ0.typed ϕ
            return ϕ
        } 

    and ty_expr' (ctx : context) (τ0 : ty_expr) : M<ty> =
        let M = new type_eval_builder<_> (τ0)
        let R = ty_expr ctx
        M {
            let k0 = τ0.typed       // this is the kind of the current ty_expr node being evaluated (annotated by previous Wk kind inference algorithm)
            match τ0.value with
            | Te_Var x ->
                let! α = M.search_or_add_scoped_var x
                yield T_Var (α, k0)

            | Te_Cons x ->
                let! too = M.search_δ x
                match too with
                | None   -> return Report.Error.unbound_type_symbol τ0.loc   yield T_Cons (x, k0)
                | Some t -> yield t

            | Te_Lambda ((x, _), τ) ->
                let! Δ = M.get_δ
                yield T_Closure (x, ref Δ, τ, k0)

            | Te_App (τ1, τ2) ->
                let! t1 = R τ1
                let! t2 = R τ2
                match t1 with
                | T_Closure (x, Δr, τ, _) ->
                    return! M.undo_δ <| M {
                        do! M.set_δ !Δr
                        do! M.bind_δ x t2
                        yield! R τ
                    }

                | _ ->
                    yield T_App (t1, t2)
                        
            | Te_Annot (τ, _) ->
                yield! R τ

            | Te_Forall ((x, _), τ) ->
                let! α = M.bind_scoped_var x
                let! t = R τ
                // check if quantified var is unused
                if t.search_var(α).IsNone then Report.Warn.unused_quantified_type_variable τ.loc α t
                yield T_Forall (α, t) 

            | Te_Let (d, τ1) ->
                yield! M.undo_δ <| M {
                    do! ty_decl ctx d
                    yield! R τ1
                }

            | Te_Row (xτs, τo) ->
                let! xts = M.List.map (fun (x : id, τ) -> M { let! t = R τ in return x, t }) xτs
                let! too = M.Option.map R τo
                match too with
                | Some (T_Row_Var α)        -> yield T_Row (xts, Some α)
                | Some (T_Row (xts', o))    -> yield T_Row (xts @ xts', o)
                | None                      -> yield T_Row (xts, None)
                | _                         -> return unexpected "non-row type in extension part of row type expression: %O" __SOURCE_FILE__ __LINE__ too

            | Te_HTuple ([] | [_]) -> return unexpected "empty or unary htuple type expression" __SOURCE_FILE__ __LINE__
            | Te_HTuple τs ->
                let! ts = M.List.map R τs
                yield T_HTuple ts

            | Te_Match (τ1, cases) ->
                let! t1 = R τ1
                yield! M.undo_δ <| M {
                    let! τo = M.List.tryPick (fun (p, _, τ) -> M { let! b = ty_patt ctx p t1 in if b then return Some τ else return None }) cases
                    match τo with
                    | None   -> return Report.Error.type_patterns_not_exhaustive τ1.loc t1
                    | Some τ -> yield! R τ
                }
        }

    and ty_bindings (ctx : context) d bs =
        let M = new type_eval_builder<_> (d)
        M {
            for { patt = p; expr = τ } in bs do
                let! t = ty_expr ctx τ
                do! M.ignore <| ty_patt ctx p t
                // prompt evaluated types
                let! Δ = M.get_δ
                for x in vars_in_ty_patt p do
                    prompt_evaluated_type x (Δ.lookup x)
        }

    and ty_rec_bindings<'e> (ctx : context) (d : node<'e, _>) bs =
        let M = new type_eval_builder<_> (d)
        M {
            let! Δ = M.get_δ
            let Δr = ref Env.empty
            Δr := List.fold (fun (Δ : tenv) { par = x, _; expr = τ } ->
                        let t = T_Closure (x, Δr, τ, τ.typed)
                        prompt_evaluated_type x t
                        Δ.bind x t) Δ bs
            do! M.set_δ !Δr
        }

    // like Wk_ty_decl, this must be defined AFTER the functions it calls
    and ty_decl ctx d =
        let M = new type_eval_builder<_> (d)
        M {
            match d.value with
            | Td_Bind bs ->
                do! ty_bindings ctx d bs

            | Td_Rec bs ->
                do! ty_rec_bindings ctx d bs

            | Td_Kind _ ->
                return not_implemented "%O" __SOURCE_FILE__ __LINE__ d
        }

    and ty_patt ctx (p : ty_patt) (t : ty) =
        let M = new type_eval_builder<_> (p)
        let R = ty_patt ctx
        M {
            match p.value, t with
            | Tp_Var x, t ->
                do! M.bind_δ x t
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
                if b then do! M.bind_δ x v
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

    let rec fxty_expr (ctx : context) (ϕτ0 : fxty_expr) =
        let M = new type_eval_builder<_> (ϕτ0)
        M {            
            let rule = "[Fx]"
            let! θ = M.get_θ
            ϕτ0.typed <- subst_kind θ.k ϕτ0.typed // apply latest subst to each typed node
            let! ϕ = fxty_expr' ctx ϕτ0
            L.debug Min "%-7s %O\n[::k]   %O\n[T*]    %O" rule ϕτ0 ϕτ0.typed ϕ
            return ϕ
        } 

    and fxty_expr' ctx ϕτ0 =
        let M = new type_eval_builder<_> (ϕτ0)
        let R = fxty_expr ctx
        let k0 = ϕτ0.typed       // this is the kind of the current ty_expr node being evaluated (annotated by previous Wk kind inference algorithm)
        M {
            match ϕτ0.value with
            | Fxe_Bottom ->
                return Fx_Bottom k0

            | Fxe_F_Ty τ ->
                let! t = ty_expr ctx τ
                return Fx_F_Ty t

            | Fxe_Forall (((x, ko), τo1), τ2) ->
                let! α = M.search_or_add_scoped_var x
                let! ϕ2 = E τ2                
                let! ϕ1 = M {
                    match τo1 with
                    | None ->
                        // check for unused quantified variable: because it's done on types rather than on type expressions, which would not allows for easy controlling scoping of the var itself
                        let k =
                            match ϕ2.ftype.search_var α with
                            | Some k -> k
                            | None   -> Report.Warn.unused_quantified_type_variable τ2.loc α ϕ2
                                        kind.fresh_var
                        in
                            return Fx_Bottom k

                    | Some τ1 -> return! E τ1
                }
                match ϕ1, ϕ2 with
                | Fx_Bottom _, Fx_F_Ty t -> yield T_Forall (α, t) 
                | _                      -> yield Fx_Forall ((α, ϕ1), ϕ2)
                
               
        }

// kind inference
//

let rec Wk_ty_expr (ctx : context) (τ0 : ty_expr) =
    let M = new kind_inference_builder<_> (τ0)
    M {
        let rule =
                match τ0.value with
                | Te_Var _  -> "(T-VAR)"
                | Te_App _      -> "(T-APP)"
                | _             -> "[T]"
        let! k = Wk_ty_expr' ctx τ0
        L.debug Min "%-7s %O\n[::k]   %O" rule τ0 k
        return k
    }

and Wk_ty_expr' (ctx : context) (τ0 : ty_expr) =
    let M = new kind_inference_builder<_> (τ0)
    let R = Wk_ty_expr ctx
    M {
        match τ0.value with
        | Te_Var x ->
            let! o1 = M.search_γ x
            let! o2 = M.search_scoped_var x
            match o1, o2 with
            | Some (KUngeneralized k), Some α ->
                yield k

            | None, None ->
                let α = kind.fresh_var
                let! _ = M.bind_γ x (KUngeneralized α)
                yield α

            | Some k, None ->
                return Report.Error.type_variable_bound_to_generalized_kscheme τ0.loc x k

            | x -> return unexpected_case __SOURCE_FILE__ __LINE__ x
                

        | Te_Cons x ->
            let! kσ = M.lookup_γ x
            yield kσ.instantiate

        | Te_Lambda ((x, ko), τ) ->
            let kx = either kind.fresh_var ko
            return! M.undo_γ <| M {
                let! _ = M.bind_γ x (KUngeneralized kx)
                let! k = R τ
                yield K_Arrow (kx, k)
            }

        | Te_HTuple ([] | [_]) -> return unexpected "empty or unary tupled type expression" __SOURCE_FILE__ __LINE__
        | Te_HTuple τs ->
            let! ks = M.List.map (fun τ -> M { yield! R τ }) τs
            yield K_HTuple ks
                                
        | Te_App (τ1, τ2) ->
            let! k1 = R τ1
            let! k2 = R τ2
            let α = kind.fresh_var
            do! M.kunify τ1.loc (K_Arrow (k2, α)) k1
            yield α

        | Te_Forall ((x, ko), τ) ->
            let kx = either kind.fresh_var ko
            return! M.undo_scoped_vars <| M {
                let! _ = M.bind_scoped_var x kx
                yield! R τ
            }

        | Te_Annot (τ, k) ->
            let! kτ = R τ
            do! M.kunify τ.loc k kτ
            yield k

        | Te_Let (d, τ) ->
            yield! M.undo_γ <| M {
                do! Wk_ty_decl { ctx with top_level_decl = false } d
                yield! R τ
            }                 

        | Te_Match (_, []) -> return unexpected "empty case list in match expression" __SOURCE_FILE__ __LINE__ 
        | Te_Match (τ1, cases) ->
            let! k1 = R τ1
            let kr0 = kind.fresh_var
            for p, _, τ in cases do
                do! M.undo_γ <| M {
                    let! kp = Wk_ty_patt ctx p
                    do! M.kunify p.loc k1 kp
                    let! tr = Wk_ty_expr ctx τ
                    do! M.kunify τ.loc kr0 tr
                }
            yield kr0

        | Te_Row (xτs, τo) ->
            for _, τ in xτs do
                let! k = R τ
                do! M.kunify τ.loc K_Star k
            do! M.Option.iter (fun τ -> M {
                        let! k = R τ
                        do! M.kunify τ.loc K_Row k
                    }) τo
            yield K_Row
    }

// TODO: deal with kindvars scoping; should resemble tyvars scoping, with restriction when generalization occurs etc
and Wk_ty_bindings (ctx : context) d bs =
    let M = new kind_inference_builder<_> (d)
    M {
        let! l = M.List.collect (fun { patt = p; expr = τ } -> M {
                    let! ke = Wk_ty_expr ctx τ
                    return! M.undo_γ <| M {
                        let! kp = Wk_ty_patt ctx p
                        do! M.kunify p.loc kp ke
                        return! M.List.map (fun x -> M { let! KUngeneralized k = M.lookup_γ x in return x, k }) (vars_in_ty_patt p |> Set.toList)
                    }
                }) bs
        for x, k in l do
            let! kσ = M.gen_and_bind_γ x k
            prompt_inferred_kind ctx Config.Printing.Prompt.type_decl_prefixes x kσ
    }   

and Wk_ty_rec_bindings<'e> (ctx : context) (d : node<'e, kind>) bs =
    let M = new kind_inference_builder<_> (d)
    M {
        let! bs = M.undo_γ <| M {
                for { par = x, ko } in bs do
                    let kx = either kind.fresh_var ko
                    do! M.ignore <| M.bind_γ x (KUngeneralized kx)
                return! M.List.map (fun { par = x, _; expr = τ } -> M {
                                let! KUngeneralized kx = M.lookup_γ x
                                let! k = Wk_ty_expr ctx τ
                                do! M.kunify τ.loc kx k
                                return x, kx
                        }) bs
            }
        for x, kx in bs do
            let! kσ = M.gen_and_bind_γ x kx
            // TODO: all type definitions should be implicitly recursive?
            prompt_inferred_kind ctx Config.Printing.Prompt.rec_type_decl_prefixes x kσ
    }

// this function must be defined AFTER the functions it recursively calls, otherwise F# type inference won't make them polymorphic
and Wk_ty_decl ctx d =
    let M = new kind_inference_builder<_> (d)
    M {
        match d.value with
        | Td_Bind bs ->
            return! Wk_ty_bindings ctx d bs

        | Td_Rec bs ->
            return! Wk_ty_rec_bindings ctx d bs

        | Td_Kind _ ->
            return not_implemented "%O" __SOURCE_FILE__ __LINE__ d
    }

and Wk_ty_patt ctx (p0 : ty_patt) =
    let K = new kind_inference_builder<_> (p0)
    let R = Wk_ty_patt ctx
    K {
        match p0.value with
        | Tp_Cons x ->
            let! kσ = K.lookup_γ x
            yield kσ.instantiate

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

let rec Wk_fxty_expr ctx ϕτ =
    let M = new kind_inference_builder<_> (ϕτ)
    let R = Wk_fxty_expr ctx
    M {
        match ϕτ.value with
        | Fxe_Bottom ->
            return kind.fresh_var

        | Fxe_F_Ty τ ->
            return! Wk_ty_expr ctx τ

        | Fxe_Forall (((x, ko), τo1), τ2) ->
            let kx = either kind.fresh_var ko
            match τo1 with
            | None    -> ()
            | Some τ1 ->
                let! k1 = R τ1
                do! M.kunify τ1.loc k1 kx
            return! M.undo_γ << M.undo_scoped_vars <| M {
                let! _ = M.bind_γ x (KUngeneralized kx)
                let! _ = M.search_or_add_scoped_var x
                yield! R τ2
            }
    }
        

// kind inference and type evaluation in one shot
//

let Wk_and_eval_ty_expr (ctx : context) τ =
    let M = new kind_inference_builder<_> (τ)
    M {
        let! k = Wk_ty_expr ctx τ
        let! t = Eval.ty_expr ctx τ
        return t.nf, k                  // evaluated flex type is normalized            
    }

let Wk_and_eval_ty_bindings (ctx : context) d bs =
    let M = new kind_inference_builder<_> (d)
    M {
        do! Wk_ty_bindings ctx d bs
        do! Eval.ty_bindings ctx d bs
    }

let Wk_and_eval_ty_rec_bindings (ctx : context) d bs =
    let M = new kind_inference_builder<_> (d)
    M {
        do! Wk_ty_rec_bindings ctx d bs
        do! Eval.ty_rec_bindings ctx d bs
    }

let Wk_and_eval_fxty_expr (ctx : context) τ =
    let M = new kind_inference_builder<_> (τ)
    M {
        let! ϕ, k = Wk_and_eval_ty_expr_fx ctx τ
        match ϕ.maybe_ftype with
        | Some t ->
            return t, k

        | None ->
            let t = ϕ.ftype
            Report.Warn.annot_flex_type_became_Ftype τ.loc ϕ t
            return t, k
    }




 