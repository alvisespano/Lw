(*
 * Lw
 * Typing/Unify.fs: unification algorithms
 * (C) 2000-2014 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Unify

open FSharp.Common.Prelude
open FSharp.Common.Log
open FSharp.Common
open Lw.Core.Absyn
open Lw.Core.Globals
open Lw.Core.Typing.Defs
open Lw.Core.Typing.StateMonad
open Lw.Core.Typing.Meta
open Lw.Core.Typing.Utils
open Lw.Core
open System.Diagnostics


// unification
//

exception Mismatch of ty * ty

let rec rewrite_row loc t1 t2 r0 l =
    let R = rewrite_row loc t1 t2
    L.mgu "[I] %O ~= %s" r0 l
    match r0 with
    | T_Row_Ext (l', t', r) ->
        if l' = l then t', r, tsubst.empty
        else
            let t, r', tθ = R r l
            in
                t, T_Row_Ext (l', t', r'), tθ

    | T_Row_Var ρ ->
        let α = ty.fresh_var
        let β = T_Row_Var var.fresh
        let t = T_Row_Ext (l, α, β)
        in
            α, β, new tsubst (ρ, t)

    | T_Row_Empty ->
        Report.Error.cannot_rewrite_row loc l t1 t2

    | T_NoRow _ ->
        unexpected "row type expected: %O" __SOURCE_FILE__ __LINE__ r0
                
// this implementation differs from HML definition, but it should be equivalent
let dom_wrt Q (t : ty) = 
    let αs = t.fv
    in
        Computation.set { for α, t : ty in Q do if Set.contains α αs then yield! t.fv }

// match System-F quantifiers
let (|T_Foralls_F|_|) = function
    | T_Foralls (Q, t) when List.forall (function _, T_Bottom -> true | _ -> false) Q -> Some (List.map fst Q, t)
    | _ -> None


[< RequireQualifiedAccess >]
module internal Mgu =


    let (|T_NamedVar|_|) = function
        | T_Var (Va (_, Some _) as α, k) -> Some (α, k)
        | _ -> None

    module Pure =

//        type ty with
//            static member skolemize_var α = T_Cons (sprintf Config.Typing.skolemized_tyvar_fmt α, )

        // TODO: [continue] probably T_Forall needs to carry kinds along with quantified vars: this would also make sense to kind inference, which currently discards the kind inferred for quantified vars
        let skolemized = function
            | T_Foralls (Q, t) when not Q.IsEmpty ->
                let t = t.apply_to_vars (fun α k -> if List.exists (fun (β, _) -> α = β) Q then T_Cons (sprintf Config.Typing.skolemized_tyvar_fmt α.pretty, k) else T_Var (α, k))
                in
                    Seq.map snd m.toSeq, t

            | t -> [], t


        let rec subsume ctx Q (t1 : ty) (t2 : ty) =
            assert (t1.is_nf && t2.is_nf)
            match t1, t2 with
            | T_Foralls_F (αs, t1), T_Foralls (Q2, t2) ->
                assert (prefix_dom Q <> prefix_dom Q2)
                let tsks, t1' = skolemized t1
                let Q1, (tθ1, _ as θ1 : tksubst) = mgu ctx (Q @ Q2) t1' t2
                let Q2, Q3 = split_prefix Q1 (prefix_dom Q)
                let θ2 = tθ1.remove (prefix_dom Q3)
                // for each skolemized variable check it does not escape
                for tsk in tsks do
                    // either via the substitution
                    let b1 = (θ2.search_by (fun _  t -> t = tsk)).IsSome
                    // or via the prefix
                    let b2 = List.exists (function _, t -> t = tsk) Q2
                    if b1 || b2 then Report.Error.skolemized_type_variable_escaped ctx.loc tsk
                Q2, (θ2, ksubst.empty)

            | _ -> Q, (tsubst.empty, ksubst.empty)

        and mgu (ctx : mgu_context) Q t1_ t2_ =
            let ( ** ) = compose_tksubst
            let S = subst_ty
            let loc = ctx.loc
            let rec R (Q0 : prefix) t1 t2 =
                match t1, t2 with
                | T_Cons (x, k1), T_Cons (y, k2) when x = y -> Q0, (tsubst.empty, kmgu ctx k1 k2)
                | T_Var (α, k1), T_Var (β, k2) when α = β   -> Q0, (tsubst.empty, kmgu ctx k1 k2)
                                      
                | (T_Row _ as s), T_Row_Ext (l, t, (T_Row (_, ρo) as r)) ->
                    let t', s', tθ1 = rewrite_row loc t1 t2 s l
                    let θ1 = tθ1, ksubst.empty
                    Option.iter (fun ρ -> if Set.contains ρ tθ1.dom then Report.Error.row_tail_circularity loc ρ tθ1) ρo
                    let Q2, θ2 = R Q0 (S θ1 t) (S θ1 t')
                    let Q3, θ3 = let θ = θ2 ** θ1 in R Q2 (S θ r) (S θ s')
                    in
                        Q3, θ3 ** θ2 ** θ1
                    
                | T_Var (α, k), (T_NamedVar _ as t) // prefer named tyvars over anonymous tyvars when unifying tyvar against tyvar
                | (T_NamedVar _ as t), T_Var (α, k)
                | T_Var (α, k), t
                | t, T_Var (α, k) ->
                    let αt =
                        match List.tryFind (function β, _ -> α = β) Q0 with
                        | Some (_, t) -> t
                        | None        -> unexpected "type variable %O does not occur in prefix" __SOURCE_FILE__ __LINE__ α
                    let θ0 = tsubst.empty, kmgu ctx k t.kind                    
                    // occurs check
                    if Set.contains α (dom_wrt Q t) then let S = S θ0 in Report.Error.circularity loc (S t1_) (S t2_) (S (T_Var (α, k))) (S t)
                    let Q1, θ1 = subsume ctx Q t αt
                    let Q2, θ2 = update_prefix Q1 (new tsubst (α, S θ1 t))
                    in
                        Q2, θ2 ** θ1

                | T_App (t1, t2), T_App (t1', t2') ->
                    let Q1, θ1 = R Q0 t1 t1'
                    let Q2, θ2 = R Q1 (S θ1 t2) (S θ1 t2')
                    in
                        Q2, θ2 ** θ1
                                                           
                | t1, t2 ->
                    raise (Mismatch (t1, t2))

            assert (t1_.is_nf && t2_.is_nf)
            try R Q t1_ t2_
            with Mismatch (t1, t2) -> Report.Error.type_mismatch loc t1_ t2_ t1 t2


    module Computational =
       
        let private __tYield _Yield (tθ : tsubst) = _Yield ((tθ, ksubst.empty))
        let private __kYield _Yield (kθ : ksubst) = _Yield ((tsubst.empty, kθ))
        let private __YieldFrom _Bind _Yield f = _Bind (f, _Yield)

        module StateMonad =

           type [< NoEquality; NoComparison >] state = { θ : tksubst }

           type mgu_builder () =
                inherit Monad.state_builder<state> ()
                member __.Zero () = fun s -> s.θ, s
                member __.Yield (θ : tksubst) = fun s -> let θ = compose_tksubst θ s.θ in θ, { θ = θ }
                member this.YieldFrom f = __YieldFrom this.Bind (fun (θ : tksubst) -> this.Yield θ) f
                member this.Yield x = __tYield this.Yield x
                member this.Yield x = __kYield this.Yield x
                member __.get = fun s -> s.θ, s
       
           let mgu (ctx : mgu_context) t1_ t2_ =
                let loc = ctx.loc
                let U = new mgu_builder ()
                let S = subst_ty
                let rec R t1 t2 =
                    U {                    
                        let! θ = U.get
                        let S = S θ
                        match t1, t2 with
                        | T_Cons (x, k1), T_Cons (y, k2) when x = y ->
                            yield kmgu ctx k1 k2

                        | T_Var (α, k1), T_Var (β, k2) when α = β ->
                            yield kmgu ctx k1 k2
                                      
                        | T_Row _ as s, T_Row_Ext (l, t, (T_Row (_, ρo) as r)) ->
                            let t', s', tθ1 = rewrite_row loc t1 t2 s l
                            match ρo with
                            | None -> ()
                            | Some ρ ->                            
                                if Set.contains ρ tθ1.dom then Report.Error.row_tail_circularity loc ρ tθ1
                                yield! R t t'
                                yield! R r s'

                        | T_Var (α, k) as tα, (T_NamedVar _ as t)
                        | (T_NamedVar _ as t), (T_Var (α, k) as tα)
                        | (T_Var (α, k) as tα), t
                        | t, (T_Var (α, k) as tα) ->
                            yield kmgu ctx k t.kind
                            if Set.contains α t.fv then Report.Error.circularity loc (S t1) (S t2) (S tα) (S t)
                            yield new tsubst (α, t) |> check_circularity

                        | T_App (t1, t2), T_App (t1', t2') ->
                            yield! R t1 t1'
                            yield! R t2 t2'
                                                           
                        | t1, t2 ->
                            return Report.Error.type_mismatch loc (S t1_) (S t2_) (S t1) (S t2)
                    }
                in
                    R t1_ t2_ { θ = tsubst.empty, ksubst.empty } |> fst
        

        module Functional =

            type mgu_builder () =
                inherit Computation.Builder.collection<tksubst> ((tsubst.empty, ksubst.empty), fun θ1 θ2 -> compose_tksubst θ2 θ1)
                member this.YieldFrom (tθ : tsubst) = this.YieldFrom ((tθ, ksubst.empty))
                member this.YieldFrom (kθ : ksubst) = this.YieldFrom ((tsubst.empty, kθ))

            let mgu (ctx : mgu_context) t1_ t2_ =
                let loc = ctx.loc
                let U = new mgu_builder ()
                let S = subst_ty
                let rec R t1 t2 =
                    U {                    
                        let! θ = U.get
                        let S = S θ
                        match t1, t2 with
                        | T_Cons (x, k1), T_Cons (y, k2) when x = y ->
                            yield! kmgu ctx k1 k2

                        | T_Var (α, k1), T_Var (β, k2) when α = β ->
                            yield! kmgu ctx k1 k2
                                      
                        | T_Row _ as s, T_Row_Ext (l, t, (T_Row (_, ρo) as r)) ->
                            let t', s', tθ1 = rewrite_row loc t1 t2 s l
                            match ρo with
                            | None -> ()
                            | Some ρ ->
                                if Set.contains ρ tθ1.dom then Report.Error.row_tail_circularity loc ρ tθ1
                                yield! R t t'
                                yield! R r s'

                        | T_Var (α, k) as tα, (T_NamedVar _ as t)
                        | (T_NamedVar _ as t), (T_Var (α, k) as tα)
                        | (T_Var (α, k) as tα), t
                        | t, (T_Var (α, k) as tα) ->
                            yield! kmgu ctx k t.kind
                            if Set.contains α t.fv then Report.Error.circularity loc (S t1) (S t2) (S tα) (S t)
                            yield! new tsubst (α, t) |> check_circularity

                        | T_App (t1, t2), T_App (t1', t2') ->
                            yield! R t1 t1'
                            yield! R t2 t2'
                                                           
                        | t1, t2 ->
                            Report.Error.type_mismatch loc (S t1_) (S t2_) (S t1) (S t2)
                    }
                in
                    R t1_ t2_


    let private multi_comparison equals fs x =
        let ret = function
            | Choice1Of2 r  -> r
            | Choice2Of2 ex -> raise ex
        let rs = [ for name, f in fs do yield name, (try Choice1Of2 (f x) with ex -> Choice2Of2 ex) ]
        let rs' = List.fold (fun z (_, r) ->        
                        let occurs name = z |> List.map snd |> List.concat |> Seq.exists ((=) name)
                        in
                            match [ for name', r' in rs do if not (occurs name') && equals r r' then yield name' ] with
                            | [] -> z
                            | names ->  (r, names) :: z)
                    [] rs
        match rs' with
        | [] -> unexpected "empty function list" __SOURCE_FILE__ __LINE__
        | [r, _] -> ret r
        | _ ->
            let r1, names1 = List.maxBy (fun (_, names) -> List.length names) rs'
            L.debug High "functions behaved differently: picking most common result: %s. Results are:\n%s" names1.[0]
                (mappen_strings (fun (r, names) ->
                        sprintf "%s:\n\t%s\n"
                            (flatten_strings ", " names)
                            (match r with Choice1Of2 (Q, (tθ, kθ)) -> sprintf "Q = %s\n\ttsubst = %O\n\tksubst = %O" (pretty_prefix Q) tθ kθ | Choice2Of2 ex -> pretty_exn_and_inners ex))
                    "\n" rs')
            #if DEBUG_MGU
            System.Diagnostics.Debugger.Break ()
            #endif
            ret r1


    // TODO: debug multiple mgus and remove this crap
    let multi =
        [ "pure", Pure.mgu
//          "func", Computational.Functional.mgu
//          "monad", Computational.StateMonad.mgu
          ]
        |> List.map (fun (a, b) -> a, uncurry4 b)
        |> multi_comparison
                (fun r1 r2 ->
                    match r1, r2 with
                    | Choice1Of2 (Q1, (tθ1, kθ1)), Choice1Of2 (Q2, (tθ2, kθ2)) -> let p x = sprintf "%O" x in p Q1 = p Q2 && p tθ1 = p tθ2 && p kθ1 = p kθ2
                    | Choice2Of2 ex1, Choice2Of2 ex2                           -> let p = pretty_exn_and_inners in p ex1 = p ex2
                    | _ -> false)
        |> curry4

let mgu = Mgu.Pure.mgu

let try_mgu ctx Q t1 t2 =
    try Some (mgu ctx Q t1 t2)
    with :? Report.type_error -> None
    
type basic_builder with
    member M.unify loc t1 t2 =
        M {
            let! { tθ = tθ; kθ = kθ; γ = γ } = M.get_state
            let θ = tθ, kθ
            let Q = M.get_Q
            let Q, (tθ, kθ as θ) = mgu { loc = loc; γ = γ } Q (subst_ty θ t1) (subst_ty θ t2)
            L.mgu "[U] %O == %O\n    [%O] --- [%O]" t1 t2 tθ kθ
            do! M.set_Q Q
            do! M.update_subst θ
        }

let try_principal_type_of ctx pt t =
    try_mgu ctx [] pt t |> Option.bind (function _, θ -> let t1 = subst_ty θ pt in if t1 = t then Some θ else None)

let is_principal_type_of ctx pt t = (try_principal_type_of ctx pt t).IsSome

let is_instance_of ctx pt t =
    let _, θ = mgu ctx [] pt t
    let t = subst_ty θ t
    in
        is_principal_type_of ctx pt t   // TODO: unification is not enough: unifier must be SMALLER - that would tell whether it is actually an instance



