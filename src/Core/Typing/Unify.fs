(*
 * Lw
 * Typing/Unify.fs: unification algorithms
 * (C) 2000-2014 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Unify

open FSharp.Common.Prelude
open FSharp.Common.Log
open FSharp.Common.Computation
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
        B.set { for α, t : ty in Q do if Set.contains α αs then yield! t.fv }

// match System-F quantifiers
let (|T_Foralls_F|_|) = function
    | T_Foralls (Q, t) when List.forall (function _, T_Bottom _ -> true | _ -> false) Q -> Some (List.map fst Q, t)
    | _ -> None


[< RequireQualifiedAccess >]
module internal Mgu =

    module Pure =
        type var with
            member α.skolemized k = T_Cons (sprintf Config.Typing.skolemized_tyvar_fmt α.pretty, k)

        let skolemized = function
            | T_ForallsK ([], t) -> [], t
            | T_ForallsK (Qk, t) ->
                let tsks = [ for α, _, k in Qk do yield α, α.skolemized k ]
                let θ = new tsubst (Env.t.ofSeq tsks), ksubst.empty
                in
                    List.map (function T_Cons (x, _) -> x | t -> unexpected "non-constructor in skolemized types: %O" __SOURCE_FILE__ __LINE__ t), subst_ty θ t

        type ty with
            member this.cons =
                let rec R t =
                  B.set {
                    match t with
                    | T_Bottom _      
                    | T_Closure _
                    | T_Var _                   -> ()
                    | T_Cons (x, _)             -> yield x
                    | T_HTuple ts               -> for t in ts do yield! R t
                    | T_App (t1, t2)     
                    | T_Forall ((_, t1), t2)    -> yield! R t1; yield! R t2 }
                in
                    R this

        type prefix with
            member this.cons = B.set { for _, t in this do yield! t.cons }

        let cons_in_tsubst (tθ : tsubst) = B.set { for _, t : ty in tθ do yield! t.cons }
        let cons_in_tksubst (tθ, _) = cons_in_tsubst tθ

        let check_skolem_escape ctx c θ (Q : prefix) =
            let cons = cons_in_tksubst θ + Q.cons
            in
                if Set.contains c cons then Report.Error.skolemized_type_variable_escaped ctx.loc c


        let rec subsume ctx (Q : prefix) (t1 : ty) (t2 : ty) =
            assert (t1.is_nf && t2.is_nf)
            match t1, t2 with
            | T_Foralls_F (αs, t1), T_ForallsQ (Q2, t2) ->
                assert (Q.dom <> Q2.dom)
                let tsks, t1' = skolemized t1
                let Q1, (tθ1, _ as θ1 : tksubst) = mgu ctx (Q.append Q2) t1' t2
                let Q2, Q3 = Q1.split Q.dom
                let θ2 = tθ1.remove Q3.dom
                // for each skolemized variable check it does not escape
                for tsk in tsks do
                    check_skolem_escape tsk ctx θ2 Q2
                    // either via the substitution
                    let b1 = (θ2.search_by (fun _  t -> t = tsk)).IsSome
                    // or via the prefix
                    let b2 = List.exists (function _, t -> t = tsk) Q2
                    if b1 || b2 then Report.Error.skolemized_type_variable_escaped ctx.loc tsk
                Q2, (θ2, ksubst.empty)

            | _ -> Q, (tsubst.empty, ksubst.empty)


        and mgu_scheme ctx (Q : prefix) (t1_ : ty)  (t2_ : ty) =
            assert (t1_.is_nf && t2_.is_nf)
            match t1_, t2_ with
            | (T_Bottom _, (_ as t))
            | (_ as t, T_Bottom _) -> Q, (tsubst.empty, ksubst.empty), t

            | T_ForallsQ (Q1, t1), T_ForallsQ (Q2, t2) ->
                assert (let p a b = Set.intersect a b = Set.empty
                        let d = Q.dom
                        let d1 = Q1.dom
                        let d2 = Q2.dom
                        in
                            p d d1 && p d1 d2 && p d d2)
                let Q3, θ3 = mgu ctx (Q.append(Q1).append(Q2)) t1 t2
                let Q4, Q5 = Q3.split Q.dom
                in
                    Q4, θ3, T_ForallsQ (Q5, subst_ty θ3 t1)


        and mgu (ctx : mgu_context) Q t1_ t2_ : prefix * tksubst =
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

                | T_ForallK ((α1, T_Bottom _, k1), t1), T_ForallK ((α2, T_Bottom _, k2), t2) ->
                    let c1 = α1.skolemized k1
                    let c2 = α2.skolemized k2
                    let Q1, θ1 =
                        let θ1 = new tsubst (α1, c1), ksubst.empty
                        let θ2 = new tsubst (α2, c2), ksubst.empty
                        in
                            R Q0 (S θ1 t1) (S θ2 t2)
                    check_skolem_escape c1 θ1 Q1
                    check_skolem_escape c2 θ1 Q1
                    Q1, θ1

                | T_Var (α1, k1), T_NamedVar (α2, k2) // prefer named tyvars over anonymous tyvars when unifying tyvar against tyvar
                | T_NamedVar (α2, k2), T_Var (α1, k1)
                | T_Var (α1, k1), T_Var (α2, k2) ->
                    let αt1 = List.find (fst >> (=) α1) Q0 |> snd
                    let αt2 = List.find (fst >> (=) α2) Q0 |> snd
                    // occurs check between one var into the other type bound
                    let check α t = if Set.contains α (dom_wrt Q0 t) then Report.Error.circularity loc t1 t2 (T_Var (α, t)) t2
                    check α1 t2
                    check α2 t1
                    let Q1, θ1, t = mgu_scheme ctx Q αt1 αt2
                    let Q2, θ2 = update_prefix_with_subst Q1 (α1, t2)
                    let Q3, θ3 = update_prefix_with_bound Q2 (α2, t)
                    in
                        Q3, θ3 ** θ2 ** θ1

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
                    let Q2, θ2 = update_prefix_with_subst Q1 (α, S θ1 t)
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


let mgu = Mgu.Pure.mgu

let try_mgu ctx Q t1 t2 =
    try Some (mgu ctx Q t1 t2)
    with :? Report.type_error -> None
    
type basic_builder with
    member M.unify loc t1 t2 =
        M {
            let! { tθ = tθ; kθ = kθ; γ = γ } = M.get_state
            let θ = tθ, kθ
            let! Q = M.get_Q
            let Q, (tθ, kθ as θ) = mgu { loc = loc; γ = γ } Q (subst_ty θ t1) (subst_ty θ t2)
            L.mgu "[U] %O == %O\n    [%O] --- [%O]\n    Q = %O" t1 t2 tθ kθ Q
            do! M.set_Q Q
            do! M.update_subst θ
        }

    member M.attempt_unify loc t1 t2 =
        M {
            let! st = M.get_state
            try do! M.unify loc t1 t2
            with :? Report.type_error -> do! M.set_state st          
        }

let try_principal_type_of ctx pt t =
    try_mgu ctx [] pt t |> Option.bind (function _, θ -> let t1 = subst_ty θ pt in if t1 = t then Some θ else None)

let is_principal_type_of ctx pt t = (try_principal_type_of ctx pt t).IsSome

let is_instance_of ctx pt t =
    let _, θ = mgu ctx [] pt t
    let t = subst_ty θ t
    in
        is_principal_type_of ctx pt t   // TODO: unification is not enough: unifier must be SMALLER - that would tell whether it is actually an instance



