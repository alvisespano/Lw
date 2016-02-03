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
        let α = ty.fresh_star_var
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
        Computation.B.set { for α, t : ty in Q do if Set.contains α αs then yield! t.fv }


[< RequireQualifiedAccess >]
module internal Mgu =

    module Pure =
        let S = subst_ty
        let ( ** ) = compose_tksubst
        let kmgu ctx k1 k2 = tsubst.empty, kmgu ctx k1 k2

        type var with
            member α.skolemized = sprintf Config.Typing.skolemized_tyvar_fmt α.pretty

        let skolemize_ty αks t =
            let sks = [ for α : var, k in αks do yield α, α.skolemized, k ]
            let θ = new tsubst (Env.t.ofSeq <| List.map (fun (α, x, k) -> α, T_Cons (x, k)) sks), ksubst.empty
            in
                Computation.B.set { for _, x, _ in sks do yield x }, S θ t

        type ty with
            member this.cons =
                let rec R t =
                  Computation.B.set {
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
            member this.cons = Computation.B.set { for _, t in this do yield! t.cons }

        let cons_in_tsubst (tθ : tsubst) = Computation.B.set { for _, t : ty in tθ do yield! t.cons }
        let cons_in_tksubst (tθ, _) = cons_in_tsubst tθ

        let check_skolem_escape ctx c θ (Q : prefix) =
            let cons = cons_in_tksubst θ + Q.cons
            in
                if Set.contains c cons then Report.Error.skolemized_type_variable_escaped ctx.loc c

        let check_skolems_escape ctx cs θ Q =
            for c in cs do
                check_skolem_escape ctx c θ Q

        let rec mgu ctx Q t1_ t2_ =
            L.mgu "[mgu] %O == %O\n      Q = %O" t1_ t2_ Q
            let Q, (tθ, kθ) as r = mgu' ctx Q t1_ t2_
            L.mgu "[mgu] %O\n      %O\n      Q' = %O" tθ kθ Q
            r

        and subsume ctx Q t1_ t2_ =
            L.mgu "[sub] %O :> %O\n      Q = %O\n" t1_ t2_ Q
            let Q, (tθ, kθ) as r = subsume' ctx Q t1_ t2_
            L.mgu "[sub] %O\n      %O\n      Q' = %O" tθ kθ Q
            r

        and mgu_scheme ctx Q t1_ t2_ =
            L.mgu "[mgu-scheme] %O == %O\n             Q = %O" t1_ t2_ Q
            let Q, (tθ, kθ), t as r = mgu_scheme' ctx Q t1_ t2_
            L.mgu "[mgu-scheme] %O\n             %O\n             Q' = %O\n             t = %O" tθ kθ Q t
            r

        and subsume' ctx (Q : prefix) (t1_ : ty) (t2_ : ty) =
            let t1_ = t1_.ftype.nf
            let t2_ = t2_.nf //.constructed_form
            match t1_, t2_ with
            | _, T_Bottom k -> Q, kmgu ctx t1_.kind k   // this case comes from HML implementation - it is not in the paper

            | T_Foralls_F (αs, t1), T_ForallsQ (Q2, t2) ->            
                assert Q.is_disjoint Q2
                let skcs, t1' = skolemize_ty αs t1
                let Q1, (tθ1, kθ1) = mgu ctx (Q + Q2) t1' t2    // TODO: does this unify kinds automatically?
                let Q2, Q3 = Q1.split Q.dom
                let θ2 = tθ1.remove Q3.dom, kθ1
                check_skolems_escape ctx skcs θ2 Q2
                Q2, θ2

        and mgu_scheme' ctx (Q : prefix) (t1_ : ty)  (t2_ : ty) =
            assert t1_.is_nf
            assert t2_.is_nf
            match t1_, t2_ with
            | (T_Bottom k, (_ as t))
            | (_ as t, T_Bottom k) -> Q, kmgu ctx k t.kind, t

            | T_ForallsQ (Q1, t1), T_ForallsQ (Q2, t2) ->
                assert (let p (a : prefix) b = a.is_disjoint b in p Q Q1 && p Q1 Q2 && p Q Q2)
                let Q3, θ3 = mgu ctx (Q + Q1 + Q2) t1 t2
                let Q4, Q5 = Q3.split Q.dom
                in
                    Q4, θ3, T_ForallsQ (Q5, S θ3 t1)

        and mgu' (ctx : mgu_context) Q t1_ t2_ : prefix * tksubst =
            let loc = ctx.loc
            let rec R (Q0 : prefix) (t1 : ty) (t2 : ty) =
                let t1 = t1.nf
                let t2 = t2.nf
                assert t1.is_ftype
                assert t2.is_ftype
                match t1, t2 with
                | T_Cons (x, k1), T_Cons (y, k2) when x = y -> Q0, kmgu ctx k1 k2
                | T_Var (α, k1), T_Var (β, k2) when α = β   -> Q0, kmgu ctx k1 k2
                                      
                | (T_Row _ as s), T_Row_Ext (l, t, (T_Row (_, ρo) as r)) ->
                    let t', s', tθ1 = rewrite_row loc t1 t2 s l
                    let θ1 = tθ1, ksubst.empty
                    Option.iter (fun ρ -> if Set.contains ρ tθ1.dom then Report.Error.row_tail_circularity loc ρ tθ1) ρo
                    let Q2, θ2 = R Q0 (S θ1 t) (S θ1 t')
                    let Q3, θ3 = let θ = θ2 ** θ1 in R Q2 (S θ r) (S θ s')
                    in
                        Q3, θ3 ** θ2 ** θ1

//                | T_Forall_F ((α1, k1), t1), T_Forall_F ((α2, k2), t2) ->
                | T_Forall ((α1, tb1), t1), T_Forall ((α2, tb2), t2) ->
                    let k1 = tb1.kind
                    let k2 = tb2.kind
                    let θ0 = kmgu ctx k1 k2 ** kmgu ctx t1.kind t2.kind
                    let skcs1, t1 = skolemize_ty [α1, k1] (S θ0 t1)
                    let skcs2, t2 = skolemize_ty [α2, k2] (S θ0 t2)
                    let Q1, θ1 = let S = S θ0 in R Q0 (S t1) (S t2)
                    check_skolems_escape ctx (skcs1 + skcs2) θ1 Q1
                    Q1, θ1 ** θ0

//                | T_Var (α1, k1), T_NamedVar (α2, k2) // prefer named over anonymous when unifying var vs. var
//                | T_NamedVar (α2, k2), T_Var (α1, k1)
                | T_Var (α1, k1), T_Var (α2, k2) ->
                    let θ0 = kmgu ctx k1 k2
                    let α1t = Q0.lookup α1
                    let α2t = Q0.lookup α2
                    // occurs check between one tyvar into the other's type bound and the other way round
                    let check α t = if Set.contains α (dom_wrt Q0 t) then let S = S θ0 in Report.Error.circularity loc (S t1) (S t2) (T_Var (α, t.kind)) (S t2)
                    check α1 α2t
                    check α2 α1t
                    let Q1, θ1, t = mgu_scheme ctx Q α1t α2t
                    let Q2, θ2 = Q1.update_prefix_with_subst (α1, t2)
                    let Q3, θ3 = Q2.update_prefix_with_bound (α2, t)
                    in
                        Q3, θ3 ** θ2 ** θ1 ** θ0

                | T_Var (α, k), t
                | t, T_Var (α, k) ->
                    let αt = Q0.lookup α
                    let θ0 = kmgu ctx k t.kind
                    // occurs check
                    if Set.contains α (dom_wrt Q t) then let S = S θ0 in Report.Error.circularity loc (S t1_) (S t2_) (S (T_Var (α, k))) (S t)
                    let Q1, θ1 = subsume ctx Q (S θ0 t) (S θ0 αt)
                    let Q2, θ2 = let S = S <| θ1 ** θ0 in Q1.update_prefix_with_subst (α, S t)
                    in
                        Q2, θ2 ** θ1 ** θ0

                | T_App (t1, t2), T_App (t1', t2') ->
                    let θ0 = kmgu ctx (K_Arrow (t2.kind, kind.fresh_var)) t1.kind ** kmgu ctx (K_Arrow (t2'.kind, kind.fresh_var)) t1'.kind
                    let Q1, θ1 = let S = S θ0 in R Q0 (S t1) (S t1')
                    let Q2, θ2 = let S = S <| θ1 ** θ0 in R Q1 (S t2) (S t2')
                    in
                        Q2, θ2 ** θ1 ** θ0
                                                           
                | t1, t2 -> 
                    raise (Mismatch (t1, t2))

            try
                let Q, (tθ, _ as θ) = R Q t1_ t2_
                // check post-condition of HML unify function
                for _, t in tθ do
                    assert t.nf.is_ftype
                Q, θ
            with Mismatch (t1, t2) -> Report.Error.type_mismatch loc t1_ t2_ t1 t2

       

let mgu = Mgu.Pure.mgu

let try_mgu ctx Q t1 t2 =
    try Some (mgu ctx Q t1 t2)
    with :? Report.type_error -> None
    
type typing_builder with
    member M.unify loc t1 t2 =
        M {
            let! γ = M.get_γ
            let! Q = M.get_Q
            let! t1 = M.update_ty t1
            let! t2 = M.update_ty t2
            let Q, (tθ, kθ as θ) = mgu { loc = loc; γ = γ } Q t1 t2
            do! M.set_Q Q
            do! M.update_θ θ
        }

    member M.attempt_unify loc t1 t2 =
        M {
            let! st = M.get_state
            try do! M.unify loc t1 t2
            with :? Report.type_error -> do! M.set_state st          
        }

let try_principal_type_of ctx pt t =
    try_mgu ctx Q_Nil pt t |> Option.bind (function _, θ -> let t1 = subst_ty θ pt in if t1 = t then Some θ else None)

let is_principal_type_of ctx pt t = (try_principal_type_of ctx pt t).IsSome

let is_instance_of ctx pt t =
    let _, θ = mgu ctx Q_Nil pt t
    let t = subst_ty θ t
    in
        is_principal_type_of ctx pt t   // TODO: use HML subsume for checking instances



