(*
 * Lw
 * Typing/Unify.fs: unification algorithms
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Unify

open FSharp.Common.Log
open FSharp.Common
open Lw.Core.Absyn
open Lw.Core.Absyn.Misc
open Lw.Core.Absyn.Var
open Lw.Core.Absyn.Kind
open Lw.Core.Absyn.Sugar
open Lw.Core.Absyn.Ast
open Lw.Core.Globals
open Lw.Core.Typing.Defs
open Lw.Core.Typing.StateMonad
open Lw.Core.Typing.Meta
open Lw.Core.Typing.Ops
open Lw.Core
open Lw.Core.Typing.Subst
open System.Diagnostics


// unification
//

//exception Mismatch of ty * ty

let rec rewrite_row loc t1 t2 r0 l =
    let R = rewrite_row loc t1 t2
    #if DEBUG_UNI
    L.uni Low "[I] %O ~= %s" r0 l
    #endif
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
                

[< RequireQualifiedAccess >]
module internal Mgu =

    module Pure =
        let S = subst_ty
        let ( ** ) = compose_tksubst
        let kmgu ctx k1 k2 : tksubst = !> (kmgu ctx k1 k2)

        type var with
            member α.skolemized = sprintf Config.Printing.skolemized_tyvar_fmt α.pretty

        type ty with
            member this.cons =
                let rec R t =
                  Computation.B.set {
                    match t with
                    | T_Closure _
                    | T_Var _                   -> ()
                    | T_Cons (x, _)             -> yield x
                    | T_HTuple ts               -> for t in ts do yield! R t
                    | T_App (t1, t2)            -> yield! R t1; yield! R t2
                    | T_Forall (_, t)           -> yield! R t }
                in
                    R this
       
        type prefix with
            member this.cons = Computation.B.set { for _, t in this do yield! t.cons }

        let cons_in_tsubst (tθ : tsubst) = Computation.B.set { for _, t : ty in tθ do yield! t.cons }
        let cons_in_tksubst θ = cons_in_tsubst θ.t
            

        and mgu (ctx : uni_context) t1_ t2_ : tksubst =
            let loc = ctx.loc
            let rec R (t1 : ty) (t2 : ty) =
                #if DEBUG_UNI && DEBUG_UNI_DEEP
                L.uni Low "[mgu] %O == %O" t1 t2
                #endif
                let Q, θ as r =
                    match t1, t2 with
                    | T_Cons (x, k1), T_Cons (y, k2) when x = y -> kmgu ctx k1 k2
                    | T_Var (α, k1), T_Var (β, k2) when α = β   -> kmgu ctx k1 k2
                                      
                    | (T_Row _ as s), T_Row_Ext (l, t, (T_Row (_, ρo) as r)) ->
                        let t', s', tθ1 = rewrite_row loc t1 t2 s l
                        let θ1 = !> tθ1
                        Option.iter (fun ρ -> if Set.contains ρ tθ1.dom then Report.Error.row_tail_circularity loc ρ tθ1) ρo
                        let Q2, θ2 = R Q0 (S θ1 t) (S θ1 t')
                        let Q3, θ3 = let θ = θ2 ** θ1 in R Q2 (S θ r) (S θ s')
                        in
                            Q3, θ3 ** θ2 ** θ1

                    | T_Var (α1, k1), T_NamedVar (α2, k2) // prefer propagating named over anonymous vars in substitutions
                    | T_NamedVar (α2, k2), T_Var (α1, k1)
                    | T_Var (α1, k1), T_Var (α2, k2) ->
                        let θ0 = kmgu ctx k1 k2
                        let ϕ1 = Q0.lookup α1
                        let ϕ2 = Q0.lookup α2
                        // occurs check between one tyvar into the other's type bound and the other way round
                        let check_wrt α t = if check_circularity_wrt α Q0 t then let S = S θ0 in Report.Error.type_circularity loc (S t1_) (S t2_) (T_Var (α, t.kind)) (S t2_)
                        check_wrt α1 ϕ2
                        check_wrt α2 ϕ1
                        let Q1, θ1, ϕ = let S = subst_fxty θ0 in mgu_fx ctx Q0 (S ϕ1) (S ϕ2)
                        let Q2, θ2 = Q1.update_with_subst (α1, T_Var (α2, k2))   // do not use t2 here! it would always refer to right-hand type of the pattern, and in case of reversed named var it would refer to α1!
                        let Q3, θ3 = Q2.update_with_bound (α2, ϕ)
                        in
                            Q3, θ3 ** θ2 ** θ1 ** θ0

                    | T_Var (α, k), t
                    | t, T_Var (α, k) ->
                        let θ0 = kmgu ctx k t.kind
                        // occurs check
                        if check_circularity_wrt α Q0 (Fx_F_Ty t) then let S = S θ0 in Report.Error.type_circularity loc (S t1_) (S t2_) (S (T_Var (α, k))) (S t)
                        let Q1, θ1 = subsume ctx Q0 (S θ0 t) (subst_fxty θ0 ϕ)
                        let Q2, θ2 = let S = S (θ1 ** θ0) in Q1.update_with_subst (α, S t)
                        in
                            Q2, θ2 ** θ1 ** θ0

                    | T_App (t1, t2), T_App (t1', t2') ->
                        let θ0 = kmgu ctx (K_Arrow (t2.kind, kind.fresh_var)) t1.kind ** kmgu ctx (K_Arrow (t2'.kind, kind.fresh_var)) t1'.kind
                        let Q1, θ1 = let S = S θ0 in R Q0 (S t1) (S t1')
                        let Q2, θ2 = let S = S (θ1 ** θ0) in R Q1 (S t2) (S t2')
                        in
                            Q2, θ2 ** θ1 ** θ0

                    | t1, t2 -> Report.Error.unification_mismatch loc t1_ t2_ t1 t2
                #if DEBUG_UNI && DEBUG_UNI_DEEP
                L.uni Low "[mgu=] %O == %O\n       %O\n       Q = %O" t1 t2 θ Q
                #endif
                r
            #if DEBUG_UNI && !DEBUG_UNI_DEEP
            L.uni Low "[mgu] %O == %O\n      Q0 = %O" t1_ t2_ Q0_
            #endif
            let Q, θ as r = R Q0_ t1_ t2_
            assert (Set.intersect Q.dom θ.dom).IsEmpty;
            #if DEBUG_UNI && !DEBUG_UNI_DEEP
            L.uni Low "[mgu=] %O == %O\n       %O\n       Q' = %O" t1_ t2_ θ Q
            #endif                    
            r

module U = Mgu.Pure

let try_mgu ctx Q t1 t2 =
    try Some (U.mgu ctx Q t1 t2)
    with :? Report.type_error -> None
    
type type_inference_builder with
    member M.unify loc (t1 : ty) (t2 : ty) =
        M {
            let! Q = M.get_Q
            let! t1 = M.updated t1
            let! t2 = M.updated t2
            let! uctx = M.get_uni_context loc
            let Q, θ = mgu uctx Q t1 t2
            do! M.set_Q Q
            do! M.update_θ θ
        }

    member M.subsume loc (t : ty) (ϕ : fxty) =
        M {
            let! Q = M.get_Q
            let! t = M.updated t
            let! ϕ = M.updated ϕ
            let! uctx = M.get_uni_context loc
            let Q, θ = subsume uctx Q t ϕ
            do! M.set_Q Q
            do! M.update_θ θ
        }

    member M.unify_fx loc (ϕ1 : fxty) (ϕ2 : fxty) =
        M {
            let! Q = M.get_Q
            let! ϕ1 = M.updated ϕ1
            let! ϕ2 = M.updated ϕ2
            let! uctx = M.get_uni_context loc
            let Q, θ, ϕ = mgu_fx uctx Q ϕ1 ϕ2
            do! M.set_Q Q
            do! M.update_θ θ
            return ϕ
        }

    member M.attempt_unify loc t1 t2 =
        M {
            let! st = M.get_state
            try do! M.unify loc t1 t2
            with :? Report.type_error -> do! M.set_state st          
        }

type ty with
    member t1.try_instance_of ctx (t2 : ty) =
        let Q = prefix.B { for α, k in Seq.append t1.ftv t2.ftv do yield α, Fx_Bottom k }
        let _, θ = mgu ctx Q t1 t2
        in
            if t2.fv.IsSubsetOf θ.dom then Some θ   // TODO: in https://web.cecs.pdx.edu/~mpj/thih/TypingHaskellInHaskell.html a "match" function similar to one-way-only MGU is defined - useful here!
            else None

    member t1.is_instance_of ctx t2 = (t1.try_instance_of ctx t2).IsSome

type fxty with
    member ϕ.is_instance_of ctx t = ϕ.ftype.is_instance_of ctx t    // TODO: needs testing


//let try_principal_type_of ctx pt t =
//    try_mgu ctx Q_Nil pt t |> Option.bind (function _, θ -> let t1 = subst_ty θ pt in if t1 = t then Some θ else None)
//
//let is_principal_type_of ctx pt t = (try_principal_type_of ctx pt t).IsSome
//
//let is_instance_of ctx (ϕ1 : fxty) (pt : ty) =
//    let ϕ2 = Fx_Foralls ([for α in pt.fv do yield α, Fx_Bottom (pt.search_var α).Value], Fx_F_Ty pt)
//    let _, θ = subsume ctx ϕ1 ϕ2    // CONTINUA: subsumere al contrario? potrebbe funzionare... cioè il pt della overload deve essere un'istanza del flextype inferito
//    let t = subst_ty θ t
//    in
//        is_principal_type_of ctx pt t   // TODO: use HML subsume for checking instances
//
//
