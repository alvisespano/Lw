(*
 * Lw
 * Typing/Unify.fs: unification algorithms
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Unify


open FSharp.Common.Log
open FSharp.Common
open Lw.Core.Absyn
open Lw.Core.Globals
open Lw.Core.Typing.Defs
open Lw.Core.Typing.StateMonad
open Lw.Core.Typing.Meta
open Lw.Core.Typing.Ops
open Lw.Core
open System.Diagnostics


// unification
//

exception Mismatch of ty * ty

let rec rewrite_row loc t1 t2 r0 l =
    let R = rewrite_row loc t1 t2
    L.uni Normal "[I] %O ~= %s" r0 l
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

        let skolemize_ty αks t =
            let sks = [ for α : var, k in αks do yield α, α.skolemized, k ]
            let θ = !> (new tsubst (Env.t.ofSeq <| List.map (fun (α, x, k) -> α, T_Cons (x, k)) sks))
            in
                Computation.B.set { for _, x, _ in sks do yield x }, S θ t

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
        
        type fxty with
            member this.cons =
                let rec R ϕ =
                    Computation.B.set {
                        match ϕ with
                        | Fx_Bottom _       -> ()
                        | Fx_F_Ty t         -> yield! t.cons
                        | Fx_Forall (_, ϕ)  -> yield! R ϕ
                    }
                in
                    R this

        type prefix with
            member this.cons = Computation.B.set { for _, t in this do yield! t.cons }

        let cons_in_tsubst (tθ : tsubst) = Computation.B.set { for _, t : ty in tθ do yield! t.cons }
        let cons_in_tksubst θ = cons_in_tsubst θ.t

        let check_skolem_escape ctx c (Q : prefix, θ) =
            let cons = cons_in_tksubst θ + Q.cons
            in
                if Set.contains c cons then
//                    #if DEBUG_HML
//                    L.warn Low ""
                    Report.Error.skolemized_type_variable_escaped ctx.loc c

        let inline check_skolems_escape ctx cs (Q, θ) =
            for c in cs do
                check_skolem_escape ctx c (Q, θ)

        let check_circularity_wrt α Q ϕ =
            match Q with
            | Q_Slice α (_, _, Q2) -> Set.contains α (Fx_ForallsQ (Q2, ϕ)).fv
            | _                    -> false
 
        let rec subsume ctx (Q0 : prefix) (t : ty) (ϕ : fxty) =
          #if ENFORCE_NF_IN_UNI
          let t = t.nf
          let ϕ = ϕ.nf
          #endif
          #if DEBUG_UNI && DEBUG_HML
          L.uni High "[sub] %O :> %O\n      Q = %O\n" t ϕ Q0
          let Q, θ as r =
          #endif
            assert t.is_nf
            assert ϕ.is_nf
            match t, ϕ with            
            | _, FxU0_Bottom k ->          // this case is not in the HML paper but it is necessary
                Q0, kmgu ctx t.kind k                    

            | T_ForallsK0 (αks, t1), FxU0_ForallsQ (Mapped fxty.instantiate_unquantified (Q', t2)) ->
                assert Q0.is_disjoint Q'
                let skcs, t1' = skolemize_ty αks t1
                let Q1, θ1 = mgu_F ctx (Q0 + Q') t1' t2
                let Q2, Q3 = Q1.split Q0.dom
                #if DISABLE_HML_FIXES
                let θ2 = { θ1 with t = θ1.t.remove Q3.dom } 
                let r = Q2, θ2
                #else
                let r = Q1, { θ1 with t = θ1.t.remove (Q3.dom + Q'.dom) }   // HACK: Q'.dom contains variables created by the intantiation, and therefore must be removed
                #endif
                check_skolems_escape ctx skcs r     // HACK: HML paper is ambiguous here cause it binds Q2 twice: I believe it should check what's returned as result
                r
          #if DEBUG_UNI && DEBUG_HML
          L.uni High "[sub=] %O :> %O\n       %O\n       Q' = %O" t ϕ θ Q
          r
          #endif


        and mgu_fx ctx (Q : prefix) (ϕ1 : fxty) (ϕ2 : fxty) =
          #if ENFORCE_NF_IN_UNI
          let ϕ1 = ϕ1.nf
          let ϕ2 = ϕ2.nf
          #endif
          #if DEBUG_UNI && DEBUG_HML
          L.uni Normal "[mgu-scheme] %O == %O\n             Q = %O" ϕ1 ϕ2 Q
          let Q', θ, ϕ as r =
          #endif
            assert ϕ1.is_nf
            assert ϕ2.is_nf
            match ϕ1, ϕ2 with
            | (FxU0_Bottom k, (_ as ϕ))
            | (_ as ϕ, FxU0_Bottom k) -> Q, kmgu ctx k ϕ.kind, ϕ

            | FxU0_ForallsQ  (Mapped fxty.instantiate_unquantified (Q1, t1)), FxU0_ForallsQ (Mapped fxty.instantiate_unquantified (Q2, t2)) ->
                assert (let p (a : prefix) b = a.is_disjoint b in p Q Q1 && p Q1 Q2 && p Q Q2)  // instantiating ϕ1 and ϕ2 makes this assert always false
                let Q3, θ3 = mgu_F ctx (Q + Q1 + Q2) t1 t2
                let Q4, Q5 = Q3.split (Q.dom + (fv_Γ (subst_jenv θ3 ctx.Γ)))    // HACK: abstract this code by using get_ungeneralizable_vars
                in
                    Q4, θ3, FxU_ForallsQ (Q5, S θ3 t1)
          #if DEBUG_UNI && DEBUG_HML
          L.uni Normal "[mgu-scheme=] %O == %O\n              %O\n              Q' = %O\n              res = %O" ϕ1 ϕ2 θ Q' ϕ
          r
          #endif


        // TODOL: rewrite the whole unification with monads?
        and mgu_F (ctx : uni_context) Q0 t1_ t2_ : prefix * tksubst =
            let loc = ctx.loc
            let rec R (Q0 : prefix) (t1 : ty) (t2 : ty) =
              #if DEBUG_UNI && DEBUG_UNI_DEEP
              L.uni Low "[mgu] %O == %O\n      Q = %O" t1 t2 Q0
              let Q, θ as r =
              #endif
                #if ENFORCE_NF_IN_UNI
                let t1 = t1.nf
                let t2 = t2.nf
                assert t1.is_nf
                assert t2.is_nf
                #endif
                match t1, t2 with
                | T_Cons (x, k1), T_Cons (y, k2) when x = y -> Q0, kmgu ctx k1 k2
                | T_Var (α, k1), T_Var (β, k2) when α = β   -> Q0, kmgu ctx k1 k2
                                      
                | (T_Row _ as s), T_Row_Ext (l, t, (T_Row (_, ρo) as r)) ->
                    let t', s', tθ1 = rewrite_row loc t1 t2 s l
                    let θ1 = !> tθ1
                    Option.iter (fun ρ -> if Set.contains ρ tθ1.dom then Report.Error.row_tail_circularity loc ρ tθ1) ρo
                    let Q2, θ2 = R Q0 (S θ1 t) (S θ1 t')
                    let Q3, θ3 = let θ = θ2 ** θ1 in R Q2 (S θ r) (S θ s')
                    in
                        Q3, θ3 ** θ2 ** θ1

                | T_ForallK ((α, k1), t1), T_ForallK ((β, k2), t2) ->
                    let skcs1, t1 = skolemize_ty [α, k1] t1
                    let skcs2, t2 = skolemize_ty [β, k2] t2
                    let Q1, θ1 = R Q0 t1 t2
                    check_skolems_escape ctx (skcs1 + skcs2) (Q1, θ1)
                    Q1, θ1

                | T_Var (α1, k1), T_NamedVar (α2, k2) // prefer propagating named over anonymous vars in substitutions
                | T_NamedVar (α2, k2), T_Var (α1, k1)
                | T_Var (α1, k1), T_Var (α2, k2) ->
                    let θ0 = kmgu ctx k1 k2
                    let ϕ1 = Q0.lookup α1
                    let ϕ2 = Q0.lookup α2
                    // occurs check between one tyvar into the other's type bound and the other way round
                    let check_wrt α t = if check_circularity_wrt α Q0 t then let S = S θ0 in Report.Error.circularity loc (S t1_) (S t2_) (T_Var (α, t.kind)) (S t2_)
                    check_wrt α1 ϕ2
                    check_wrt α2 ϕ1
                    let Q1, θ1, ϕ = let S = subst_fxty in mgu_fx ctx Q0 (S θ0 ϕ1) (S θ0 ϕ2)  // TODO: this θ0 subst should be applied also on the 2 types involved in the 2 updates below?
                    let Q2, θ2 = Q1.update_with_subst (α1, T_Var (α2, k2))   // do not use t2 here! it would always refer to right-hand type of the pattern, and in case of reversed named var it would refer to α1!
                    let Q3, θ3 = Q2.update_with_bound (α2, ϕ)
                    in
                        Q3, θ3 ** θ2 ** θ1 ** θ0

                | T_Var (α, k), t
                | t, T_Var (α, k) ->
                    let ϕ = Q0.lookup α
                    let θ0 = kmgu ctx k t.kind
                    // occurs check
                    if check_circularity_wrt α Q0 (Fx_F_Ty t) then let S = S θ0 in Report.Error.circularity loc (S t1_) (S t2_) (S (T_Var (α, k))) (S t)
                    let Q1, θ1 = subsume ctx Q0 (S θ0 t) (subst_fxty θ0 ϕ)
                    let Q2, θ2 = let S = S <| θ1 ** θ0 in Q1.update_with_subst (α, S t)
                    in
                        Q2, θ2 ** θ1 ** θ0

                | T_App (t1, t2), T_App (t1', t2') ->
//                    let θ0 = kmgu ctx (K_Arrow (t2.kind, kind.fresh_var)) t1.kind ** kmgu ctx (K_Arrow (t2'.kind, kind.fresh_var)) t1'.kind   // TODOH: is this line needed?
                    let Q1, θ1 = R Q0 t1 t1'
                    let Q2, θ2 = let S = S θ1 in R Q1 (S t2) (S t2')
                    in
                        Q2, θ2 ** θ1

                | t1, t2 -> raise (Mismatch (t1, t2))
              #if DEBUG_UNI && DEBUG_UNI_DEEP
              L.uni Low "[mgu=] %O == %O\n       %O\n       Q' = %O" t1 t2 θ Q
              r
              #endif
            in
                try
                    #if DEBUG_UNI && !DEBUG_UNI_DEEP
                    L.uni Low "[mgu] %O == %O\n      Q = %O" t1_ t2_ Q0
                    #endif
                    let Q, θ as r = R Q0 t1_ t2_
                    assert (Set.intersect Q.dom θ.dom).IsEmpty
                    #if DEBUG_UNI && !DEBUG_UNI_DEEP
                    L.uni Low "[mgu=] %O == %O\n       %O\n       Q' = %O" t1_ t2_ θ Q
                    #endif                    
                    r
                with Mismatch (t1, t2) -> Report.Error.type_mismatch loc t1_ t2_ t1 t2

       
let mgu = Mgu.Pure.mgu_F
let subsume = Mgu.Pure.subsume
let mgu_fx = Mgu.Pure.mgu_fx

let try_mgu ctx Q t1 t2 =
    try Some (mgu ctx Q t1 t2)
    with :? Report.type_error -> None
    
type type_inference_builder with
    member M.unify_F loc (t1 : ty) (t2 : ty) =
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
            try do! M.unify_F loc t1 t2
            with :? Report.type_error -> do! M.set_state st          
        }

type ty with
    member t1.try_instance_of ctx (t2 : ty) =
        let Q = prefix.B { for α, k in Seq.append t1.kinded_ftv t2.kinded_ftv do yield α, Fx_Bottom k }
        let _, θ = mgu ctx Q t1 t2
        in
            if t2.fv.IsSubsetOf θ.dom then Some θ   // TODO: in https://web.cecs.pdx.edu/~mpj/thih/TypingHaskellInHaskell.html they define a "match" function similar to one-way-only MGU, useful here!
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
