(*
 * Lw
 * Typing/fs: equivalence algorithms for types and kinds
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Equivalence

open FSharp.Common.Log
open FSharp.Common
open Lw.Core
open Lw.Core.Absyn
open Lw.Core.Absyn.Misc
open Lw.Core.Absyn.Var
open Lw.Core.Absyn.Kind
open Lw.Core.Absyn.Ast
open Lw.Core.Globals
open Lw.Core.Typing
open Lw.Core.Typing.Defs
open Subst


// type equivalence
//

module Monadic =

    type state = Env.t<var, var>

    type M<'a> = Monad.M<'a, state>

    type builder<'t> (is_equivalent : 't -> 't -> M<bool>) =
        inherit Monad.state_builder<state> ()

        member M.is_var_equivalent (α : var) (β : var) =
            M {
                let! env = M.get_state
                match env.search α with
                | Some α' ->
                    #if DEBUG_TYPE_EQUIVALENCE
                    L.debug Unmaskerable "%O |-> %O = %O: %b" α α' β (α' = β)
                    #endif
                    return α' = β
                | None ->
                    let! env = M.get_state
                    if env.exists (fun _ β' -> β' = β) then
                        return false
                    else
                        do! M.lift_state <| fun env -> env.bind α β
                        #if DEBUG_TYPE_EQUIVALENCE
                        L.debug Unmaskerable "%O |-> %O" α β
                        #endif
                        return true
            }

        member M.undoable_remove_vars_mapped_by (αs : Set<var>) =
            M {
                let! env = M.get_state
                let bck = [ for α, β in env do if Set.contains α αs then yield α, β ]
                do! M.set_state (env.remove αs)
                return M { do! M.lift_state (fun env -> env.binds bck) }
            }

        member M.undoable_remove_vars_mapping_to (βs : Set<var>) =
            M {
                let! env = M.get_state
                let bck = [ for α, β in env do if Set.contains β βs then yield α, β ]
                do! M.set_state (env.remove (Seq.map fst bck))
                return M { do! M.lift_state (fun env -> env.binds bck) }
            }

        member M.binop_and_with_result on_false on_true x y =
            M {
                let! st = M.get_state
                let! a, r1 = x
                if a then
                    let! b, r2 = y r1
                    if b then
                        return! on_true r1 r2
                    else
                        do! M.set_state st
                        return! on_false
                else 
                    do! M.set_state st
                    return! on_false
            }
        
        member M.binop_and_with_undo x y =
            M {
                let! st = M.get_state
                let! a = x
                if a then
                    let! b = y
                    if b then return true
                    else
                        do! M.set_state st
                        return false
                else 
                    do! M.set_state st
                    return false
            }

    //    member M.binop_and_with_undo x y =
    //        M {
    //            let on_false = M { return false }
    //            let on_true _  _ = M { return true }
    //            let f x = M { let! r = x in return r, () }
    //            return! M.binop_and_with_result on_false on_true (f x) (fun () -> f y)
    //        }
            
        member M.are_equivalent l1 l2 =
            let (&&&) = M.binop_and_with_undo
            M {
                return! M.List.fold (fun b (t1, t2) -> M { return! M { return b } &&& is_equivalent t1 t2 }) true (List.zip l1 l2)
            }

    let rec is_kind_equivalent (x : kind) (y : kind) =
        let M = new builder<kind> (is_kind_equivalent)
        M {
            match x, y with
            | K_Var α, K_Var β ->
                    return! M.is_var_equivalent α β

            | K_Cons (x1, ks1), K_Cons (x2, ks2) when x1 = x2 && ks1.Length = ks2.Length ->
                return! M.are_equivalent ks1 ks2

            | _ ->
                return false
        }

    let rec private is_prefixed_unquantified_ty_equivalent (Q1 : prefix, t1 : ty) (Q2 : prefix, t2 : ty) =
        assert t1.is_unquantified
        assert t2.is_unquantified
        let M = new builder<fxty> (is_fxty_equivalent)
        let (&&&) = M.binop_and_with_undo
        M {
            let contains (α, αϕ) =
                let rec R q Q =
                    M {
                        match Q with
                        | Q_Nil ->
                            return false, q

                        | Q_Cons (q1, (β, βϕ)) ->
                            let! st = M.get_state
                            let! a = is_fxty_equivalent αϕ βϕ
                            let! b = M.is_var_equivalent α β
                            if a && b then
                                return true, q1 + q
                            else
                                do! M.set_state st
                                return! R (q.insert (β, βϕ)) q1
                        }
                in
                    fun Q ->
                        M {
                            let! r, q = R Q_Nil Q
                            #if DEBUG_TYPE_EQUIVALENCE
                            L.debug Unmaskerable "%O contained in %O: %b, %O" α Q2 r q
                            #endif
                            return r, q
                        }
            let rec is_permutation Q1 Q2 = M {
                match Q1 with
                | Q_Nil ->
                    return true

                | Q_Cons (q1, α) ->
                    let! a, q2 = contains α Q2
                    let! b = is_permutation q1 q2
                    #if DEBUG_TYPE_EQUIVALENCE
                    L.debug Unmaskerable "%O is permutation of %O: %b" Q1 Q2 (a && b)
                    #endif
                    return a && b
            }
            let! st = M.get_state
            let! undo1 = M.undoable_remove_vars_mapped_by Q1.dom
            let! undo2 = M.undoable_remove_vars_mapping_to Q2.dom
            let! r = is_ty_equivalent t1 t2 &&& is_permutation Q1 Q2
            if r then
                do! undo1
                do! undo2
                return true
            else
                do! M.set_state st
                return false
        }

    and private is_ty_equivalent' (x : ty) (y : ty) =
        let M = new builder<ty> (is_ty_equivalent)
        M {   
            match x, y with
            | T_Cons (x, _), T_Cons (y, _)          -> return x = y
            | T_Var (α, _), T_Var (β, _)            -> return! M.is_var_equivalent α β
            | T_App (t1, t2), T_App (t1', t2')      -> return! M.are_equivalent [t1; t2] [t1'; t2']

            | T_ForallsK (αs, t1), T_ForallsK (βs, t2) when αs.Length = βs.Length ->
                let Q1 = prefix.of_bottoms αs
                let Q2 = prefix.of_bottoms βs
                return! is_prefixed_unquantified_ty_equivalent (Q1, t1) (Q2, t2)

            | T_HTuple ts, T_HTuple ts' when ts.Length = ts'.Length ->
                return! M.are_equivalent ts ts'

            #if DEBUG
            | T_Closure _, _ | _, T_Closure _ ->
                L.unexpected_error "comparing type closures: %O = %O" x y
                return false
            #endif
            | _ ->
                return false
        }

    and private is_fxty_equivalent' (x : fxty) (y : fxty) =
        let M = new builder<fxty> (is_fxty_equivalent)
        M {   
            match x, y with
            | FxU_ForallsQ (Q1, t1), FxU_ForallsQ (Q2, t2) ->
                return! is_prefixed_unquantified_ty_equivalent (Q1, t1) (Q2, t2)

            | Fx_F_Ty t1, Fx_F_Ty t2 ->
                return! is_ty_equivalent t1 t2

            | Fx_Bottom _, Fx_Bottom _ ->
                return true

            | _ -> return false
        }

    and private is_kinded_equivalent f x y =
        let M = new builder<fxty> (is_fxty_equivalent)
        let (&&&) = M.binop_and_with_undo
        M {
            let! r = f x y
            return! M { return r } &&& is_kind_equivalent (x :> kinded).kind (y :> kinded).kind
        }

    and is_fxty_equivalent = is_kinded_equivalent is_fxty_equivalent'
    and is_ty_equivalent = is_kinded_equivalent is_ty_equivalent'

    let internal unM f = f state.empty |> fst



// non-monadic version
//

// TODOL: can type equivalence be written in a pure way?

//module Pure =
//    let private are_equivalent p l1 l2 = List.zip l1 l2 |> List.map (uncurry2 p) |> List.fold (&&) true
//
//    let rec is_kind_equivalent (x : kind) (y : kind) =
//        let are_equivalent = are_equivalent is_kind_equivalent
//        match x, y with
//        | K_Var α, K_Var β -> α = β
//
//        | K_Cons (x1, ks1), K_Cons (x2, ks2) when x1 = x2 && ks1.Length = ks2.Length ->
//             are_equivalent ks1 ks2
//
//        | _ -> false
//
//    and private is_ty_equivalent' (x : ty) (y : ty) =
//        let are_equivalent = are_equivalent is_ty_equivalent
//        match x, y with
//        | T_Cons (x, _), T_Cons (y, _)      -> x = y
//        | T_Var (α, _), T_Var (β, _)        -> α = β
//        | T_App (t1, t2), T_App (t1', t2')  -> are_equivalent [t1; t2] [t1'; t2']
//
//        | T_ForallsK (αs, t1), T_ForallsK (βs, t2) when αs.Length = βs.Length ->
//             is_prefixed_unquantified_ty_equivalent (prefix.of_bottoms αs, t1) (prefix.of_bottoms βs, t2)
//
//        | T_HTuple ts1, T_HTuple ts2 when ts1.Length = ts2.Length ->
//             are_equivalent ts1 ts2
//
//        | T_Closure _, _ | _, T_Closure _ ->
//            #if DEBUG
//            L.unexpected_error "comparing type closures: %O = %O" x y
//            #endif
//            false
//
//        | _ -> false
//
//    and private is_fxty_equivalent' (x : fxty) (y : fxty) =
//        match x, y with
//        | FxU_ForallsQ (Q1, t1), FxU_ForallsQ (Q2, t2) when Q1.dom.Count = Q2.dom.Count ->
//            is_prefixed_unquantified_ty_equivalent (Q1, t1) (Q2, t2)
//
//        | Fx_F_Ty t1, Fx_F_Ty t2   -> is_ty_equivalent t1 t2
//        | Fx_Bottom _, Fx_Bottom _ -> true
//
//        | _ -> false
//
//    and is_prefixed_unquantified_ty_equivalent (Q1 : prefix, t1) (Q2 : prefix, t2) =
//        assert (Q1.dom.Count = Q2.dom.Count)
//        let θ = new tsubst (Env.t.B { for (α, _), (β, t) in Seq.zip Q1 Q2 do yield α, T_Var (β, )
//        let t2' = subst_ty (!> θ) t2
//        in
//            is_ty_equivalent t1 t2'
//
//    and private is_kinded_equivalent p x y = p x y && is_kind_equivalent (x :> kinded).kind (y :> kinded).kind
//
//    and is_fxty_equivalent = is_kinded_equivalent is_fxty_equivalent'
//    and is_ty_equivalent = is_kinded_equivalent is_ty_equivalent'



// augmentations
//

open Monadic

type kind with
    member x.is_equivalent y = unM <| is_kind_equivalent x y

type ty with            
    member x.is_equivalent y = unM <| is_ty_equivalent x y

type fxty with
    member x.is_equivalent y = unM <| is_fxty_equivalent x y

