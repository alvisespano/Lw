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
            let t, r', θ = R r l
            in
                t, T_Row_Ext (l', t', r'), θ

    | T_Row_Var ρ ->
        let γ = ty.fresh_var
        let β = T_Row_Var var.fresh
        let t = T_Row_Ext (l, γ, β)
        in
            γ, β, new tsubst (ρ, t)

    | T_Row_Empty ->
        Report.Error.cannot_rewrite_row loc l t1 t2

    | T_NoRow _ ->
        unexpected "row type expected: %O" __SOURCE_FILE__ __LINE__ r0
                

[< RequireQualifiedAccess >]
module Mgu =

    let check_circularity (θ : tsubst) =
        for α, t in θ do
            if Set.contains α t.fv then Debugger.Break ()
            match t with
            | T_Var (β, _) when α = β -> Debugger.Break ()
            | _ -> ()
        θ

    module Pure =

        let mgu (ctx : mgu_context) t1_ t2_ =
            let ( ** ) = compose_tksubst
            let S = subst_ty
            let Sk = subst_kind
            let loc = ctx.loc
            let rec R t1 t2 =        
                match t1, t2 with
                | T_Cons (x, k1), T_Cons (y, k2) when x = y -> tsubst.empty, kmgu ctx k1 k2
                | T_Var (α, k1), T_Var (β, k2) when α = β   -> tsubst.empty, kmgu ctx k1 k2
                                      
                | (T_Row _ as s), T_Row_Ext (l, t, (T_Row (_, ρo) as r)) ->
                    let t', s', θ1 = rewrite_row loc t1 t2 s l
                    let Σ1 = θ1, ksubst.empty
                    Option.iter (fun ρ -> if Set.contains ρ θ1.dom then Report.Error.row_tail_circularity loc ρ θ1) ρo
                    let Σ2 = R (S Σ1 t) (S Σ1 t')
                    let Σ3 =
                        let Σ = Σ2 ** Σ1
                        in
                            R (S Σ r) (S Σ s')
                    in
                        Σ3 ** Σ2 ** Σ1

                | T_Var (α, k), t
                | t, T_Var (α, k) ->
                    let kt = t.kind
                    let Θ = kmgu ctx k kt
                    in
                        if Set.contains α t.fv then Report.Error.circularity loc t1_ t2_ (T_Var (α, Sk Θ k)) t
                        else new tsubst (α, t) |> check_circularity, Θ

                | T_App (t1, t2), T_App (t1', t2') ->
                    let Σ1 = R t1 t1'
                    let Σ2 = R (S Σ1 t2) (S Σ1 t2')
                    in
                        Σ2 ** Σ1
                                                           
                | t1, t2 ->
                    raise (Mismatch (t1, t2))
            in
                try R t1_ t2_
                with Mismatch (t1, t2) -> Report.Error.type_mismatch loc t1_ t2_ t1 t2


    module Computational =
       
        let private __tYield _Yield (θ : tsubst) = _Yield ((θ, ksubst.empty))
        let private __kYield _Yield (Θ : ksubst) = _Yield ((tsubst.empty, Θ))
        let private __YieldFrom _Bind _Yield f = _Bind (f, _Yield) // { let! (r : tksubst) = f in yield r }

        module StateMonad =

           type [< NoEquality; NoComparison >] state = { Σ : tksubst }

           type mgu_builder () =
                inherit Monad.state_builder<state> ()
                member __.Zero () = fun s -> s.Σ, s
                member __.Yield (Σ : tksubst) = fun s -> let Σ = compose_tksubst Σ s.Σ in Σ, { Σ = Σ }
                member this.YieldFrom f = __YieldFrom this.Bind (fun (Σ : tksubst) -> this.Yield Σ) f
                member this.Yield x = __tYield this.Yield x
                member this.Yield x = __kYield this.Yield x
                member __.get = fun s -> s.Σ, s
       
           let mgu (ctx : mgu_context) t1_ t2_ =
                let loc = ctx.loc
                let U = new mgu_builder ()
                let S = subst_ty
                let rec R t1 t2 =
                    U {                    
                        let! Σ = U.get
                        let S = S Σ
                        match t1, t2 with
                        | T_Cons (x, k1), T_Cons (y, k2) when x = y ->
                            yield kmgu ctx k1 k2

                        | T_Var (α, k1), T_Var (β, k2) when α = β ->
                            yield kmgu ctx k1 k2
                                      
                        | T_Row _ as s, T_Row_Ext (l, t, (T_Row (_, ρo) as r)) ->
                            let t', s', θ1 = rewrite_row loc t1 t2 s l
                            match ρo with
                            | None -> ()
                            | Some ρ ->                            
                                if Set.contains ρ θ1.dom then Report.Error.row_tail_circularity loc ρ θ1
                                yield! R t t'
                                yield! R r s'

                        | T_Var (α, k) as tα, t
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
                    R t1_ t2_ { Σ = tsubst.empty, ksubst.empty } |> fst
        

        module Functional =

            type mgu_builder () =
                inherit Computation.Builder.collection<tksubst> ((tsubst.empty, ksubst.empty), fun Σ1 Σ2 -> compose_tksubst Σ2 Σ1)
                member this.YieldFrom (θ : tsubst) = this.YieldFrom ((θ, ksubst.empty))
                member this.YieldFrom (Θ : ksubst) = this.YieldFrom ((tsubst.empty, Θ))

            let mgu (ctx : mgu_context) t1_ t2_ =
                let loc = ctx.loc
                let U = new mgu_builder ()
                let S = subst_ty
                let rec R t1 t2 =
                    U {                    
                        let! Σ = U.get
                        let S = S Σ
                        match t1, t2 with
                        | T_Cons (x, k1), T_Cons (y, k2) when x = y ->
                            yield! kmgu ctx k1 k2

                        | T_Var (α, k1), T_Var (β, k2) when α = β ->
                            yield! kmgu ctx k1 k2
                                      
                        | T_Row _ as s, T_Row_Ext (l, t, (T_Row (_, ρo) as r)) ->
                            let t', s', θ1 = rewrite_row loc t1 t2 s l
                            match ρo with
                            | None -> ()
                            | Some ρ ->
                                if Set.contains ρ θ1.dom then Report.Error.row_tail_circularity loc ρ θ1
                                yield! R t t'
                                yield! R r s'

                        | T_Var (α, k) as tα, t
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


let multi_mgu_comparison equals fs x =
    let ret = function
        | Choice1Of2 Σ -> Σ
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
                        (match r with Choice1Of2 (θ, Θ) -> sprintf "tsubst = %O\n\tksubst = %O" θ Θ | Choice2Of2 ex -> pretty_exn_and_inners ex))
                "\n" rs')
        #if DEBUG
        System.Diagnostics.Debugger.Break ()
        #endif
        ret r1


// TODO: debug multiple mgus and remove this
let multi_mgu =
    [ "pure", Mgu.Pure.mgu
      "func", Mgu.Computational.Functional.mgu
      "monad", Mgu.Computational.StateMonad.mgu ]
    |> List.map (fun (a, b) -> a, uncurry3 b)
    |> multi_mgu_comparison
            (fun r1 r2 ->
                match r1, r2 with
                | Choice1Of2 (θ1, Θ1), Choice1Of2 (θ2, Θ2) -> let p x = sprintf "%O" x in p θ1 = p θ2 && p Θ1 = p Θ2
                | Choice2Of2 ex1, Choice2Of2 ex2           -> let p = pretty_exn_and_inners in p ex1 = p ex2
                | _ -> false)
    |> curry3

let mgu = multi_mgu

let try_mgu ctx t1 t2 =
    try Some (mgu ctx t1 t2)
    with :? Report.type_error -> None
    
type state_builder with
    member M.unify loc t1 t2 =
        M {
            let! { θ = θ; Θ = Θ; χ = χ } = M.get_state
            let Σ = θ, Θ
            let θ, Θ as Σ = mgu { loc = loc; χ = χ } (subst_ty Σ t1) (subst_ty Σ t2)
            L.mgu "[U] %O == %O // [%O] // [%O]" t1 t2 θ Θ
            do! M.update_subst Σ
        }

let try_principal_type_of ctx pt t =
    try_mgu ctx pt t |> Option.bind (fun Σ -> let t1 = subst_ty Σ pt in if t1 = t then Some Σ else None)

let is_principal_type_of ctx pt t = (try_principal_type_of ctx pt t).IsSome

let is_instance_of ctx pt t =
    let Σ = mgu ctx pt t
    let t = subst_ty Σ t
    in
        is_principal_type_of ctx pt t   // TODO: unification is not enough: unifier must be SMALLER - that would tell whether it's an actual instance
