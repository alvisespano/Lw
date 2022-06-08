(*
 * Lw
 * Typing/Subst.fs: substitutions
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Subst

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
open System.Collections
open System.Collections.Generic


// substitutions
//

type [< NoComparison >] subst< [< EqualityConditionalOn >] 't> (env : Env.t<var, 't>) =
    interface IEnumerable<var * 't> with
        member __.GetEnumerator () = (env :> IEnumerable<_>).GetEnumerator ()

    interface IEnumerable with
        member this.GetEnumerator () = (this :> IEnumerable<_>).GetEnumerator () :> IEnumerator

    new () = new subst<'t> (Env.empty)
    new (α, t) = new subst<'t> (Env.empty.bind α t)

    member internal __.env = env

    member __.is_empty = env.is_empty
    member __.search = env.search
    member __.dom = env.dom
    member __.filter f = new subst<'t> (env.filter f)
    member this.restrict αs = this.filter (fun α _ -> Set.contains α αs)
    member this.remove αs = this.filter (fun α _ -> not <| Set.contains α αs)
    member __.map f = new subst<'t> (env.map f)
    member __.search_by f = env.search_by f

    static member pretty_item (bra, ket, α : var, t : 't) = sprintf "%s%O %s %O%s" bra α Config.Printing.substitution_sep t ket
    static member pretty_item (α, t) = subst<'t>.pretty_item ("[", "]", α, t)
    member __.pretty (bra, ket) = if env.is_empty then sprintf "%s%s" bra ket else env.pretty_by_binding (fun α t -> subst<'t>.pretty_item (bra, ket, α, t)) ""
    override this.ToString () = this.pretty ("[", "]")
      
    member private θ1.append (θ2 : subst<'t>) =
        assert (Set.intersect θ1.dom θ2.dom).IsEmpty    // HACK: if this assert gets triggered, try change compose as described in the note below
        new subst<'t> (θ1.env + θ2.env)

    static member empty = new subst<'t> ()
  
    // from "Typing Haskell in Haskell":
    //      s1 @@ s2    = [ (u, apply s1 t) | (u,t) <- s2 ] ++ s1
    // HACK: this does not restrict domain of appended substitution, thus the assert in method append might get triggered
    member θ1.compose apply_subst (θ2 : subst<'t>) = (θ2.map (fun _ -> apply_subst θ1)).append θ1 // (θ2.restrict (θ2.dom - θ1.dom))

type ksubst = subst<kind>
type tsubst = subst<ty>

type [< NoComparison; NoEquality >] tksubst = { t : tsubst; k : ksubst }
with
    static member op_Implicit tθ = { t = tθ; k = ksubst.empty }
    static member op_Implicit kθ = { t = tsubst.empty; k = kθ }
    static member empty = { t = tsubst.empty; k = ksubst.empty }
    member θ.dom = θ.t.dom + θ.k.dom
    override this.ToString () = this.pretty
    member this.pretty = this.t.pretty ("[", "]") + if this.k.is_empty then "" else this.k.pretty ("{", "}") 
       


// substitution applications
//

let rec subst_kind (kθ : ksubst) =
    let S k = subst_kind kθ k
    in function
    | K_Cons (x, ks) -> K_Cons (x, List.map S ks)
    | K_Var α as k ->
        match kθ.search α with
        | Some β -> β
        | None   -> k

let subst_var (tθ : tsubst) α =
    match tθ.search α with
    #if DEBUG
    | Some (T_Var (β, _)) -> β
    | None                -> α
    | t                   -> unexpected "substituting type variable with non-variable type: %s" __SOURCE_FILE__ __LINE__ (subst<_>.pretty_item (α, t))
    #else
    | Some (T_Var (β, _)) -> β
    | _                   -> α
    #endif

let rec subst_ty =
    let rec subst_ty_in_ty (tθ : tsubst) =
        let S t = subst_ty_in_ty tθ t
        in function
        | T_Var (α, _) as t         -> either t (tθ.search α)
        | T_Forall (α, t)           -> T_Forall (subst_var tθ α, S t)
        | T_App (t1, t2)            -> T_App (S t1, S t2)
        | T_HTuple ts               -> T_HTuple (List.map S ts)
        | T_Cons _
        | T_Closure _ as t          -> t
    let rec subst_kind_in_ty kθ =
        let S t = subst_kind_in_ty kθ t
        let Sk k = subst_kind kθ k
        function
        | T_Var (α, k)              -> T_Var (α, Sk k)
        | T_Forall (α, t)           -> T_Forall (α, S t)
        | T_Cons (x, k)             -> T_Cons (x, Sk k)
        | T_App (t1, t2)            -> T_App (S t1, S t2)
        | T_HTuple ts               -> T_HTuple (List.map S ts)
        | T_Closure (x, Δ, τ, k)    -> T_Closure (x, Δ, τ, Sk k)
    in
        fun θ t -> t |> subst_ty_in_ty θ.t |> subst_kind_in_ty θ.k

let rec subst_fxty θ =
    let S x = subst_fxty θ x
    let St t = subst_ty θ t
    let Sk k = subst_kind θ.k k
    in function
    | Fx_Bottom k             -> Fx_Bottom (Sk k)
    | Fx_F_Ty t               -> Fx_F_Ty (St t)
    | Fx_Forall ((α, ϕ1), ϕ2) -> Fx_Forall ((subst_var θ.t α, S ϕ1), S ϕ2)


/// first argument is the NEW subst, second argument is the OLD one
let compose_ksubst (kθ' : ksubst) (kθ : ksubst) = kθ'.compose subst_kind kθ
let compose_tksubst { t = tθ'; k = kθ' } { t = tθ; k = kθ } =
    let kθ = compose_ksubst kθ' kθ
    let tθ = tθ'.compose (fun tθ -> subst_ty { t = tθ; k = kθ }) tθ     // this is correct: left argument of compose is 'this' when calling method compose, and composition have the NEW subst as first argument, i.e. left
    in
        { t = tθ; k = kθ }

let subst_prefix θ Q = prefix.B { for α, ϕ in Q do yield subst_var θ.t α, subst_fxty θ ϕ }

let subst_type_constraints _ tcs = tcs

let subst_constraints θ (cs : constraints) = cs.map (fun c -> { c with ty = subst_ty θ c.ty })

let subst_scheme θ σ =
    let { constraints = cs; fxty = ϕ } = σ
    in
        { constraints = subst_constraints θ cs; fxty = subst_fxty θ ϕ }
        
let subst_kscheme (kθ : ksubst) σκ =
    let { forall = αs; kind = k } = σκ
    let kθ = kθ.remove αs
    in
        { forall = αs; kind = subst_kind kθ k }

let subst_jenv θ (env : jenv) = env.map (fun _ ({ scheme = σ } as jv) -> { jv with scheme = subst_scheme θ σ })
let subst_kjenv kθ (env : kjenv) = env.map (fun _ -> subst_kscheme kθ)
let subst_tenv θ (env : tenv) = env.map (fun _ -> subst_ty θ)


// computation expression builders
//

[< CompilationRepresentationAttribute(CompilationRepresentationFlags.ModuleSuffix) >]
module subst =
    let B compose =
        new Computation.Builder.itemized_collection<_, subst<'a>> (empty = subst<_>.empty,
                                                                   singleton = (fun (α, t) -> new subst<_> (α, t)),
                                                                   plus = compose)

[< CompilationRepresentationAttribute(CompilationRepresentationFlags.ModuleSuffix) >]
module ksubst =
    let B = subst.B compose_ksubst

// TODOL: find a way for making a builder for tksubst
//[< CompilationRepresentationAttribute(CompilationRepresentationFlags.ModuleSuffix) >]
//module tksubst =
//    let B = subst.B compose_tksubst

