(*
 * Lw
 * Typing/Resolve.fs: constraint resolution sub-system
 * (C) 2000-2014 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Resolve

open FSharp.Common.Prelude
open FSharp.Common.Log
open FSharp.Common
open Lw.Core.Absyn
open Lw.Core.Globals
open Lw.Core.Typing.Defs
open Lw.Core.Typing.StateMonad
open Lw.Core.Typing.Utils
open Lw.Core.Typing.Unify
open Lw.Core.Typing.Meta


// constraint resolution
//

type [< NoComparison; NoEquality >] candidate =
    {
        jk          : jenv_key
        constraints : constraints
        σ           : scheme
        δ           : int
        θ           : tsubst * ksubst
    }
with
    override this.ToString () = this.pretty
    member this.pretty = sprintf "%O : %O [δ = %d]" this.jk this.σ this.δ

let private search_best_candidate ctx p cx ct jkσs =
    [ for jk, σ in jkσs do
            let csi, _, ti = instantiate σ
            match try_principal_type_of ctx ti ct with
            | Some (tθ : tsubst, kθ) ->
                yield { constraints = csi
                        jk          = jk
                        σ           = σ
                        δ           = (tθ.restrict ti.fv).dom.Count
                        θ           = tθ, kθ }
            | _ -> ()
      ] |> List.sortBy (fun cand -> cand.δ)
        |> function
           | []     -> None
           | cand0 :: _ as cands ->
                match List.filter (fun cand -> cand0.δ = cand.δ && p cand) cands with
                | []      -> None
                | [cand0] -> Some cand0
                | _       -> Report.Warn.resolution_is_ambiguous ctx.loc cx ct cands
                             None

let private restrict_overloaded x (Γ : jenv) =
    seq {
        for jk, jv in Γ do
            match jk, jv with
            | Jk_Inst (y, _), { mode = Jm_Normal; scheme = σ } when y = x -> yield jk, σ
            | _ -> ()
        }

let rec resolve_constraints (ctx : context) e0 =
    let M = new translator_typing_builder<_, _> (e0)
    let loc = e0.loc
    let L0 x = Lo loc x
    M {
        if ctx.resolution <> Res_No then
            let! { γ = γ; Γ = Γ; constraints = cs } = M.get_state
            #if DEBUG_RESOLVE
            L.debug Low "resolving constraints: %O" cs
            #endif
            if not cs.is_empty then
                let mgu_ctx = { mgu_context.loc = loc; γ = γ }
                for { name = x; ty = t } as c in cs do
                    let strict = ctx.resolution = Res_Strict && c.strict
                    let jkσs = restrict_overloaded x Γ
                    if not (Seq.isEmpty jkσs) then
                        match search_best_candidate mgu_ctx (fun cand -> if strict then cand.δ = 0 else true) x t jkσs with
                        | None -> ()
                        | Some cand ->
                            L.resolve Normal "%s : %O\n ~~> %O" x t cand
                            do! M.remove_constraint c
                            do! M.update_subst cand.θ
                            let p = P_CId c
                            let e1 = E_Jk cand.jk
                            let e2 = e0.value
                            M.translated <- Let (L0 (D_Bind [{ qual = decl_qual.none; patt = L0 p; expr = L0 e1 }]), L0 e2)
                            do! M.add_constraints cand.constraints
                            if cand.constraints.exists (fun c' -> x = c'.name && t = c'.ty) then
                                return Report.Warn.cyclic_constraint loc c t
                let! cs' = M.get_constraints
                if not (cs.forall (fun c -> cs'.exists (fun c' -> c.name = c'.name && c.ty = c'.ty))) then
                    do! resolve_constraints ctx e0
    }