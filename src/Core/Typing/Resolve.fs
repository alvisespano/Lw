(*
 * Lw
 * Typing/Resolve.fs: constraint resolution sub-system
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Resolve

open FSharp.Common.Log
open FSharp.Common
open Lw.Core.Absyn
open Lw.Core.Absyn.Misc
open Lw.Core.Absyn.Var
open Lw.Core.Absyn.Kind
open Lw.Core.Absyn.Factory
open Lw.Core.Absyn.Ast
open Lw.Core.Globals
open Lw.Core.Typing.Defs
open Lw.Core.Typing.StateMonad
open Lw.Core.Typing.Ops
open Lw.Core.Typing.Unify
open Lw.Core.Typing.Meta
open Lw.Core.Typing.Equivalence


// constraint resolution
//

type [< NoComparison; NoEquality >] candidate =
    {
        jk          : jenv_key
        constraints : constraints
        σ           : tscheme
        δ           : int
        θ           : tksubst
    }
with
    override this.ToString () = this.pretty
    member this.pretty = sprintf "%O : %O [δ = %d]" this.jk this.σ this.δ

let private search_best_candidate ctx p cx ct jkσs =
    [ for jk, σ : tscheme in jkσs do
            let { constraints = csi; fxty = ϕi } = σ.instantiate
            let ti = ϕi.ftype // TODO: can we use flex types here?
            match ti.try_instance_of ctx ct with
            | Some θ ->
                yield { constraints = csi
                        jk          = jk
                        σ           = σ
                        δ           = (θ.t.restrict ti.fv).dom.Count
                        θ           = θ }
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
            | jenv_key.Inst (y, _), { mode = jenv_mode.Normal; scheme = σ } when y = x -> yield jk, σ
            | _ -> ()
        }

let rec resolve_constraints (ctx : context) e0 =
    let M = new translatable_type_inference_builder<_> (e0, ctx)
    let loc = e0.loc
    let L0 x = Lo loc x
    M {
        if ctx.resolution <> Res_No then
            let! Γ = M.get_Γ
            let! cs = M.get_constraints
            #if DEBUG_RESOLVE
            L.debug Low "resolving constraints: %O" cs
            #endif
            if not cs.is_empty then
                let! uctx = M.get_uni_context e0.loc
                for { name = x; ty = t } as c in cs do
                    let strict = ctx.resolution = Res_Strict && c.strict
                    let jkσs = restrict_overloaded x Γ
                    if not (Seq.isEmpty jkσs) then
                        match search_best_candidate uctx (fun cand -> if strict then cand.δ = 0 else true) x t jkσs with
                        | None -> ()
                        | Some candidate ->
                            L.resolve Normal "%s : %O\n ~~> %O" x t candidate
                            do! M.remove_constraint c
                            do! M.update_θ candidate.θ
                            let p = P_CId c
                            let e1 = E_Jk candidate.jk
                            let e2 = e0.value
                            M.translate <- Let (L0 (D_Bind [{ qual = decl_qual.none; patt = L0 p; expr = L0 e1 }]), L0 e2)
                            do! M.add_constraints candidate.constraints
                            if candidate.constraints.exists (fun c' -> x = c'.name && t.is_equivalent c'.ty) then
                                return Report.Warn.cyclic_constraint loc c t
                let! cs' = M.get_constraints
                if not (cs.forall (fun c -> cs'.exists (fun c' -> c.name = c'.name && c.ty.is_equivalent c'.ty))) then
                    do! resolve_constraints ctx e0
    }