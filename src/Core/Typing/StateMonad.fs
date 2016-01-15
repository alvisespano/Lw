﻿(*
 * Lw
 * Typing/StateMonad.fs: custom monad for typing
 * (C) 2000-2015 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.StateMonad

open FSharp.Common.Prelude
open FSharp.Common
open Lw.Core
open Lw.Core.Absyn
open Lw.Core.Typing.Defs

type resolution = Res_Strict | Res_Loose | Res_No

type [< NoComparison; NoEquality >] context =
    { 
        top_level_decl  : bool
        resolution      : resolution
//        strict          : bool
    }
with
    static member top_level = {
        top_level_decl  = true
        resolution      = Res_Strict
//        strict          = true
    }

type [< NoComparison; NoEquality >] state =
    {
        // environments
        Γ   : jenv              // type judices
        γ   : kjenv             // kind judices
        δ   : tenv              // evaluated types

        // substitutions
        θ   : tsubst            // type substitution
        Θ   : ksubst            // kind substitution

        // predicates
        π   : predicate         // global predicate
        Q   : prefix            // prefix for quantified type variables

        // extras
        named_tyvars   : Env.t<id, int>    // named type variables
    }
with
    override this.ToString () = this.pretty

    member this.pretty =
        let p (env : Env.t<_, _>) = env.pretty Config.Printing.type_annotation_sep "\n"
        in
            sprintf "Γ:\n%s\n\nθ:\n%O\n" (p this.Γ) this.θ

    static member empty =
        {
            Γ   = Env.empty
            γ   = Env.empty
            θ   = tsubst.empty
            δ   = tenv.empty
            Θ   = ksubst.empty
            π   = predicate.empty
            Q   = []
            named_tyvars = Env.empty
        }

    member this.Σ = this.θ, this.Θ
        
type K<'a> = Monad.M<'a, state>

let (|Jb_Overload|Jb_Var|Jb_Data|Jb_OverVar|Jb_Unbound|) = function
    | Some (Jk_Var _, { mode = Jm_Overloadable; scheme = Ungeneralized t }) -> Jb_Overload (refresh_ty t)
    | Some (Jk_Var _, { mode = Jm_Normal; scheme = σ })                     -> Jb_Var σ
    | Some (Jk_Inst _, { mode = Jm_Overloadable; scheme = _ })              -> Jb_OverVar
    | Some (Jk_Data _, { mode = Jm_Normal; scheme = σ })                    -> Jb_Data σ
    | None                                                                  -> Jb_Unbound
    | Some (jk, jv)                                                         -> unexpected "ill-formed jenv binding: %O = %O" __SOURCE_FILE__ __LINE__ jk jv

type basic_builder (loc : location) =
    inherit Monad.state_builder<state> ()

    member __.get_Γ st = st.Γ, st
    member __.get_Δ st = st.δ, st
    member __.get_γ st = st.γ, st
    member __.get_θ st = st.θ, st
    member __.get_Q st = st.Q, st
    member __.get_π st = st.π, st
    member M.get_Σ = M { let! s = M.get_state in return s.θ, s.Θ }
    member M.get_constraints = M { let! { constraints = cs } = M.get_π in return cs }
    member __.get_named_tyvars st = st.named_tyvars, st

    member __.lift_Γ f st = (), { st with Γ = f st.Γ |> subst_jenv st.Σ }
    member __.lift_Δ f st = (), { st with δ = f st.δ }
    member __.lift_γ f st = (), { st with γ = f st.γ |> subst_kjenv st.Θ }
    member __.lift_Q f st = (), { st with Q = f st.Q }
    member __.lift_π f (st : state) = (), { st with π = subst_predicate st.Σ (f st.π) }
    member __.lift_named_tyvars f (st : state) = (), { st with named_tyvars = f st.named_tyvars }

    member M.set_Γ x = M.lift_Γ (fun _ -> x)
    member M.set_Δ x = M.lift_Δ (fun _ -> x)
    member M.set_γ x = M.lift_γ (fun _ -> x)
    member M.set_Q x = M.lift_Q (fun _ -> x)
    member M.set_π x = M.lift_π (fun _ -> x)
    member M.set_named_tyvars x = M.lift_named_tyvars (fun _ -> x)

    member M.clear_constraints = M.set_π predicate.empty

    member M.update_subst Σ =
        M {
            do! M.lift_state (fun s ->
                    let θ, Θ as Σ = compose_tksubst Σ s.Σ
                    in
                        { γ = subst_kjenv Θ s.γ
                          δ = subst_tenv Σ s.δ
                          θ = θ
                          Θ = Θ
                          Γ = subst_jenv Σ s.Γ
                          π = subst_predicate Σ s.π
                          Q = subst_prefix Σ s.Q
                          named_tyvars = s.named_tyvars })
        }

    member private M.gen t =
        M {
            let! { Γ = Γ; π = π; θ = θ; Θ = Θ } as st = M.get_state
            let vas = Computation.set { for x, n in st.named_tyvars do yield Va (n, Some x) }
            return generalize (π, subst_ty (θ, Θ) t) Γ vas
        }

    member private M.kgen k =
        M {
            let! { γ = γ; Θ = Θ } = M.get_state
            return kgeneralize (subst_kind Θ k) γ
        }

    member private __.lookup report (env : Env.t<_, _>) x =
        try env.lookup x
        with Env.UnboundSymbol x -> report loc x

    member M.add_named_tyvar x =
        M {
            let! vas = M.get_named_tyvars
            match vas.search x with
            | Some n -> return Va (n, Some x)
            | None   -> let Va (n, _) as α = var.fresh_named x
                        do! M.lift_named_tyvars (fun vas -> vas.bind x n)
                        return α
        }

    member M.bind_γ x ς =
        M {
            let! _, Θ = M.get_Σ
            let ς = subst_kscheme Θ ς
            do! M.lift_γ (fun γ -> γ.bind x ς)
            return ς
        }
        
    member M.gen_bind_γ x k =
        M {
            let! ς = M.kgen k
            return! M.bind_γ x ς
        }

    member M.bind_Δ x t =
        M {
            do! M.lift_Δ (fun Δ -> Δ.bind x t)
        }

    member M.search_γ x =
        M {
            let! γ = M.get_γ
            return γ.search x
        }

    member M.lookup_γ x =
        M {
            let! γ = M.get_γ
            return M.lookup Report.Error.unbound_type_symbol γ x
        }
        
    member M.search_binding_by_name_Γ x =
        M {
            let! Γ = M.get_Γ
            return Γ.search_by (fun jk { mode = jm } ->
                    match jk, jm with
                    | Jk_Var y, _
                    | Jk_Data y, _
                    | Jk_Inst (y, _), Jm_Overloadable -> x = y
                    | _                               -> false)
        }

    member M.lookup_Γ jk =
        M {
            let! Γ = M.get_Γ
            return M.lookup Report.Error.unbound_symbol Γ jk
        }

    member M.bind_Γ jk ({ scheme = σ } as jv) =
        M {
            let! Σ = M.get_Σ
            let σ = subst_scheme Σ σ
            do! M.lift_Γ (fun Γ -> Γ.bind jk jv)
            return σ
        }

    member M.bind_var_Γ x t =
        M {
            return! M.bind_Γ (Jk_Var x) { mode = Jm_Normal; scheme = Ungeneralized t }
        }

    member M.gen_bind_Γ jk jm (t : ty) =
        M {
            let! σ = M.gen t
            return! M.bind_Γ jk { mode = jm; scheme = σ }
        }

    member M.add_prefix α t =
        M {
            do! M.lift_Q (fun Q -> (α, t) :: Q)
        }

    member M.add_constraint c =
        M {
            do! M.lift_π (fun π -> { π with constraints = π.constraints.add c })
        }

    member M.add_constraints cs =
        M {
            do! M.lift_π (fun π -> { π with constraints = π.constraints + cs })
        }

    member M.remove_constraint c =
        M {
            do! M.lift_π (fun π -> { π with constraints = π.constraints.remove c })
        }

    member M.inst (ctx : context) σ =
        M {
            let π, t = instantiate σ
            do! M.add_constraints π.constraints
            return π, t
        }

    member M.fork_named_tyvars f =
        M {
            let! Γ = M.get_named_tyvars
            let! r = f
            do! M.set_named_tyvars Γ
            return r
        }

    member M.fork_Γ f =
        M {
            let! Γ = M.get_Γ
            let! r = f
            do! M.set_Γ Γ
            return r
        }

    member M.fork_γ f =
        M {
            let! Γ = M.get_γ
            let! r = f
            do! M.set_γ Γ
            return r
        }

    member M.fork_π f =
        M {
            let! π = M.get_π
            let! r = f
            do! M.set_π π
            return r
        }

    member M.fork_Δ f =
        M {
            let! Δ = M.get_Δ
            let! r = f
            do! M.set_Δ Δ
            return r
        }


type typing_builder (loc) =
    inherit basic_builder (loc)
    member __.Yield ((x, t : ty)) = fun (s : state) -> (x, subst_ty s.Σ t), s
    member M.Yield (t : ty) = M { let! (), r = M { yield (), t } in return r }
    member M.YieldFrom f = M { let! (r : ty) = f in yield r }

type translator_typing_builder<'u, 'a> (e : node<'u, 'a>) =
    inherit typing_builder (e.loc)
    member __.translated with set x = e.value <- x 

type kinding_builder<'u> (τ : node<'u, kind>) =
    inherit basic_builder (τ.loc)
    member __.Yield ((x, k : kind)) = fun s -> let k = subst_kind s.Θ k in τ.typed <- k; (x, k), s
    member M.Yield (k : kind) = M { let! (), r = M { yield (), k } in return r }
    member M.YieldFrom f = M { let! (r : kind) = f in yield r }
