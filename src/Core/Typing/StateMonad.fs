(*
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
        Γ   : jenv              // type judices
        χ   : kjenv             // kind judices
        δ   : tenv              // evaluated types
        θ   : tsubst            // type substitution
        Θ   : ksubst            // kind substitution
        π   : predicate         // global predicate

        named_tyvars   : Env.t<id, int>    // named type variables
    }
with
    override this.ToString () = this.pretty

    member this.pretty =
        let p (env : Env.t<_, _>) = env.pretty ":" "\n"
        in
            sprintf "Γ:\n%s\n\nθ:\n%O\n" (p this.Γ) this.θ

    static member empty =
        {
            Γ   = Env.empty
            χ   = Env.empty
            θ   = tsubst.empty
            δ   = tenv.empty
            Θ   = ksubst.empty
            π   = predicate.empty

            named_tyvars = Env.empty
        }

    member this.Σ = this.θ, this.Θ
        
type K<'a> = Monad.M<'a, state>

// TODO: rename Jb, Jk and Jm prefixes with Γb, Γk, Γm
let (|Jb_Overload|Jb_Var|Jb_Data|Jb_OverVar|Jb_Unbound|) = function
    | Some (Jk_Var _, { mode = Jm_Overloadable; scheme = Ungeneralized t }) -> Jb_Overload (refresh_ty t)
    | Some (Jk_Var _, { mode = Jm_Normal; scheme = σ })                     -> Jb_Var σ
    | Some (Jk_Inst _, { mode = Jm_Overloadable; scheme = _ })              -> Jb_OverVar
    | Some (Jk_Data _, { mode = Jm_Normal; scheme = σ })                    -> Jb_Data σ
    | None                                                                  -> Jb_Unbound
    | Some (jk, jv)                                                         -> unexpected "ill-formed jenv binding: %O = %O" __SOURCE_FILE__ __LINE__ jk jv

type state_builder (loc : location) =
    inherit Monad.state_builder<state> ()

    member __.get_Γ st = st.Γ, st
    member __.get_Δ st = st.δ, st
    member __.get_χ st = st.χ, st
    member __.get_θ st = st.θ, st
    member __.get_π st = st.π, st
    member M.get_Σ = M { let! s = M.get_state in return s.θ, s.Θ }
    member M.get_constraints = M { let! { constraints = cs } = M.get_π in return cs }
    member __.get_named_tyvars st = st.named_tyvars, st

    member __.lift_Γ f st = (), { st with Γ = f st.Γ |> subst_jenv st.Σ }
    member __.lift_Δ f st = (), { st with δ = f st.δ }
    member __.lift_χ f st = (), { st with χ = f st.χ |> subst_kjenv st.Θ }
    member __.lift_π f (st : state) = (), { st with π = subst_predicate st.Σ (f st.π) }
    member __.lift_named_tyvars f (st : state) = (), { st with named_tyvars = f st.named_tyvars }

    member M.set_Γ x = M.lift_Γ (fun _ -> x)
    member M.set_Δ x = M.lift_Δ (fun _ -> x)
    member M.set_χ x = M.lift_χ (fun _ -> x)
    member M.set_π x = M.lift_π (fun _ -> x)
    member M.set_named_tyvars x = M.lift_named_tyvars (fun _ -> x)

    member M.clear_constraints = M.set_π predicate.empty

    member M.update_subst Σ =
        M {
            do! M.lift_state (fun s ->
                    let θ, Θ as Σ = compose_tksubst Σ s.Σ
                    in
                        { χ = subst_kjenv Θ s.χ
                          δ = subst_tenv Σ s.δ
                          θ = θ
                          Θ = Θ
                          Γ = subst_jenv Σ s.Γ
                          π = subst_predicate Σ s.π
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
            let! { χ = χ; Θ = Θ } = M.get_state
            return kgeneralize (subst_kind Θ k) χ
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

    member M.bind_χ x ς =
        M {
            let! _, Θ = M.get_Σ
            let ς = subst_kscheme Θ ς
            do! M.lift_χ (fun χ -> χ.bind x ς)
            return ς
        }
        
    member M.gen_bind_χ x k =
        M {
            let! ς = M.kgen k
            return! M.bind_χ x ς
        }

    member M.bind_Δ x t =
        M {
            do! M.lift_Δ (fun Δ -> Δ.bind x t)
        }

    member M.search_χ x =
        M {
            let! χ = M.get_χ
            return χ.search x
        }

    member M.lookup_χ x =
        M {
            let! χ = M.get_χ
            return M.lookup Report.Error.unbound_type_symbol χ x
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

    member M.fork_Γ f =
        M {
            let! Γ = M.get_Γ
            let! r = f
            do! M.set_Γ Γ
            return r
        }

    member M.fork_χ f =
        M {
            let! Γ = M.get_χ
            let! r = f
            do! M.set_χ Γ
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

// TODO: questi nomi di builder sono orrendi: non si capisce che questo qui traduce le expr facendo un side-effect

type typing_state_builder (loc) =
    inherit state_builder (loc)
    member __.Yield ((x, t : ty)) = fun (s : state) -> (x, subst_ty s.Σ t), s
    member M.Yield (t : ty) = M { let! (), r = M { yield (), t } in return r }
    member M.YieldFrom f = M { let! (r : ty) = f in yield r }

type node_typing_state_builder<'u, 'a> (e : node<'u, 'a>) =
    inherit typing_state_builder (e.loc)
//    member M.translate x = M { e.value <- x }   // TODO: rinominare la property value in modo che sia più chiaro che ospita l'espressione tradotta?
    member __.translated with set x = e.value <- x 
//    new (ctx : context, node) = new node_typing_state_builder<'u, 'a> (node, ctx.loc)

type kinding_state_builder<'u> (τ : node<'u, kind>) = //, ?loc : location) =
    inherit state_builder (τ.loc)
    member __.Yield ((x, k : kind)) = fun s -> let k = subst_kind s.Θ k in τ.typed <- k; (x, k), s
    member M.Yield (k : kind) = M { let! (), r = M { yield (), k } in return r }
    member M.YieldFrom f = M { let! (r : kind) = f in yield r }
//    new (ctx : context, node) = new kinding_state_builder<'u> (node, ctx.loc)
