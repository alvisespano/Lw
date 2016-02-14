(*
 * Lw
 * Typing/StateMonad.fs: custom monad for typing
 * (C) 2000-2015 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.StateMonad

open FSharp.Common.Prelude
open FSharp.Common.Log
open FSharp.Common
open Lw.Core
open Lw.Core.Absyn
open Lw.Core.Typing.Defs
open Lw.Core.Typing.Ops
open Lw.Core.Globals


type [< NoComparison; NoEquality; System.Diagnostics.DebuggerDisplayAttribute("{ToString()}") >] state =
    {
        // environments
        Γ   : jenv              // type judices
        γ   : kjenv             // kind judices
        δ   : tenv              // evaluated types

        // substitutions
        θ   : tksubst           // substitution
        Q   : prefix            // prefix for quantified type variables

        // extras
        constraints     : constraints       // global constraints
        scoped_vars    : Env.t<id, int>    // named type variables
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
            θ   = tksubst.empty
            δ   = tenv.empty
            Q   = Q_Nil

            constraints     = constraints.empty
            scoped_vars    = Env.empty
        }

        
type M<'a> = Monad.M<'a, state>

let (|Jb_Overload|Jb_Var|Jb_Data|Jb_OverVar|Jb_Unbound|) = function
    | Some (Jk_Var _, { mode = Jm_Overloadable; scheme = Ungeneralized t }) -> Jb_Overload t.instantiate_fv
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
    member __.get_Q st = st.Q, st
    member __.get_constraints st = st.constraints, st
    member M.get_θ = M { let! s = M.get_state in return s.θ }
    member __.get_scoped_vars st = st.scoped_vars, st

    member __.lift_Γ f st = (), { st with Γ = f st.Γ |> subst_jenv st.θ }
    member __.lift_Δ f st = (), { st with δ = f st.δ }
    member __.lift_γ f st = (), { st with state.γ = f st.γ |> subst_kjenv st.θ.k }
    member __.lift_Q f st = (), { st with Q = f st.Q }
    member __.lift_θ f st = (), { st with θ = f st.θ }
    member __.lift_constraints f (st : state) = (), { st with constraints = subst_constraints st.θ (f st.constraints) }
    member __.lift_scoped_vars f (st : state) = (), { st with scoped_vars = f st.scoped_vars }

    member M.set_Γ x = M.lift_Γ (fun _ -> x)
    member M.set_Δ x = M.lift_Δ (fun _ -> x)
    member M.set_γ x = M.lift_γ (fun _ -> x)
    member M.set_Q x = M.lift_Q (fun _ -> x)
    [< System.Obsolete("Global substitution should never be set explicitly: use update_θ method instead.") >]
    member M.set_θ x = M.lift_θ (fun _ -> x)
    member M.set_constraints x = M.lift_constraints (fun _ -> x)
    member M.set_scoped_vars x = M.lift_scoped_vars (fun _ -> x)

    member M.clear_constraints = M.set_constraints constraints.empty

    // TODO: design a smart system for pruning substition automatically via weak pointers.
    //       The basic implementation idea behind it is to use weak references: each object of type var carries a reference count, which implies that each type a given var 
    //       appears in increases the counter. Naturally, also substitutions carry objects of type var, but substitutions should count as weak references, in such a way
    //       that when a var is being referenced only from within a substitution, the substitution entry can be safely removed because we ensure no other type is referencing that var any longer.
    member M.update_θ θ =
        M {
            do! M.lift_state (fun s ->
                    let θ = compose_tksubst θ s.θ
                    in
                        { γ = subst_kjenv θ.k s.γ
                          δ = subst_tenv θ s.δ
                          θ = θ
                          Γ = subst_jenv θ s.Γ
                          Q = subst_prefix θ s.Q
                          constraints = subst_constraints θ s.constraints
                          scoped_vars = s.scoped_vars })
            let! θ' = M.get_θ
            L.debug Normal "[S+] %O\n     = %O" θ θ'
        }


    member internal __.lookup report (env : Env.t<_, _>) x =
        try env.lookup x
        with Env.UnboundSymbol x -> report loc x

    member M.add_scoped_var x =
        M {
            let! vas = M.get_scoped_vars
            match vas.search x with
            | Some n -> return Va (n, Some x)
            | None   -> let Va (n, _) as α = var.fresh_named x
                        do! M.lift_scoped_vars (fun vas -> vas.bind x n)
                        return α
        }

    member M.get_scoped_vars_as_set =
        M {
            let! vas = M.get_scoped_vars
            return Computation.B.set { for x, n in vas do yield Va (n, Some x) }
        }

    member M.fork_scoped_vars f =
        M {
            let! Γ = M.get_scoped_vars
            let! r = f
            do! M.set_scoped_vars Γ
            return r
        }

    member M.bind_γ x kσ =
        M {
            let! θ = M.get_θ
            let kσ = subst_kscheme θ.k kσ
            do! M.lift_γ (fun γ -> γ.bind x kσ)
            return kσ
        }
        
    member M.gen_bind_γ x k =
        M {
            let! { γ = γ; θ = θ } = M.get_state
            let! αs = M.get_scoped_vars_as_set
            let kσ = (subst_kind θ.k k).generalize γ αs
            return! M.bind_γ x kσ
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

    member M.fork_γ f =
        M {
            let! Γ = M.get_γ
            let! r = f
            do! M.set_γ Γ
            return r
        }


// specialized monad for type inference and translation
//

type type_inference_builder (loc) =
    inherit basic_builder (loc)

    new () = new type_inference_builder (new location ())

    member M.Yield (ϕ : fxty) =
        M {
            let! ϕ = M.updated ϕ
            return ϕ
        }

    member M.Yield (t : ty) = M { yield Fx_F_Ty t }   
    member M.Yield ((x : id, t : ty)) = M { let! t = M.updated t in return x, t }    // used for row types

    // used when inferring let bindings    
    member M.Yield l =
        M {
            return! M.List.map (fun (b : _, x : id, cs : constraints, ϕ : fxty) -> M {
                        let! ϕ = M.updated ϕ
                        let! cs = M.updated cs
                        return b, x, cs, ϕ
                    }) l                    
        }

    // used by some HML rules inferring foralls where the type part have been substituted
    member M.Yield ((Q : prefix, t : ty)) =
        M {
            assert Q.dom.IsSubsetOf t.fv
            let! θ = M.get_θ
            assert (Set.intersect Q.dom θ.dom).IsEmpty
            yield Fx_ForallsQ (Q, Fx_F_Ty t)
        }

    // banged versions
    member M.YieldFrom f = M { let! (r : fxty) = f in yield r }
    member M.YieldFrom f = M { let! (r : list<_ * id * constraints * fxty>) = f in yield r }

    member M.fork_Γ f =
        M {
            let! Γ = M.get_Γ
            let! r = f
            do! M.set_Γ Γ
            return r
        }

    member M.fork_Q f =
        M {
            let! Q = M.get_Q
            let! r = f
            do! M.set_Q Q
            return r
        }

    member M.updated (t : ty) =
        M {
            let! θ = M.get_θ
            return subst_ty θ t
        }

    member M.updated (ϕ : fxty) =
        M {
            let! θ = M.get_θ
            return subst_fxty θ ϕ
        }

    member M.updated cs =
        M {
            let! θ = M.get_θ
            return subst_constraints θ cs
        }

    member M.split_prefix αs =
        M {
            let! Q = M.get_Q
//            let! Q = M.updated Q    // TODO: is this really needed?
            let Q1, Q2 = Q.split αs
            do! M.set_Q Q1
            return Q2
        }

    member M.extend (α, ϕ) =
        M {
//            let! t = M.updated t
            let! Q = M.get_Q
            let Q, θ = Q.extend (α, ϕ)
            do! M.set_Q Q
            do! M.update_θ θ
        }

    member M.extend xs =
        M {
            for α, t in xs do
                do! M.extend (α, t)
        }

    member M.update_prefix_with_bound (Q : prefix) (α, ϕ : fxty) =
        M {
//            let! ϕ = M.updated ϕ
            let Q, θ = Q.update_prefix_with_bound (α, ϕ)
            do! M.set_Q Q
            do! M.update_θ θ
        }

    member M.update_prefix_with_subst (Q : prefix) (α, t : ty) =
        M {
//            let! t = M.updated t
            let Q, θ = Q.update_prefix_with_subst (α, t)
            do! M.set_Q Q
            do! M.update_θ θ            
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
            let! θ = M.get_θ
            let σ = subst_scheme θ σ
            do! M.lift_Γ (fun Γ -> Γ.bind jk jv)
            return σ
        }

    member M.bind_ungeneralized_Γ x t =
        M {
            return! M.bind_Γ (Jk_Var x) { mode = Jm_Normal; scheme = Ungeneralized t }
        }

    // TODO: check generalization and finalization
    member M.bind_generalized_Γ jk jm ϕ =
        M {
            let! σ = M {
                let! cs = M.get_constraints
                match ϕ with
                | Fx_ForallsQ0 (Q, ϕ1) ->
                    let! αs = M.get_scoped_vars_as_set
                    let _, Q2 = Q.split αs
                    let! ϕ = M.updated (Fx_ForallsQ (Q2, ϕ1))
                    return { constraints = cs; fxty = ϕ }
            }
            return! M.bind_Γ jk { mode = jm; scheme = σ }
        }
        
    member M.add_prefix α t =
        M {
            do! M.lift_Q (fun Q -> Q + (α, t))
        }

    member M.add_constraint c =
        M {
            do! M.lift_constraints (fun cs -> cs.add c)
        }

    member M.add_constraints cs =
        M {
            do! M.lift_constraints (fun cs0 -> cs0 + cs)
        }

    member M.remove_constraint c =
        M {
            do! M.lift_constraints (fun cs -> cs.remove c)
        }

    member M.instantiate_and_inherit_constraints (σ : scheme) =
        M {            
            let σ = σ.instantiate
            do! M.add_constraints σ.constraints
            return σ
        }

    member M.fork_constraints f =
        M {
            let! π = M.get_constraints
            let! r = f
            do! M.set_constraints π
            return r
        }

type translatable_type_inference_builder<'e> (e : node<'e, unit>) =
    inherit type_inference_builder (e.loc)
    member __.translated with set x = e.value <- x 


// specialized monad for type evaluation
//

type type_eval_builder<'e> (τ : node<'e, kind>) =
    inherit basic_builder (τ.loc)

    member M.Yield (ϕ : fxty) = M { return ϕ }
    member M.Yield (t : ty) = M { yield Fx_F_Ty t }

    member M.YieldFrom f = M { let! (r : ty) = f in yield r }
    member M.YieldFrom f = M { let! (r : fxty) = f in yield r }

    member M.search_Δ x =
        M {
            let! Δ = M.get_Δ
            return Δ.search x
        }

    member M.bind_Δ x t =
        M {
            do! M.lift_Δ (fun Δ -> Δ.bind x t)
        }
    
    member M.fork_Δ f =
        M {
            let! Δ = M.get_Δ
            let! r = f
            do! M.set_Δ Δ
            return r
        }



// specialized monad kind inference
//

// yield operations do decorate nodes
type kind_inference_builder<'e> (τ : node<'e, kind>) =
    inherit basic_builder (τ.loc)

    member M.Yield (k : kind) =
        M {
            let! k = M.updated k
            τ.typed <- k
            return k
        }

    member M.Yield ((x, k : kind)) =
        M {
            let! k = M.updated k
            τ.typed <- k
            return x, k
            
        }
    
    member M.YieldFrom f = M { let! (r : kind) = f in yield r }

    member M.updated k =
        M {
            let! θ = M.get_θ
            return subst_kind θ.k k
        }
        