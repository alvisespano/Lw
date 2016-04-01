(*
 * Lw
 * Typing/StateMonad.fs: custom monad for typing
 * (C) 2000-2015 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.StateMonad


open FSharp.Common.Log
open FSharp.Common
open Lw.Core
open Lw.Core.Absyn
open Lw.Core.Absyn.Misc
open Lw.Core.Absyn.Var
open Lw.Core.Absyn.Kind
open Lw.Core.Absyn.Sugar
open Lw.Core.Absyn.Ast
open Lw.Core.Typing.Defs
open Lw.Core.Typing.Ops
open Lw.Core.Globals
open Lw.Core.Typing.Subst


type [< NoComparison; NoEquality; System.Diagnostics.DebuggerDisplayAttribute("{ToString()}") >] state =
    {
        // environments
        Γ   : jenv              // type judices
        γ   : kjenv             // kind judices
        γα  : vakjenv           // kind judices for vars
        δ   : tenv              // evaluated types

        // substitutions
        θ   : tksubst           // substitution
        Q   : prefix            // prefix for quantified type variables

        // extras
        constraints : constraints       // global constraints
        scoped_vars : Set<var>          // named type variables
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
            γα  = Env.empty
            δ   = tenv.empty
            θ   = tksubst.empty
            Q   = Q_Nil

            constraints = constraints.empty
            scoped_vars = Set.empty
        }

        
type M<'a> = Monad.M<'a, state>

let (|Jb_Overload|Jb_Var|Jb_Data|Jb_OverVar|Jb_Unbound|) = function
    | Some (jenv_key.Var _, { mode = jenv_mode.Overload; scheme = Ungeneralized t }) -> Jb_Overload t
    | Some (jenv_key.Var _, { mode = jenv_mode.Normal; scheme = σ })                 -> Jb_Var σ
    | Some (jenv_key.Inst _, { mode = jenv_mode.Overload; scheme = _ })              -> Jb_OverVar
    | Some (jenv_key.Data _, { mode = jenv_mode.Normal; scheme = σ })                -> Jb_Data σ
    | None                                                              -> Jb_Unbound
    | Some (jk, jv)                                                     -> unexpected "ill-formed jenv binding: %O = %O" __SOURCE_FILE__ __LINE__ jk jv


type basic_builder (loc : location) =
    inherit Monad.state_builder<state> ()

    member __.get_Γ st = st.Γ, st
    member __.get_δ st = st.δ, st
    member __.get_γ st = st.γ, st
    member __.get_γα st = st.γα, st
    member __.get_Q st = st.Q, st
    member __.get_constraints st = st.constraints, st
    member __M.get_θ st = st.θ, st
    member __.get_scoped_vars st = st.scoped_vars, st

    member __.lift_Γ f st = (), { st with state.Γ = f st.Γ }
    member __.lift_δ f st = (), { st with δ = f st.δ }
    member __.lift_γ f st = (), { st with state.γ = f st.γ }
    member __.lift_γα f st = (), { st with state.γα = f st.γα }
    member __.lift_Q f st = (), { st with Q = f st.Q }
    member __.lift_θ f st = (), { st with θ = f st.θ }
    member __.lift_constraints f (st : state) = (), { st with constraints = f st.constraints }
    member __.lift_scoped_vars f (st : state) = (), { st with scoped_vars = f st.scoped_vars }

    member M.set_Γ x = M.lift_Γ (fun _ -> x)
    member M.set_δ x = M.lift_δ (fun _ -> x)
    member M.set_γ x = M.lift_γ (fun _ -> x)
    member M.set_γα x = M.lift_γα (fun _ -> x)
    member M.set_Q x = M.lift_Q (fun _ -> x)
    [< System.Obsolete("Global substitution should never be set explicitly: use update_θ method instead.") >]
    member M.set_θ x = M.lift_θ (fun _ -> x)
    member M.set_constraints x = M.lift_constraints (fun _ -> x)
    member M.set_scoped_vars x = M.lift_scoped_vars (fun _ -> x)

    member M.clear_constraints = M.set_constraints constraints.empty

    member private M.update_state =
        M {
            let! θ = M.get_θ
            do! M.lift_state (fun s ->
                { s with
                    γ = subst_kjenv θ.k s.γ
                    δ = subst_tenv θ s.δ
                    Γ = subst_jenv θ s.Γ
                    Q = subst_prefix θ s.Q
                    constraints = subst_constraints θ s.constraints })
        }

    // TODO: design a smart system for pruning substition automatically via gargabe collection.
    //       The basic implementation idea behind it is to use weak references: each object of type var carries a reference count, which implies that each type a given var 
    //       appears in increases the counter. Naturally, also substitutions carry objects of type var, but substitutions should count as weak references, in such a way
    //       that when a var is being referenced only from within a substitution, the substitution entry can be safely removed because we ensure no other type is referencing that var any longer.
    member M.update_θ θ1 =
        M {
            do! M.lift_θ (compose_tksubst θ1)
            do! M.update_state
            #if DEBUG_SUBST
            let! θ' = M.get_θ
            L.debug Normal "[S+] %O\n     = %O" θ1 θ'
            #endif
        }

    member internal __.lookup report (env : Env.t<_, _>) x =
        try env.lookup x
        with Env.UnboundSymbol x -> report loc x

    member M.search_scoped_var x =
        M {
            let! αs = M.get_scoped_vars
            return Set.toList αs |> List.tryFind (function Va (_, Some s) -> s = x | _ -> false)
        }

    member M.search_or_add_scoped_var x =
        M {
            let! o = M.search_scoped_var x
            match o with
            | Some α -> return α
            | None   -> let α = var.fresh_named x
                        do! M.lift_scoped_vars (Set.add α)
                        return α
        }

    member M.undo_scoped_vars f =
        M {
            let! Γ = M.get_scoped_vars
            let! r = f
            do! M.set_scoped_vars Γ
            return r
        }

    member M.updated (k : kind) =
        M {
            let! θ = M.get_θ
            return subst_kind θ.k k
        }

    member M.updated (kσ : kscheme) =
        M {
            let! θ = M.get_θ
            return subst_kscheme θ.k kσ
        }

    member M.updated (γ : kjenv) =
        M {
            let! θ = M.get_θ
            return subst_kjenv θ.k γ
        }

    member M.get_uni_context loc =
        M {
            let! Γ = M.get_Γ
            let! γ = M.get_γ
            let! αs = M.get_scoped_vars
            return { uni_context.Γ = Γ; γ = γ; loc = loc; scoped_vars = αs }
        }

    member M.undoable_bind lift x v =
        M {
            do! lift (fun (env : Env.t<_, _>) -> env.bind x v)
            return v, M { do! lift (fun (env : Env.t<_, _>) -> env.remove x) }
        }

    // bind for δ is here because it's used by type inference and type evaluation as well    
    member M.bind_δ x t =
        M {
            return! M.undoable_bind M.lift_δ x t
        }


// monad supertype for inference
//

type inference_builder (loc, ctx) =
    inherit basic_builder (loc)

    new (ctx) = new inference_builder (new location (), ctx)

    // this method abstracts the computation of ungeneralizable variables (both type and kind variables together)
    member M.get_ungeneralizable_vars =
        M {
            let! Γ = M.get_Γ            
            let! αs = M.get_scoped_vars
            return fv_Γ Γ + if ctx.is_top_level then Set.empty else αs
        }

    // bind methods for γ and δ are in this superclass because they are used by type inference, kind inference and type evaluation
    member M.bind_γ x (kσ : kscheme) =
        M {
            let! kσ = M.updated kσ
            return! M.undoable_bind M.lift_γ x kσ
        }
        
    member M.gen_and_bind_γ x (k : kind) =
        M {
            let! αs = M.get_ungeneralizable_vars
            let! γ = M.get_γ
            let! k = M.updated k
            let kσ = k.generalize γ αs
            assert (Set.intersect kσ.fv αs).IsEmpty
            return! M.bind_γ x kσ
        }


// specialized monad for type inference
//

type type_inference_builder (loc, ctx) =
    inherit inference_builder (loc, ctx)

    new (is_top_level) = new type_inference_builder (new location (), is_top_level)

    member M.Yield (ϕ : fxty) =
        M {
            let! ϕ' = M.updated ϕ
            return ϕ'
        }

    member M.Yield (t : ty) = M { yield Fx_F_Ty t }   
    member M.Yield ((x : ident, t : ty)) = M { let! t = M.updated t in return x, t }    // used for row types

    member M.updated (t : ty) =
        M {
            let! θ = M.get_θ
            return subst_ty θ t
        }


    // used by some HML rules inferring foralls where the type part have been substituted
    member M.Yield ((Q : prefix, t : ty)) =
        M {
            let! t = M.updated t
            let! θ = M.get_θ
            let! αs = M.get_ungeneralizable_vars
//            #if DEBUG_HML
//            let! Γ = M.get_Γ
//            let p set = sprintf "{ %s }" <| flatten_stringables ", " set
//            L.debug High "[yield-Q] S.dom = %O\n          Q.dom = %O\n          fv_gamma = %O\n          ungen = %O\n          t = %O" (p θ.dom) (p Q.dom) (p (fv_Γ Γ)) (p αs) t
//            #endif
            assert (Set.intersect Q.dom θ.dom).IsEmpty      // prefix and subst must involve different variables
            assert Q.dom.IsSubsetOf t.fv                    // generalizable vars must be present in t
            assert (Set.intersect Q.dom αs).IsEmpty         // generalizable vars must not be among ungeneralizable ones
            return Fx_ForallsQ (Q, Fx_F_Ty t)
        }

    // banged versions
    member M.YieldFrom f = M { let! (r : fxty) = f in yield r }

    // restrict current θ to fv in Γ
    member M.prune_θ =
        M {
            let! Γ = M.get_Γ
            do! M.lift_θ (fun θ -> let αs = fv_Γ Γ in { t = θ.t.restrict αs; k = θ.k.restrict αs })
        }

    member M.undo_Γ f =
        M {
            let! Γ = M.get_Γ
            let! r = f
            let! Γ = M.updated Γ        // it's important to apply the current substitution to the previously-saved env before setting it, or some changes will be lost
            do! M.set_Γ Γ
            return r
        }

    member M.updated (Γ : jenv) =
        M {
            let! θ = M.get_θ
            return subst_jenv θ Γ
        }

    member M.updated (ϕ : fxty) =
        M {
            let! θ = M.get_θ
            return subst_fxty θ ϕ
        }

    member M.updated (cs : constraints) =
        M {
            let! θ = M.get_θ
            return subst_constraints θ cs
        }

    member M.updated (σ : tscheme) =
        M {
            let! θ = M.get_θ
            return subst_scheme θ σ
        }

    member M.split_for_gen (Q0 : prefix) =
        M {
            let! αs = M.get_ungeneralizable_vars
            let! Q = M.get_Q
            let Q1, Q2 = Q.split (Q0.dom + αs)
            do! M.set_Q Q1
            return Q2
        }

    member M.extend (α, ϕ : fxty) =
        M {
            let! ϕ = M.updated ϕ
            let! Q = M.get_Q
            let Q, θ = Q.extend (α, ϕ)
            do! M.update_θ θ
            do! M.set_Q Q
        }

    member M.update_prefix_with_bound (Q : prefix) (α, ϕ : fxty) =
        M {
            let! ϕ = M.updated ϕ
            let Q, θ = Q.update_with_bound (α, ϕ)
            do! M.update_θ θ
            do! M.set_Q Q
        }

    member M.update_prefix_with_subst (Q : prefix) (α, t : ty) =
        M {
            let! t = M.updated t
            let Q, θ = Q.update_with_subst (α, t)
            do! M.update_θ θ
            do! M.set_Q Q
        }

    member M.search_binding_by_name_Γ x =
        M {
            let! Γ = M.get_Γ
            return Γ.search_by (fun jk { mode = jm } ->
                    match jk, jm with
                    | jenv_key.Var y, _
                    | jenv_key.Data y, _
                    | jenv_key.Inst (y, _), jenv_mode.Overload -> x = y      // TODO: this is not elegant: combinations may vary and this does not scale
                    | _ -> false)
        }

    member M.lookup_Γ jk =
        M {
            let! Γ = M.get_Γ
            return M.lookup Report.Error.unbound_symbol Γ jk
        }

    member M.bind_Γ jk ({ scheme = σ } as jv) =
        M {
            let! σ = M.updated σ
            return! M.undoable_bind M.lift_Γ jk jv
        }

    member M.bind_ungeneralized_var_Γ x t =
        M {
            return! M.bind_ungeneralized_Γ (jenv_key.Var x) jenv_mode.Normal t
        }

    member M.bind_generalized_var_Γ x ϕ =
        M {
            return! M.bind_generalized_Γ (jenv_key.Var x) jenv_mode.Normal ϕ
        }

    member M.bind_ungeneralized_Γ jk jm (t : ty) =
        M {
            return! M.bind_Γ jk { mode = jm; scheme = Ungeneralized t }
        }

    member M.bind_generalized_Γ jk jm (ϕ : fxty) =
        M {           
            let! αs = M.get_ungeneralizable_vars
            match ϕ with
            | FxU0_ForallsQ (Q, _) -> assert (Set.intersect Q.dom αs).IsEmpty   // no quantified vars must be ungeneralizable
            | FxU0_Bottom _        -> ()                                        // TODOL: is there something to check with kind vars?
            assert ϕ.fv.IsSubsetOf αs                                           // dual check: free vars must be among the ungeneralizable ones
            let! Q = M.get_Q
            for α in Set.intersect ϕ.fv αs do
                Report.Hint.scoped_tyvar_was_not_generalized loc α
            let! cs = M.get_constraints
            return! M.bind_Γ jk { mode = jm; scheme = { constraints = cs; fxty = ϕ } }
        }

    member M.auto_geneneralize (t : ty) =
        M {
            let! Γ = M.get_Γ
            return t.auto_generalize loc Γ
        }

    member M.extend_fresh_star =
        M {
            let α, tα = ty.fresh_star_var_and_ty
            do! M.extend (α, Fx_Bottom K_Star)
            return tα
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

    member M.instantiate_and_inherit_constraints (σ : tscheme) =
        M {            
            let σ = σ.instantiate
            do! M.add_constraints σ.constraints
            return σ
        }

    member M.undo_constraints f =
        M {
            let! π = M.get_constraints
            let! r = f
            do! M.set_constraints π
            return r
        }


// specialized monad for translation while inferring types
//

type translatable_type_inference_builder<'e> (e : node<'e, unit>, ctx) =
    inherit type_inference_builder (e.loc, ctx)
    member val current_node = e
    member __.translate
        //with get () = e.translated
        with set x = e.translated <- Translated x

    member __.already_translated
        with set x = e.translated <- x


// specialized monad for type evaluation
//

type type_eval_builder<'e> (τ : node<'e, kind>) =
    inherit basic_builder (τ.loc)

    member M.search_δ x =
        M {
            let! Δ = M.get_δ
            return Δ.search x
        }
   
    member M.undo_δ f =
        M {
            let! δ = M.get_δ
            let! r = f
            let! δ = M.updated δ
            do! M.set_δ δ
            return r
        }

    member M.updated (δ : tenv) =
        M {
            let! θ = M.get_θ
            return subst_tenv θ δ
        }


// specialized monad kind inference
//

// yield decorates node
type kind_inference_builder<'e> (τ : node<'e, kind>, ctx) =
    inherit inference_builder (τ.loc, ctx)

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

    member M.bind_γα x (k : kind) =
        M {
            let! k = M.updated k
            return! M.undoable_bind M.lift_γα x k
        }

    member M.search_γα x =
        M {
            let! γα = M.get_γα
            return γα.search x
        }
        
    member M.lookup_γ x =
        M {
            let! γ = M.get_γ
            return M.lookup Report.Error.unbound_type_constructor γ x
        }

    member M.undo_γ f =
        M {
            let! γ = M.get_γ
            let! r = f
            let! γ = M.updated γ
            do! M.set_γ γ
            return r
        }

    // environment γα does not have a full undo but only this one, because scoping of vars is special: vars can be introduced anytime and do not have to be undone
    member M.undone_bind_γα x v f =
        M {
            let! _, undo = M.bind_γα x v
            let! r = f
            do! undo
            yield r
        }


        