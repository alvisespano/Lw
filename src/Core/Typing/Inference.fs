(*
 * Lw
 * Typing/Inference.fs: principal type inference algortihms
 * (C) 2014-2016 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module Lw.Core.Typing.Inference

#nowarn "49"

open System
open System.Text.RegularExpressions
open System.Diagnostics
open FSharp.Common.Log
open FSharp.Common
open Lw.Core
open Lw.Core.Absyn
open Lw.Core.Absyn.Misc
open Lw.Core.Absyn.Var
open Lw.Core.Absyn.Kind
open Lw.Core.Absyn.Sugar
open Lw.Core.Absyn.Ast
open Lw.Core.Globals
open Lw.Core.Typing.Defs
open Lw.Core.Typing.StateMonad
open Lw.Core.Typing.Unify
open Lw.Core.Typing.Resolve
open Lw.Core.Typing.Ops
open Lw.Core.Typing.Meta
open Lw.Core.Typing.Equivalence


type translatable_type_inference_builder<'e> with
    member M.W_desugared f (e' : node<_>) =
        M {
            L.debug Low "[DESUGAR] %O ~~> %O" M.current_node e'
            let! t = f e'
            M.translate <- match e'.translated with Translated u -> u
            return t
        }

type [< NoComparison; NoEquality >] gen_binding = {
    qual   : decl_qual
    expr        : expr
    id          : ident
    constraints : constraints
    inferred    : fxty
    to_bind     : fxty
}


// type inference bits
//

let W_lit = function
    | lit.Int _       -> T_Int
    | lit.Float _     -> T_Float
    | lit.String _    -> T_String
    | lit.Bool _      -> T_Bool
    | lit.Char _      -> T_Char
    | lit.Unit        -> T_Unit

let auto_jk decl_qual x (ϕ : fxty) = if decl_qual.over then jenv_key.Inst (x, ϕ.pretty.GetHashCode ()) else jenv_key.Var x

let gen_bind ctx prefixes ({ id = x; qual = dq; expr = e0; to_bind = ϕ } as gb) =
    let M = new translatable_type_inference_builder<_> (e0, ctx)
    let loc0 = e0.loc
    let Lo0 x = Lo loc0 x
    M {
        // check shadowing and interaction with previous bindings
        let! jb = M.search_binding_by_name_Γ x
        if dq.over then
            match jb with                
            | Jb_Overload pt -> let! uctx = M.get_uni_context loc0
                                if not (ϕ.is_instance_of uctx pt) then Report.Error.instance_not_valid loc0 x ϕ pt   // open-world overloadable instance
            | Jb_Unbound     -> Report.Warn.let_over_without_previous_let loc0 x                                                     // let-over binding without a previous let-non-over is a warning
            | _              -> ()                                                                                                  // let-over binding after anything else is valid closed-world overloading
        else
            match jb with                
            | Jb_Overload _ -> Report.Warn.shadowing_overloaded_symbol loc0 x    // let-non-over after overload
            | _             -> ()                                               // normal binding that can shadow legally

        // check constraints solvability and scope escaping
        let! cs = M.get_constraints
        for { name = cx; ty = ct } as c in cs do
            let αs = ct.fv - ϕ.fv in if not αs.IsEmpty then Report.Hint.unsolvable_constraint loc0 x ϕ cx ct αs
            match c.mode with
            | Cm_OpenWorldOverload ->
                let! jb = M.search_binding_by_name_Γ cx
                match jb with
                | Jb_Overload _ -> ()
                | _ ->
                    Report.Warn.constraint_escaped_scope_of_overload loc0 cx ct x ϕ
                    do! M.remove_constraint c
                    do! M.add_constraint { c with mode = Cm_FreeVar; ty = ct }              // escaped overload constraint becomes a FreeVar constraint

            | Cm_ClosedWorldOverload ->
                Report.Error.closed_world_overload_constraint_not_resolved loc0 cx ct x ϕ    // closed-world overload constraint not resolved

            | _ -> ()

        // generalization and binding
        let jk = auto_jk dq x gb.to_bind
        let! _ =
            let jm = if dq.over then jenv_mode.Overload else jenv_mode.Normal
            in
                M.bind_generalized_Γ jk jm gb.to_bind
        Report.prompt ctx (prefixes @ dq.as_tokens) x gb.to_bind (Some (Config.Printing.ftype_instance_of_fxty_sep, gb.inferred))

        // translation
        let e1 = if cs.is_empty then e0 else LambdaCurriedArgs ([possibly_tuple Lo0 P_CId P_Tuple cs], Lo0 e0.value)
        return jk, e1
    }


// deal with annotations
//

let W_fxty_annot ctx loc (ϕann : fxty) (ϕinf : fxty) =
    let M = new type_inference_builder (loc, ctx)
    M {
        let! ϕ = M {
            match ϕann.maybe_ftype with
            | Some tann ->
                match ϕinf.maybe_ftype with
                | Some tinf ->
                    do! M.unify loc tann tinf
                    yield tinf                          // return the inferred F-type when the annotation is an F-type
                | None      -> 
                    do! M.subsume loc tann ϕinf
                    Report.Hint.type_annotation_is_instantiation loc tann ϕinf
                    yield tann
            | None ->
                yield! M.unify_fx loc ϕann ϕinf     // return the flex unification result when annotation is a flex type instead
        }
        return ϕ
    }

let W_fxty_expr_annot ctx (τ : fxty_expr) (ϕinf : fxty) =
    let loc = τ.loc
    let M = new type_inference_builder (loc, ctx)
    M {
        let! ϕann, k = Wk_and_eval_fxty_expr ctx τ
        do! M.kunify loc K_Star k
        return! W_fxty_annot ctx τ.loc ϕann ϕinf
    }

let W_fxty_expr_annot_in_binding ctx (τ : fxty_expr) (ϕinf : fxty) =
    let loc = τ.loc
    let M = new type_inference_builder (loc, ctx)
    M {
        let! ϕann, k = Wk_and_eval_fxty_expr ctx τ
        do! M.kunify loc K_Star k
        let! ϕann = M {
            match ϕann.maybe_ftype with
            | Some tann ->
                let! tann' = M.auto_geneneralize tann
                if not (tann.is_equivalent tann') then Report.Hint.auto_generalization_occurred_in_annotation loc tann tann'
                return (Fx_F_Ty tann')
            | None ->
                return ϕann
        }
        return! W_fxty_annot ctx loc ϕann ϕinf
    }


let check_rec_value_restriction ctx loc (t : ty) =
    let M = new type_inference_builder (loc, ctx)
    M {
        match t with
        | T_Foralls0 (_, T_Arrow _) -> ()
        | _ -> Report.Error.value_restriction_non_arrow_in_letrec loc t
    }


// main inference function recursive wrappers
//

let rec W_expr (ctx : context) (e0 : expr) =
    let M = new translatable_type_inference_builder<_> (e0, ctx)
    M {
        L.tabulate 2
        try
            let rule =
                match e0.value with
                | Var _     -> "(VAR)"
                | Lambda _  -> "(ABS)"
                | App _     -> "(APP)"
                | Let _     -> "(LET)"
                | _         -> "[e]  "
            let! Q = M.get_Q
            let! θ = M.get_θ
            let! cs = M.get_constraints
            #if DEBUG_BEFORE_INFERENCE
            L.debug Min "%s %O\n[C]   %O\n[Q]   %O" rule e0 cs Q
            #endif
            let! (ϕ : fxty) = W_expr' ctx e0
            do! resolve_constraints ctx e0
            // TODOH: insert automatic generalization here, beside automatic resolution
            #if DEBUG_INFERENCE
            let! Q' = M.get_Q
            let! cs' = M.get_constraints
            // TODOL: create a logger.prefix(str) method returning a new logger object which prefixes string str for each line (and deals with EOLs padding correctly)
            #if DEBUG_SUBST
            let! θ' = M.get_θ
            L.debug Low "%s %O\n[:t]  %O\n[F-t] %O\n[e*]  %O\n[C]   %O\n[Q]   %O\n[S]   %O\n[C']  %O\n[Q']  %O\n[S']  %O" rule e0 ϕ ϕ.ftype e0.translated cs Q θ cs' Q' θ'
            #else
            L.debug Low "%s %O\n[:t]  %O\n[F-t] %O\n[e*]  %O\n[C]   %O\n[Q]   %O\n[C']  %O\n[Q']  %O\n" rule e0 ϕ ϕ.ftype e0.translated cs Q cs' Q'
            #endif
            #endif
            return ϕ
        finally
            L.undo_tabulate
    } 

and W_decl ctx d =
    let M = new translatable_type_inference_builder<_> (d, ctx)
    M {
        L.debug Low "[decl] %O" d
        if ctx.is_top_level then
            // when it's a top level binding
            #if DEBUG
            use N = var.reset_normalization
            #endif
            do! M.undo_scoped_vars <| M {
                do! W_decl' ctx d   
            }
            do! M.prune_θ
        else
            // when it's an inner binding
            do! W_decl' ctx d
    }  

and W_patt ctx (p0 : patt) =
    let M = new type_inference_builder (p0.loc, ctx)
    M {
        L.tabulate 2
        try
            let rule =
                sprintf "%-9s" <|
                match p0.value with
                | P_Var _     -> "(P-VAR) "
                | P_Cons _    -> "(P-CONS)"
                | P_App _     -> "(P-APP) "
                | _           -> "[P]     "
            let! Q = M.get_Q
            let! θ = M.get_θ
            #if DEBUG_BEFORE_INFERENCE
            L.debug Min "%s %O\n[Q]   %O" rule p0 Q
            #endif
            let! (ϕ : fxty) = W_patt' ctx p0
            // TODOH: insert automatic generalization here, besides automatic resolution
            #if DEBUG_INFERENCE
            let! Q' = M.get_Q
            // TODOL: create a logger.prefix(str) method returning a new logger object which prefixes string str for each line (and deals with EOLs padding correctly)
            #if DEBUG_SUBST
            let! θ' = M.get_θ
            L.debug Low "%s %O\n[:t]  %O\n[F-t] %O\n[e*]  %O\n[Q]   %O\n[S]   %O\n[Q']  %O\n[S']  %O" rule p0 ϕ ϕ.ftype p0.translated Q θ Q' θ'
            #else
            L.debug Low "%s %O\n[:t]  %O\n[F-t] %O\n[e*]  %O\n[Q]   %O\n[Q']  %O" rule p0 ϕ ϕ.ftype p0.translated Q Q'
            #endif
            #endif
            return ϕ
        finally
            L.undo_tabulate
    }

and W_patt_F ctx (p0 : patt) =
    let M = new type_inference_builder (p0.loc, ctx)
    M {
        let! ϕ = W_patt ctx p0
        return ϕ.ftype
    }


and W_expr_F ctx e0 =
    let M = new translatable_type_inference_builder< _> (e0, ctx)
    M {
        let! ϕ = W_expr ctx e0
        return ϕ.ftype
    }


// main inference functions
//

and W_expr' ctx (e0 : expr) =
    let Lo x = Lo e0.loc x
    let M = new translatable_type_inference_builder< _> (e0, ctx)
    let W_desugared_expr = M.W_desugared (W_expr ctx)
    M {
        match e0.value with
        | Lit lit ->
            yield W_lit lit

        | Record (bs, eo) ->
            let! bs = M.List.map (fun (x : ident, e) -> M { let! t = W_expr_F ctx e in yield x, t }) bs
            match eo with
            | None ->
                yield T_Closed_Record bs

            | Some e ->
                let! ϕ = W_expr ctx e
                let ρ = var.fresh
                do! M.unify e.loc (T_Record ([], Some ρ)) ϕ.ftype
                yield T_Record (bs, Some ρ)

        | Var x ->
            let! jv = M.search_binding_by_name_Γ x
            match jv with
            | Jb_Overload t ->
                let c = constraintt.fresh_strict Cm_OpenWorldOverload x t
                do! M.add_constraint c
                M.translate <- E_CId c
                yield t

            | Jb_OverVar ->
                let α = ty.fresh_star_var
                let c = constraintt.fresh_strict Cm_ClosedWorldOverload x α
                do! M.add_constraint c
                M.translate <- E_CId c
                yield α

            | Jb_Var σ ->
                let! { constraints = cs; fxty = ϕ } = M.instantiate_and_inherit_constraints σ
                if cs.is_empty then yield ϕ
                else
                    let e1 = Id x
                    let e2 = possibly_tuple Lo E_CId Tuple cs
                    M.translate <- App (Lo e1, e2)
                    yield ϕ

            | Jb_Data σ ->
                let! { fxty = ϕ } = M.instantiate_and_inherit_constraints σ
//                M.translate <- Reserved_Cons x
                yield ϕ
                
            | Jb_Unbound ->
                return Report.Error.unbound_symbol e0.loc x

        | FreeVar x ->
            let! jb = M.search_binding_by_name_Γ x
            let ot =
                // TODO: verify the behaviour of free vars in conjunction with the following cases
                match jb with
                | Jb_Overload t -> Some t
                | Jb_OverVar    
                | Jb_Unbound    -> None
                | Jb_Data σ   
                | Jb_Var σ      -> Report.Warn.freevar_shadowing e0.loc x σ; None
            let t = either ty.fresh_star_var ot
            do! M.add_constraint (constraintt.fresh_strict Cm_FreeVar x t)
            yield t

        | PolyCons x ->
            let α = ty.fresh_star_var
            let β = ty.fresh_star_var
            yield T_Open_Variant [x, T_Arrow (α, β)]

        | Lambda ((x, τo), e) ->
            let! Q0 = M.get_Q
            let! tx = M {
                match τo with
                | None -> return ty.fresh_star_var
                | Some τ ->
                    let! ϕ, k = Wk_and_eval_fxty_expr ctx τ
                    match ϕ.maybe_ftype with
                    | None   -> return Report.Error.annotated_lambda_parameter_is_flex τ.loc x ϕ
                    | Some t -> do! M.kunify τ.loc K_Star k
                                return t
            }
            // annotated or not, all free vars are added to the prefix
            for α in tx.ftv do
                do! M.extend (α, Fx_Bottom K_Star)
            let! ϕ1 = M.undo_Γ <| M {
                let! _ = M.bind_ungeneralized_var_Γ x tx
                return! W_expr ctx e
            }            
            let! tx = M.updated tx
            // check that the inferred type of parameter is a monotype when no annotation was provided
            if τo.IsNone && not tx.is_monomorphic then Report.Error.inferred_lambda_parameter_is_not_monomorphic e0.loc x tx
            let β, tβ = ty.fresh_star_var_and_ty
            #if ENABLE_HML_OPTS
            do! M.extend (β, ϕ1)
            let! Q3' = M.split_for_gen Q0      // HACK: this code should have the same behaviour as the original shown in HML paper, but is shorter
            #else
            let! Q3 = M.split_for_gen Q0
            let Q3', θ3' = Q3.extend (β, ϕ1)
            do! M.update_θ θ3'
            #endif
            yield Q3', T_Arrow (tx, tβ)

        | App (e1, e2) -> 
            let! Q0 = M.get_Q
            let! ϕ1 = W_expr ctx e1
            let! ϕ2 = W_expr ctx e2
            let α1, tα1 = ty.fresh_star_var_and_ty
            let α2, tα2 = ty.fresh_star_var_and_ty
            let β, tβ = ty.fresh_star_var_and_ty
            do! M.extend (α1, ϕ1)
            do! M.extend (α2, ϕ2)
            do! M.extend (β, Fx_Bottom K_Star)
            do! M.unify e1.loc (T_Arrow (tα2, tβ)) tα1
            let! Q5 = M.split_for_gen Q0
            yield Q5, tβ
           
        | Tuple ([] | [_]) as e ->
            return unexpected "empty or unary tuple: %O" __SOURCE_FILE__ __LINE__ e

        | Tuple es ->
            let! ts = M.List.map (W_expr_F ctx) es
            yield T_Tuple ts

        | If (e1, e2, e3) ->
            // TODOL: desugar to match with booleans?
            let! t1 = W_expr_F ctx e1
            do! M.unify e1.loc T_Bool t1
            let! t2 = W_expr_F ctx e2
            let! t3 = W_expr_F ctx e3
            do! M.unify e3.loc t2 t3
            yield t2

        | Let (d, e) ->
            yield! M.undo_Γ <| M {
                do! W_decl { ctx with is_top_level = false } d
                yield! W_expr ctx e
            }
        
        | Match (_, []) ->
            return unexpected "empty case list in match expression" __SOURCE_FILE__ __LINE__ 
             
        // TODO: why don't we try to use flex types here and unify schemes instead? does it make sense?
        | Match (e1, cases) ->
            let! ϕe1 = W_expr ctx e1
            let! tr = M.extend_fresh_star
            let! (_, ϕr) =
                M.List.fold (fun (ϕe1, ϕr) (p, ewo, e) -> M {
                    let! ϕp = W_patt ctx p
                    let! ϕe1 = M.unify_fx p.loc ϕe1 ϕp
                    match ewo with
                    | None    -> return ()
                    | Some ew -> let! tew = W_expr_F ctx ew
                                 do! M.unify ew.loc T_Bool tew
                    let! ϕe = W_expr ctx e
                    let! ϕr = M.unify_fx e.loc ϕr ϕe
                    return ϕe1, ϕr
                }) (ϕe1, Fx_F_Ty tr) cases
            yield ϕr
        
        | Annot (e, τ) ->
            let! ϕe = W_expr ctx e
            yield! W_fxty_expr_annot ctx τ ϕe
//            let x = fresh_reserved_id ()
//            let! ϕ = W_desugared_expr (Lo <| App (Lo <| Lambda ((x, Some τ), Lo <| Var x), e))  // TODO: or maybe just use unification of flex types?
//            M.already_translated <- e.translated
//            yield ϕ

        | Combine es ->
            assert (es.Length > 1)
            let es, e =
                let rec R = function
                    | []       -> unexpected_case __SOURCE_FILE__ __LINE__ []
                    | [e]      -> [], e
                    | e1 :: es -> let l, e = R es in e1 :: l, e
                in
                    R es
            for ei in es do
                let! ti = W_expr_F ctx ei
                try do! M.unify ei.loc T_Unit ti
                with :? Report.type_error as e -> Report.Warn.expected_unit_statement ei.loc ti
            yield! W_expr ctx e

        | Select (e, x) ->
            let! te = W_expr_F ctx e
            let α = ty.fresh_star_var
            let t = T_Open_Record [x, α]
            do! M.unify e.loc t te
            yield α
            
        | Restrict (e, x) ->
            let! te = W_expr_F ctx e
            let α = ty.fresh_star_var
            let ρ = var.fresh
            do! M.unify e.loc (T_Record ([x, α], Some ρ)) te
            yield T_Record ([], Some ρ)

        | Loosen e ->
            let! cs0 = M.get_constraints
            let! t = W_expr ctx e
            let! cs1 = M.get_constraints
            let cs = cs1 - cs0
            if cs.is_empty then Report.Warn.no_constraints_to_loosen e.loc
            for c in cs do
                do! M.remove_constraint c
                do! M.add_constraint { c with strict = false }
            yield t

        | Val e ->
            let! t = W_expr { ctx with resolution = Res_Loose } e
            let! cs = M.get_constraints
            if not cs.is_empty then return Report.Error.value_not_resolved e0.loc cs
            yield t

        | Inject e ->
            let! cs = M.undo_constraints <| M {
                do! M.clear_constraints
                let! _ = W_expr ctx e
                return! M.get_constraints
            }
            let x = fresh_reserved_id ()
            if cs.is_empty then Report.Warn.no_constraints_to_abstract e.loc
            let e1 =
                let bs = [ for c in cs -> let xi = c.name in { qual = decl_qual.none; patt = Lo <| P_Var xi; expr = Lo <| Select (Lo <| Id x, xi) } ]
                in
                    Let (Lo <| D_Bind bs, e)
            yield! W_desugared_expr (Lo <| Lambda ((x, None), Lo e1))

        | Eject e ->
            let! t = W_expr_F ctx e
            let α = ty.fresh_star_var
            let tr = T_Open_Record []
            do! M.unify e.loc (T_Arrow (tr, α)) t   // TODO: probably this is not working in HML and something like the (APP) rule must be used
            match tr with
            | T_Record (xts, _) ->
                for x, t in xts do
                    // TODOL: think about a syntax for expressing constraint mode and strictness
                    do! M.add_constraint (constraintt.fresh_strict Cm_OpenWorldOverload x t)
            | _ -> unexpected_case __SOURCE_FILE__ __LINE__ tr
            let! cs = M.get_constraints
            let x = fresh_reserved_id ()
            let e1 = Record ([ for { name = y } in cs -> y, Lo <| Id y ], None)
            let e2 = App (e, Lo <| Id x)
            yield! W_desugared_expr (Lo <| Let (Lo <| D_Bind [{ qual = decl_qual.none; patt = Lo <| P_Var x; expr = Lo e1 }], Lo e2))    // TODO: infer the type of the desugared expression?

        | Solve (e, τ) ->
            let! te = W_expr_F ctx e
            let! t, _ = Wk_and_eval_ty_expr ctx τ
            do! M.unify e.loc (T_Open_Record []) t
            let xts =
                match t with
                | T_Record (xts, _) -> xts
                | _                 -> unexpected_case __SOURCE_FILE__ __LINE__ t
            // check that all label types unify with principal types in case of overloaded symbols and whether symbols refer to multiple constraints
            do! M.List.iter (fun (x, t) -> M {
                    let! o = M.search_binding_by_name_Γ x
                    match o with
                    | Jb_Overload t' -> try do! M.unify τ.loc t t'
                                        with _ -> Report.Warn.manually_resolved_symbol_does_respect_overload e.loc x t t'
                    | Jb_Unbound     -> Report.Warn.manually_resolved_symbol_does_not_exist e.loc x t
                    | _              -> ()
                }) xts
                                
            // unify user-defined types to constraints in order of appearence
            for x, t in xts do
                let! cs = M.get_constraints
                for c in cs do
                    if c.name = x then
                        do! M.attempt_unify e.loc c.ty t
            M.translate <- e.value
            yield te

    }
    

and W_decl' (ctx : context) (d0 : decl) =
    let M = new translatable_type_inference_builder<_> (d0, ctx)
    let desugar = M.W_desugared (W_decl ctx) 
    let (|B_Unannot|B_Annot|B_Patt|) = function
        | ULo (P_Var x)                    -> B_Unannot x
        | ULo (P_Annot (ULo (P_Var x), τ)) -> B_Annot (x, τ)
        | p                                -> B_Patt p
    
    M {
        match d0.value with
        | D_Overload []
        | D_Bind []
        | D_RecBind []
        | D_Reserved_Multi [] ->
            return unexpected "empty declaration list" __SOURCE_FILE__ __LINE__

        | D_Overload l ->
            for { id = x; signature = τ } in l do
                let! t, k = Wk_and_eval_ty_expr ctx τ
                do! M.kunify τ.loc K_Star k
                let! _ = M.bind_Γ (jenv_key.Var x) { mode = jenv_mode.Overload; scheme = Ungeneralized t }
                Report.prompt ctx Config.Printing.Prompt.overload_decl_prefixes x t None

        | D_Bind bs ->
            do! M.undo_constraints <| M {
                // infer type for each binding in the let..and block
                let! l = M.List.collect (fun ({ patt = p; expr = e } as b) -> M {
                            do! M.clear_constraints     // TODOH: probably there's a relation between constraints to keep and the free vars in Γ
                            let! ϕe = W_expr ctx e
                            return! M.undo_Γ <| M {
                                // TODOL: support return type annotations after parameters like in "let f x y : int = ..."
                                match p with
                                | B_Unannot x ->
                                    do! resolve_constraints ctx e
                                    let! cs = M.get_constraints
                                    return [{ expr = b.expr; qual = b.qual; id = x; constraints = cs; to_bind = ϕe; inferred = ϕe }]     // by default bind the inferred type as a flex type

                                | B_Annot (x, τ) ->
                                    let! ϕe' = W_fxty_expr_annot_in_binding ctx τ ϕe
                                    do! resolve_constraints ctx e
                                    let! cs = M.get_constraints
                                    return [{ expr = b.expr; qual = b.qual; id = x; constraints = cs; to_bind = ϕe'; inferred = ϕe }]

                                | B_Patt p ->
                                    let! tp = W_patt_F ctx p
                                    do! M.unify e.loc tp ϕe.ftype                 // HACK: pattern-based let-bindings needs to be written in terms of (LAMBDA) and (APP) rules
                                    do! resolve_constraints ctx e
                                    let! cs = M.get_constraints
                                    return! vars_in_patt p |> Set.toList |> M.List.map (fun x -> M {
                                            let! { scheme = σ } = M.lookup_Γ (jenv_key.Var x) 
                                            return { expr = b.expr; qual = b.qual; id = x; constraints = cs; to_bind = σ.fxty; inferred = ϕe }
                                        })
                            }
                        }) bs
                let! bs' = M.List.map (fun gb -> M { let! () = M.set_constraints gb.constraints in return! gen_bind ctx Config.Printing.Prompt.value_decl_prefixes gb }) l
                M.translate <- D_Bind [for jk, e in bs' -> { qual = decl_qual.none; patt = Lo e.loc (P_Jk jk); expr = e }]
            }

        | D_RecBind bs ->
            do! M.undo_constraints <| M {
                let! Q0 = M.get_Q
                let! l = M.undo_Γ <| M {
                    do! M.clear_constraints
                    // introduce fresh type variables or the annotated type for each rec binding
                    let! l = M.List.map (fun ({ patt = p } as b) -> M {
                                let x, τo =
                                    match p with
                                    | B_Unannot x       -> x, None
                                    | B_Annot (x, τ)    -> x, Some τ
                                    | B_Patt _          -> Report.Error.illegal_letrec_binding p.loc 
                                let! tx = M {
                                    match τo with
                                    | None -> return ty.fresh_star_var
                                    | Some τ -> 
                                        let! t, k = Wk_and_eval_ty_expr ctx τ   // UNDONE: generalize annotations over fxty and define a shortcut for when F-types are expected
                                        do! M.kunify τ.loc K_Star k
                                        return t
                                }
                                for α in tx.fv do
                                    do! M.extend (α, Fx_Bottom K_Star)
                                let! _ = M.bind_ungeneralized_var_Γ x tx
                                return b, x, τo, tx
                            }) bs
                    // infer each rec binding and behave as if they were (LAMBDA) parameters
                    for { expr = e }, x, τo, tx in l do                        
                        let! ϕe = W_expr ctx e
                        let β, tβ = ty.fresh_star_var_and_ty
                        do! M.extend (β, ϕe)
                        do! M.unify e.loc tx tβ
                        let! tx = M.updated tx
                        if τo.IsNone && not tx.is_monomorphic then Report.Error.inferred_rec_definition_is_not_monomorphic e.loc x tx
                        do! check_rec_value_restriction ctx e.loc tx
                    return l
                }
                // rebind all rec bindings with proper generalization
                let! Q = M.split_for_gen Q0
                let! cs = M.get_constraints
                let! bs' = l |> M.List.map (fun (b, x, _ , tx) -> M {
                                let! ϕx = M { yield Q, tx } // same prefix for each rec binding, but normal form will clean up useless quantifications
                                let ϕ = ϕx.nf
                                return! gen_bind ctx Config.Printing.Prompt.rec_value_decl_prefixes { expr = b.expr; qual = b.qual; id = x; constraints = cs; inferred = ϕ; to_bind = ϕ }
                            })
                M.translate <- D_RecBind [for jk, e in bs' -> { qual = decl_qual.none; patt = B_Unannot jk.pretty; expr = e }]
            }

        | D_Open (q, e) ->
            let! t = W_expr_F ctx e
            do! M.unify e.loc (T_Open_Record []) t    // HACK: probably not working in HML
            let Lo x = Lo e.loc x
            match t with
            | T_Record (bs, _) ->
                let rec_id = fresh_reserved_id ()
                let sel x = Select (Lo (Id rec_id), x)
                let d1 = D_Bind [{ qual = decl_qual.none; patt = Lo (P_Var rec_id); expr = e }]
                let d2 = D_Bind [ for x, _ in bs -> { qual = q; patt = Lo (P_Var x); expr = Lo (sel x) } ]
                do! desugar (Lo <| D_Reserved_Multi [Lo d1; Lo d2])
                        
            | _ -> return unexpected "non-record type: %O" __SOURCE_FILE__ __LINE__ t

        | D_Reserved_Multi ds ->
            for d in ds do
                do! W_decl ctx d

        | D_Type bs ->
            let d = Lo d0.loc <| Td_RecBind bs
            do! Wk_and_eval_ty_rec_bindings ctx d bs

        // TODO: support the alternate datatype declaration syntax, for example:
        //          datatype list 'a = Nil | Cons of 'a * 'a list
        //       and even mixed syntaxes, such as:
        //          datatype list 'a = Nil | Cons : 'a -> 'a list -> 'a list
        //       finally support also let-datatype and further let-data declarations, e.g.:
        //          datatype list : * -> *
        //          data Nil : list 'a
        //          data Cons : 'a -> list 'a -> list 'a
        | D_Datatype { id = c; kind = kc; dataconss = bs } ->
            let! kσ, _ = M.gen_and_bind_γ c kc
            let! _ = M.bind_δ c (T_Cons (c, kc))
            Report.prompt ctx Config.Printing.Prompt.datatype_decl_prefixes c kσ None
            for { id = x; signature = τx } in bs do
                // the whole inferred kind must be star
                let! tx, kx = Wk_and_eval_ty_expr ctx τx      // TODO: support flex types for data constructors
                let! tx = M.auto_geneneralize tx
                do! M.kunify τx.loc K_Star kx                              
                // each data constructor's return type must be equal to the type constructor being defined; arguments are not checked to be variables, so it means GADTs can be defined
                let txcod = tx.return_ty
                match txcod with
                | T_ConsApps1 ((x', _), _) when x' = c -> ()    
                | _                                    -> Report.Error.data_constructor_codomain_invalid τx.loc x c txcod
                // check there are no Γ-free vars in the signature
                if not tx.fv.IsEmpty then Report.Hint.datacons_contains_env_fv τx.loc c x tx
                let! σ, _ = M.bind_generalized_Γ (jenv_key.Data x) jenv_mode.Normal (Fx_F_Ty tx)
                Report.prompt ctx Config.Printing.Prompt.data_decl_prefixes x σ.scheme None

        // TODOL: implement kind aliases
        | D_Kind _ ->
            return not_implemented "%O" __SOURCE_FILE__ __LINE__ d0
    }  



and W_patt' ctx (p0 : patt) : M<fxty> =
    let M = new type_inference_builder (p0.loc, ctx)
    let loc0 = p0.loc
    let Lo0 = Lo loc0
    M {
        match p0.value with
        | P_Cons x ->
            let! o = M.search_binding_by_name_Γ x
            match o with
                | Jb_Unbound ->
                    return Report.Error.unbound_data_constructor loc0 x
                    
                | Jb_Data σ ->
                    let! σ = M.instantiate_and_inherit_constraints σ
                    yield σ.fxty

                | Jb_Overload t ->
                    return Report.Error.data_constructor_bound_to_wrong_symbol loc0 "open-world overloaded symbol" x t

                | Jb_Var σ ->
                    return Report.Error.data_constructor_bound_to_wrong_symbol loc0 "variable" x σ

                | Jb_OverVar ->
                    return Report.Error.data_constructor_bound_to_wrong_symbol loc0 "closed-world overloaded symbol" x null

        | P_PolyCons x ->
            let α = ty.fresh_star_var
            let β = ty.fresh_star_var
            yield T_Open_Variant [x, T_Arrow (α, β)]

        | P_Var x ->
            let! tα = M.extend_fresh_star
            let! _ = M.bind_ungeneralized_var_Γ x tα
            yield tα

        | P_As (p, x) ->
            yield! W_patt ctx (Lo0 <| P_And (p, Lo0 (P_Var x)))

        | P_Wildcard ->
            yield! W_patt ctx (Lo0 <| P_Var (fresh_reserved_id ()))

        | P_Annot (p, τ) ->
            let! ϕp = W_patt ctx p
            yield! W_fxty_expr_annot ctx τ ϕp

        | P_Lit lit ->
            yield W_lit lit

        | P_Tuple ([] | [_]) as p ->
            return unexpected "empty or unary tuple in pattern: %O" __SOURCE_FILE__ __LINE__ p

        | P_Tuple ps ->
            let! ts = M.List.map (W_patt_F ctx) ps
            yield T_Tuple ts

        | P_Record xps ->
            let! xts = M.List.map (fun (x : ident, p) -> M { let! t = W_patt_F ctx p in return x, t }) xps
            yield T_Open_Record xts

        | P_Or (p1, p2) ->
            let xs1 = vars_in_patt p1
            let xs2 = vars_in_patt p2
            let set = (xs1 + xs2) - Set.intersect xs1 xs2
            if not (Set.isEmpty set) then Report.Error.different_vars_in_sides_of_or_pattern loc0 set
            let! t1 = W_patt_F ctx p1
            let! t2 = W_patt_F ctx p2
            do! M.unify p2.loc t1 t2
            yield t1

        | P_And (p1, p2) ->
            let xs1 = vars_in_patt p1
            let xs2 = vars_in_patt p2
            let set = Set.intersect xs1 xs2
            if not (Set.isEmpty set) then Report.Error.same_vars_in_sides_of_or_pattern loc0 set
            let! t1 = W_patt_F ctx p1
            let! t2 = W_patt_F ctx p2
            do! M.unify p2.loc t1 t2
            yield t1

        // TODO: rewrite (P-APP) using a W_like_app function which is reused also by (APP)
        | P_App (p1, p2) & P_ConsApps1 _ ->
            let! Q0 = M.get_Q
            let! ϕ1 = W_patt ctx p1
            let! ϕ2 = W_patt ctx p2
            let α1, tα1 = ty.fresh_star_var_and_ty
            let α2, tα2 = ty.fresh_star_var_and_ty
            let β, tβ = ty.fresh_star_var_and_ty
            do! M.extend (α1, ϕ1)
            do! M.extend (α2, ϕ2)
            do! M.extend (β, Fx_Bottom K_Star)
            do! M.unify p1.loc (T_Arrow (tα2, tβ)) tα1
            let! Q5 = M.split_for_gen Q0
            yield Q5, tβ
        | P_App _ -> return Report.Error.invalid_pattern_application loc0 p0
    }


and W_program (prg : program) =
    let ctx = context.as_top_level_decl
    let M = new type_inference_builder (ctx)
    M {
        for d in prg.decls do
            do! W_decl ctx d
        match prg.main with
        | None -> ()
        | Some e ->
            let! t = W_expr_F ctx (Lo e.loc <| Val e)
            do! M.unify e.loc T_Int t
    }
