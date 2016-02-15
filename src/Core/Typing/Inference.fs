(*
 * Lw
 * Typing/Inference.fs: principal type inference algortihms
 * (C) 2000-2016 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module Lw.Core.Typing.Inference

#nowarn "49"

open System
open System.Text.RegularExpressions
open System.Diagnostics
open FSharp.Common.Prelude
open FSharp.Common.Log
open FSharp.Common
open Lw.Core
open Lw.Core.Absyn
open Lw.Core.Globals
open Lw.Core.Typing.Defs
open Lw.Core.Typing.StateMonad
open Lw.Core.Typing.Unify
open Lw.Core.Typing.Resolve
open Lw.Core.Typing.Ops
open Lw.Core.Typing.Meta


let desugar (M : translatable_type_inference_builder<_>) f (e0 : node<_, _>) (e : node<_, _>) =
    M {
        L.debug Low "[DESUGAR] %O ~~> %O" e0 e
        let! t = f e
        M.translated <- e.value
        return t
    }

// special Yield for generalization

type [< NoComparison; NoEquality >] gen_binding<'n> = {
    b  : 'n
    x  : id
    cs : constraints
    ϕ  : fxty
}

//type type_inference_builder with
//    member M.Yield l =
//        M {
//            return! M.List.map (fun gb -> M {
//                        let! ϕ = M.updated gb.ϕ
//                        let! cs = M.updated gb.cs
//                        return  { gb with cs = cs; ϕ = ϕ }
//                    }) l                    
//        }
//    member M.YieldFrom f = M { let! (r : list<gen_binding>) = f in yield r }


// type inference algorithms
//

let W_lit = function
    | Int _       -> T_Int
    | Float _     -> T_Float
    | String _    -> T_String
    | Bool _      -> T_Bool
    | Char _      -> T_Char
    | Unit        -> T_Unit

// some wrappers

let rec W_expr (ctx : context) (e0 : expr) =
    let M = new translatable_type_inference_builder<_> (e0)
    M {
        let e = e0.value // uexpr must be bound before translation, or printing will not work
        #if DEBUG_BEFORE_INFERENCE
        let! Q = M.get_Q
        let! θ = M.get_θ
        let! cs = M.get_constraints
        let rule =
            match e with
            | Var _     -> "VAR"
            | Lambda _  -> "ABS"
            | App _     -> "APP"
            | Let _     -> "LET"
            | _         -> "e"
        L.tabulate 2
        L.debug Min "(%-3s) %O\n[C]   %O\n[Q]   %O\n[S]   %O" rule e cs Q θ
        #endif
        let! (ϕ : fxty) = W_expr' ctx e0
        do! resolve_constraints ctx e0
        let! Q' = M.get_Q
        let! θ' = M.get_θ
        let! cs' = M.get_constraints
        // TODO: create a logger.prefix(str) method returning a new logger object which prefixes string str for each line (and deals with EOLs padding correctly)
        L.debug Low "(%-3s) %O\n[:T]  %O\n[nf]  %O\n[F-t] %O\n[e*]  %O\n[C]   %O\n[Q]   %O\n[S]   %O\n[C']  %O\n[Q']  %O\n[S']  %O" rule e ϕ ϕ.nf ϕ.ftype e0 cs Q θ cs' Q' θ'
        #if DEBUG_BEFORE_INFERENCE
        L.undo_tabulate
        #endif
        return ϕ
    } 

and W_decl ctx d =
    let M = new translatable_type_inference_builder<_> (d)
    M {
        L.debug Low "[decl] %O" d
        return! (if ctx.top_level_decl then M.fork_scoped_vars else M.ReturnFrom) <| M { 
            do! W_decl' ctx d
        }
    }  


// main W functions
//

and W_expr_F ctx e0 =
    let M = new translatable_type_inference_builder< _> (e0)
    M {
        let! ϕ = W_expr ctx e0
        return ϕ.ftype
    }

and W_expr' ctx e0 =
    let Lo x = Lo e0.loc x
    let M = new translatable_type_inference_builder< _> (e0)
    let desugar = desugar M (W_expr ctx) e0
    M {
        match e0.value with
        | Lit lit ->
            yield W_lit lit

        | Record (bs, eo) ->
            let! bs = M.List.map (fun (x : id, e) -> M { let! t = W_expr_F ctx e in yield x, t }) bs
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
                M.translated <- E_CId c
                yield t

            | Jb_OverVar ->
                let α = ty.fresh_star_var
                let c = constraintt.fresh_strict Cm_ClosedWorldOverload x α
                do! M.add_constraint c
                M.translated <- E_CId c
                yield α

            | Jb_Var σ ->
                let! { constraints = cs; fxty = ϕ } = M.instantiate_and_inherit_constraints σ
                if cs.is_empty then yield ϕ
                else
                    let e1 = Id x
                    let e2 = possibly_tuple Lo E_CId Tuple cs
                    M.translated <- App (Lo e1, e2)
                    yield ϕ

            | Jb_Data σ ->
                let! { fxty = ϕ } = M.instantiate_and_inherit_constraints σ
                M.translated <- Reserved_Cons x
                yield ϕ
                
            | Jb_Unbound ->
                return Report.Error.unbound_symbol e0.loc x

        | FreeVar x ->
            let! jb = M.search_binding_by_name_Γ x
            let ot =
                // TODO: double check the behaviour of free vars in conjunction with the following cases
                match jb with
                | Jb_Overload t -> Some t
                | Jb_OverVar    
                | Jb_Unbound    -> None
                | Jb_Data σ   
                | Jb_Var σ      -> Report.Warn.freevar_shadowing e0.loc x σ; None
            let t = either ty.fresh_star_var ot
            do! M.add_constraint (constraintt.fresh_strict Cm_FreeVar x t)
            yield t

        | Reserved_Cons x ->
            return unexpected "Reserved_Cons term is not supposed to appear in input code: %O" __SOURCE_FILE__ __LINE__ x

        | PolyCons x ->
            let α = ty.fresh_star_var
            let β = ty.fresh_star_var
            yield T_Open_Variant [x, T_Arrow (α, β)]

        | Lambda ((x, τo), e) ->
            // TODO: make the code for Lambda a generic "on_bind" function and use it every time a similar scenario is needed
            let α, tα = ty.fresh_star_var_and_ty
            let! Q0 = M.get_Q
            let! tx = M {
                match τo with
                | None ->
                    do! M.add_prefix α (Fx_Bottom K_Star)
                    return tα
                | Some τ ->
                    let! t, k = Wk_and_eval_ty_expr_F ctx τ
                    do! M.kunify τ.loc K_Star k
                    return t
            }
            let! t = M.fork_Γ <| M {
                let! _ = M.bind_ungeneralized_Γ x tx
                yield! W_expr ctx e
            }            
            let! tx = M.updated tx
            // check that the inferred type of parameter is a monotype when no annotation was provided
            if τo.IsNone && not tx.is_monomorphic then Report.Error.inferred_lambda_parameter_is_not_monomorphic e0.loc x t
            let! Q3 = M.split_prefix Q0.dom
            let β, tβ = ty.fresh_star_var_and_ty
            let Q3', θ3' = Q3.extend (β, t)
            do! M.update_θ θ3'
            yield Q3', T_Arrow (tx, tβ)

        | App (e1, e2) -> 
            let! Q0 = M.get_Q
            let! ϕ1 = W_expr ctx e1
            let! ϕ2 = W_expr ctx e2
            let α1, tα1 = ty.fresh_star_var_and_ty
            let α2, tα2 = ty.fresh_star_var_and_ty
            let β, tβ = ty.fresh_star_var_and_ty
            do! M.extend [α1, ϕ1; α2, ϕ2; β, Fx_Bottom K_Star]
            do! M.unify e1.loc (T_Arrow (tα2, tβ)) tα1
            let! Q5 = M.split_prefix Q0.dom
            yield Q5, tβ
           
        | Tuple ([] | [_]) as e ->
            return unexpected "empty or unary tuple: %O" __SOURCE_FILE__ __LINE__ e

        | Tuple es ->
            let! ts = M.List.map (W_expr_F ctx) es
            yield T_Tuple ts

        | If (e1, e2, e3) ->
            let! t1 = W_expr_F ctx e1
            do! M.unify e1.loc T_Bool t1
            let! t2 = W_expr_F ctx e2
            let! t3 = W_expr_F ctx e3
            do! M.unify e3.loc t2 t3
            yield t2

        | Let (d, e) ->
            yield! M.fork_Γ <| M {
                do! M.ignore <| W_decl { ctx with top_level_decl = false } d
                yield! W_expr ctx e
            }
        
        | Match (_, []) ->
            return unexpected "empty case list in match expression" __SOURCE_FILE__ __LINE__ 
             
        // TODO: why don't we try to use flex types here and unify schemes instead? does it make sense?
        | Match (e1, cases) ->
            let! te1 = W_expr_F ctx e1
            let tr0 = ty.fresh_star_var
            for p, ewo, e in cases do
                let! tp = W_patt_F ctx p
                do! M.unify p.loc te1 tp
                match ewo with
                | None    -> return ()
                | Some ew -> let! tew = W_expr_F ctx ew
                             do! M.unify ew.loc T_Bool tew
                let! te = W_expr_F ctx e
                do! M.unify e.loc tr0 te
            yield tr0
        
        // TODO: treat Annot as an application to an annotated lambda
        | Annot (e, τ) ->
            let! t, _ = Wk_and_eval_ty_expr_F ctx τ
            let! te = W_expr_F ctx e 
            do! M.unify e.loc t te
            yield t

        | Combine es ->
            if es.Length <= 1 then Debugger.Break ()
            let es, e =
                let rec R = function
                    | []       -> unexpected "empty expression list in combine" __SOURCE_FILE__ __LINE__
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
            let! cs = M.fork_constraints <| M {
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
            yield! desugar (Lo <| Lambda ((x, None), Lo e1))    // TODO: infer the type of the desugared expression?

        | Eject e ->
            let! t = W_expr_F ctx e
            let α = ty.fresh_star_var
            let tr = T_Open_Record []
            do! M.unify e.loc (T_Arrow (tr, α)) t   // TODO: probably this is not working in HML and something like the (APP) rule must be used
            match tr with
            | T_Record (xts, _) ->
                for x, t in xts do
                    // TODO: think about a special construct for expressing constraint mode and strictness
                    do! M.add_constraint (constraintt.fresh_strict Cm_OpenWorldOverload x t)
            | _ -> unexpected "non-record type in eject expression: %O" __SOURCE_FILE__ __LINE__ tr
            let! cs = M.get_constraints
            let x = fresh_reserved_id ()
            let e1 = Record ([ for { name = y } in cs -> y, Lo <| Id y ], None)
            let e2 = App (e, Lo <| Id x)
            yield! desugar (Lo <| Let (Lo <| D_Bind [{ qual = decl_qual.none; patt = Lo <| P_Var x; expr = Lo e1 }], Lo e2))    // TODO: infer the type of the desugared expression?

        | Solve (e, τ) ->
            let! te = W_expr_F ctx e
            let! t, _ = Wk_and_eval_ty_expr_F ctx τ
            do! M.unify e.loc (T_Open_Record []) t
            let xts =
                match t with
                | T_Record (xts, _) -> xts
                | _                 -> unexpected "non-record type in manual resolution: %O" __SOURCE_FILE__ __LINE__ t
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
            M.translated <- e.value
            yield te

    }
    

and W_decl' (ctx : context) (d0 : decl) =
    let M = new translatable_type_inference_builder<_> (d0)
    let desugar = desugar M (W_decl ctx) d0
    let unify_and_resolve (ctx : context) (e : node<_, _>) t1 t2 =
        M {
            do! M.unify e.loc t1 t2
            do! resolve_constraints ctx e
        }
    let jk decl_qual x t = if decl_qual.over then Jk_Inst (x, t.GetHashCode ()) else Jk_Var x

    let gen_bind prefixes ({ x = x; ϕ = ϕ} as gb) =
        let dq = gb.b.qual
        let e0 = gb.b.expr
        let loc = e0.loc
        let Lo x = Lo loc x
        M {
            let! { γ = γ; constraints = cs } = M.get_state
            // check shadowing and relation with previous bindings
            let! jb = M.search_binding_by_name_Γ x
            if dq.over then
                match jb with                
                | Jb_Overload pt -> if not (ϕ.is_instance_of { loc = loc; γ = γ } pt) then Report.Error.instance_not_valid loc x ϕ pt   // open-world overloadable instance
                | Jb_Unbound     -> Report.Warn.let_over_without_previous_let loc x                                                     // let-over binding without a previous let-non-over is a warning
                | _              -> ()                                                                                                  // let-over binding after anything else is valid closed-world overloading
            else
                match jb with                
                | Jb_Overload _ -> Report.Warn.shadowing_overloaded_symbol loc x    // let-non-over after overload
                | _             -> ()                                               // normal binding that can shadow legally

            // check constraints solvability and scope escaping
            for { name = cx; ty = ct } as c in cs do
                let αs = ct.fv - ϕ.fv in if not αs.IsEmpty then Report.Hint.unsolvable_constraint loc x ϕ cx ct αs
                match c.mode with
                | Cm_OpenWorldOverload ->
                    let! jb = M.search_binding_by_name_Γ cx
                    match jb with
                    | Jb_Overload _ -> ()
                    | _ ->
                        Report.Warn.constraint_escaped_scope_of_overload loc cx ct x ϕ
                        do! M.remove_constraint c
                        do! M.add_constraint { c with mode = Cm_FreeVar; ty = ct }              // escaped overload constraint becomes a FreeVar constraint

                | Cm_ClosedWorldOverload ->
                    Report.Error.closed_world_overload_constraint_not_resolved loc cx ct x ϕ    // closed-world overload constraint not resolved

                | _ -> ()

            // generalize, bind and translate
            let jk = jk dq x ϕ
            let! σ =
                let jm = if dq.over then Jm_Overloadable else Jm_Normal
                in
                    M.bind_generalized_Γ jk jm ϕ
            let e1 = if cs.is_empty then e0 else LambdaFun ([possibly_tuple Lo P_CId P_Tuple cs], Lo e0.value)
            Report.prompt ctx (prefixes @ dq.as_tokens) x ϕ (Some (Config.Printing.ftype_instance_sep, σ.fxty.ftype))
            return jk, e1
        }

    M {
        match d0.value with
        | D_Overload []
        | D_Bind []
        | D_Rec []
        | D_Reserved_Multi [] ->
            return unexpected "empty declaration list" __SOURCE_FILE__ __LINE__

        | D_Overload l ->
            for { id = x; signature = τ } in l do
                let! t, k = Wk_and_eval_ty_expr_F ctx τ
                do! M.kunify τ.loc K_Star k
                let! _ = M.bind_Γ (Jk_Var x) { mode = Jm_Overloadable; scheme = Ungeneralized t }
                Report.prompt ctx Config.Printing.Prompt.overload_decl_prefixes x t None

        | D_Bind bs ->
            do! M.fork_constraints <| M {
                let! l =
                    // TODO: refactor this crap an write shorter code
                    M.List.collect (fun ({ patt = p; expr = e } as b) -> M {
                                do! M.clear_constraints
                                let! ϕe = W_expr ctx e
                                let te = ϕe.ftype
                                return! M.fork_Γ <| M {
                                    let (|B_Unannot|B_Annot|B_Patt|) = function
                                        | ULo (P_Var x)                    -> B_Unannot x
                                        | ULo (P_Annot (ULo (P_Var x), τ)) -> B_Annot (x, τ)
                                        | p                                -> B_Patt p
                                    match p with
                                    | B_Unannot x ->
                                        let! cs = M.get_constraints
                                        return [{ b = b; x = x; cs = cs; ϕ = Fx_F_Ty ϕe.ftype }]      // by default bind inferred types as F-types

                                    | B_Annot (x, τ) ->
                                        let! ϕx, k = Wk_and_eval_ty_expr_fx ctx τ
                                        do! M.kunify τ.loc K_Star k
                                        let! ϕe = M {
                                            match ϕx with
                                            | Fx_F_Ty tx ->
                                                do! M.unify τ.loc tx te
                                                yield te                        // bind inferred type as an F-type when the annotation is an F-type
                                            | _ ->
                                                do! M.subsume τ.loc te ϕx
                                                yield ϕe                        // bind the inferred type when annotation is a flex type instead
                                        }
                                        let! cs = M.get_constraints
                                        return [{ b = b; x = x; cs = cs; ϕ = ϕe }] // TODO: cleanup the gen_binding type, perhaps putting a field of type scheme

                                    | B_Patt p ->
                                        let! tp = W_patt_F ctx p
                                        do! M.unify e.loc tp te                 // TODO: redesign the behaviour of pattern-based let-bindings reusing (LAMBDA) and (APP) rules
                                        do! resolve_constraints ctx e
                                        let! cs = M.get_constraints
                                        return! vars_in_patt p |> Set.toList |> M.List.map (fun x -> M { let! { scheme = σ } = M.lookup_Γ (Jk_Var x) in return { b = b; x = x; cs = cs; ϕ = σ.fxty } })
                                }
                            }) bs
                let! bs' = M.List.map (fun gb -> M { let! () = M.set_constraints gb.cs in return! gen_bind Config.Printing.Prompt.value_decl_prefixes gb }) l
                M.translated <- D_Bind [for jk, e in bs' -> { qual = decl_qual.none; patt = Lo e.loc (P_Jk jk); expr = e }]
            }

        | D_Rec bs ->
            do! M.fork_constraints <| M {
                let! l =
                    M.fork_Γ <| M {
                        do! M.clear_constraints
                        let! l = M.List.map (fun ({ qual = dq; par = x, _; expr = e } as b) -> M {
                                        // TODO: verify how let rec works
                                        let! tx = M {
                                            match b.par with
                                            | _, None ->
                                                let α, tα = ty.fresh_star_var_and_ty
                                                do! M.add_prefix α (Fx_Bottom K_Star)
                                                return tα

                                            | _, Some τ -> 
                                                let! t, k = Wk_and_eval_ty_expr_F ctx τ
                                                do! M.kunify τ.loc K_Star k
                                                return t                                                
                                        }
                                        let! _ = M.bind_Γ (jk dq x tx) { mode = Jm_Normal; scheme = Ungeneralized tx }  // TODO: reuse the (LAMBDA) rule behaviour
                                        return b, x, tx
                                    }) bs
                        // basic value restriction for let rec
                        for { expr = e }, _, tx in l do
                            let! te = W_expr_F ctx e
                            do! unify_and_resolve ctx e tx te
                            match te with
                            | T_Arrow _ -> ()
                            | _         -> Report.Error.value_restriction_non_arrow_in_letrec e.loc te
                        return l
                    }
                let! bs' = M.List.map (fun (b : rec_binding, x, tx) -> M { return! gen_bind Config.Printing.Prompt.rec_value_decl_prefixes { b = b; x = x; cs = cs; ϕ = Fx_F_Ty tx } }) l
                M.translated <- D_Rec [for jk, e in bs' -> { qual = decl_qual.none; par = jk.pretty, None; expr = e }]
            }

        | D_Open (q, e) ->
            let! t = W_expr_F ctx e
            do! unify_and_resolve ctx e (T_Open_Record []) t
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
            let d = Lo d0.loc <| Td_Rec bs
            do! Wk_and_eval_ty_rec_bindings ctx d bs

        | D_Datatype { id = c; kind = kc; datacons = bs } ->
            // type constructor must have star as codomain
            let split (|Arrows|_|) = function
                | Arrows ks -> let ks = List.rev ks in List.tail ks, List.head ks
                | k         -> [], k
            let kdom, kcod = split (|K_Arrows|_|) kc
            do! M.kunify d0.loc K_Star kcod
            let! kσ = M.gen_bind_γ c kc
            Report.prompt ctx Config.Printing.Prompt.datatype_decl_prefixes c kσ None
            // rebind kc to the unified kind, by reinstantiating it rather than keeping the user-declared one
            let kc = kσ.instantiate
            for { id = x; signature = τx } in bs do
                let! tx, kx = Wk_and_eval_ty_expr_F ctx τx
                do! M.kunify τx.loc K_Star kx
                // each curried argument of the each data constructor must have kind star
                match tx with
                | T_Arrows ts -> for t in ts do do! M.kunify τx.loc K_Star t.kind
                | _           -> return ()
                // each data constructor's codomain must be the type constructor being defined
                let pt = T_Apps [ yield T_Cons (c, kc); for _ in kdom -> ty.fresh_star_var ]
                let _, tcod = split (|T_Arrows|_|) tx
                let! γ = M.get_γ
                if not (tcod.is_instance_of { γ = γ; loc = τx.loc } pt) then return Report.Error.data_constructor_codomain_invalid τx.loc x c tcod
                let! σ = M.bind_generalized_Γ (Jk_Data x) Jm_Normal (Fx_F_Ty tx)
                Report.prompt ctx Config.Printing.Prompt.data_decl_prefixes x σ None

        | D_Kind _ ->
            return not_implemented "%O" __SOURCE_FILE__ __LINE__ d0
    }  


and W_patt_F ctx p0 =
    let M = new translatable_type_inference_builder<_> (p0)
    M {
        let! ϕ = W_patt ctx p0
        return ϕ.ftype
    }

and W_patt ctx (p0 : patt) : M<fxty> =
    let M = new type_inference_builder (p0.loc)
    let loc0 = p0.loc
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
            let α = var.fresh
            let k = K_Star
            do! M.add_prefix α (Fx_Bottom k)
            let t = T_Var (α, k)
            do! M.ignore <| M.bind_ungeneralized_Γ x t
            yield t

        | P_Lit lit ->
            yield W_lit lit

        | P_Tuple ([] | [_]) as p ->
            return unexpected "empty or unary tuple in pattern: %O" __SOURCE_FILE__ __LINE__ p

        | P_Tuple ps ->
            let! ts = M.List.map (W_patt_F ctx) ps
            yield T_Tuple ts

        | P_Record xps ->
            let! xts = M.List.map (fun (x : id, p) -> M { let! t = W_patt_F ctx p in return x, t }) xps
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

        | P_App (p1, p2) ->
            // TODO: consider supporting HML for pattern application
            let! t1 = W_patt_F ctx p1
            let! t2 = W_patt_F ctx p2
            let α = ty.fresh_star_var
            do! M.unify p1.loc (T_Arrow (t2, α)) t1
            yield α

        | P_Wildcard ->
            yield ty.fresh_star_var

        | P_As (p, x) ->
            let! tp = W_patt_F ctx p
            let! _ = M.bind_ungeneralized_Γ x tp
            yield tp

        | P_Annot (p, τ) ->
            let! t, _ = Wk_and_eval_ty_expr_F ctx τ
            let! tp = W_patt_F ctx p
            do! M.unify p.loc t tp
            yield t
    }


and W_program (prg : program) =
    let ctx = context.top_level
    let M = new type_inference_builder ()
    M {
        for d in prg.decls do
            do! W_decl ctx d
        match prg.main with
        | None -> ()
        | Some e ->
            let! t = W_expr_F ctx (Lo e.loc <| Val e)
            do! M.unify e.loc T_Int t
    }
