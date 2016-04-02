(*
 * Lw
 * Typing/Report.Error.fs: type error Report.Error.ng
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Report

open FSharp.Common
open FSharp.Common.Parsing
open FSharp.Common.Log
open Lw.Core
open Lw.Core.Absyn
open Lw.Core.Absyn.Misc
open Lw.Core.Absyn.Var
open Lw.Core.Absyn.Kind
open Lw.Core.Absyn.Sugar
open Lw.Core.Typing.Equivalence
open Lw.Core.Typing.Defs
open Lw.Core.Globals
open Printf
open System

type type_error (msg, n, loc) =
    inherit static_error (type_error.error_name, msg, n, loc)
    static member error_name = "type error"

type kind_error (msg, n, loc) =
    inherit static_error (kind_error.error_name, msg, n, loc)
    static member error_name = "kind error"

let flatten_and_trim_strings sep ss = flatten_strings sep (seq { for s : string in ss do let s = s.Trim () in if not <| String.IsNullOrWhiteSpace s then yield s })

let inline prompt ctx prefixes x (t1 : ^t1) t2o =
    let is_top_level = (^a : (member is_top_level : bool) ctx)
    let log =
        if is_top_level then L.msg Normal
        else
            #if DEBUG
            L.msg Low
            #else
            null_L.msg Low
            #endif
    let prefixes = List.distinct <| if is_top_level then prefixes else Config.Printing.Prompt.nested_decl_prefix :: prefixes
    let header = sprintf "%s %s" (flatten_and_trim_strings Config.Printing.Prompt.header_sep (prefixes @ [x])) (^t1 : (static member binding_separator : string) ())
    use N = var.reset_normalization
    let t1 = (^t1 : (member pretty : string) t1)
    let reduction = 
        match t2o with
        | Some (sep, t2) ->
            let t2 = sprintf "%O" t2
            in
                if t1 = t2 then ""
                else
                    let s = sprintf "%s %s" sep t2
                    in
                        if header.Length + 1 + t1.Length + 1 + s.Length >= Console.BufferWidth / 2 then sprintf "\n%s%s" (spaces (header.Length + 1)) s
                        else sprintf " %s" s
        | _ -> ""
    log "%s %s%s" header t1 reduction
        

let private E f n loc fmt = let N = var.reset_normalization in throw_formatted (fun msg -> N.Dispose (); f (msg, n, loc)) fmt
let private Es n loc fmt = E (fun (a, b, c) -> new static_error (a, b, c)) n loc fmt
let private Et n loc fmt = E (fun args -> new type_error (args)) n loc fmt
let private Ek n loc fmt = E (fun args -> new kind_error (args)) n loc fmt
   
let private mismatch E (n : int) (loc : location) is_equivalent what1 what2 expected1 got1 expected2 got2 =
    use N = var.reset_normalization
    let s =
        sprintf "%s was expected to have %s %O but got %s %O" what1 what2 expected1 what2 got1
        + (if not (is_equivalent expected1 expected2) && not (is_equivalent got1 got2) then
            sprintf ", because %s %O is not compatible with %O" what2 expected2 got2
           else "")
    in
        E n loc ("%s" : StringFormat<_, _>) s

//let private mismatch1 E (n : int) (loc : location) what1 what2 expected1 got1 expected2 got2 =
//    use N = var.reset_normalization
//    let expected1 = sprintf "%O" expected1
//    let expected2 = sprintf "%O" expected2
//    let got1 = sprintf "%O" got1
//    let got2 = sprintf "%O" got2
//    let s = sprintf "%s was expected to have %s %s but got %s %s" what1 what2 expected1 what2 got1
//    let s = s + if expected1 <> expected2 && got1 <> got2 then sprintf ", because %s %s is not compatible with %s" what2 expected2 got2 else ""
//    in
//        E n loc ("%s" : StringFormat<_, _>) s
//
//let inline private mismatch2 E (n : int) (loc : location) what1 what2 (expected1 : ^t) (got1 : ^t) (expected2 : ^t) (got2 : ^t) =
//    use N = var.reset_normalization
//    let s =
//        sprintf "%s was expected to have %s %O but got %s %O" what1 what2 expected1 what2 got1
//        + (if (^t : (member is_equivalent : ^t -> bool) expected1, expected2) && (^t : (member is_equivalent : ^t -> bool) got1, got2) then
//            sprintf ", because %s %O is not compatible with %O" what2 expected2 got2
//           else "")
//    in
//        E n loc ("%s" : StringFormat<_, _>) s
//
//let inline private mismatch3 E E' (n : int) (loc : location) what1 what2 (expected1 : ^t) (got1 : ^t) (expected2 : ^t) (got2 : ^t) =
//    if (^t : (member is_equivalent : _) expected1) expected2 && (^t : (member is_equivalent : _) got1) got2 then
//        E n loc "%s was expected to have %s %O but got %s %s" what1 what2 expected1 what2 got1
//    else
//        E' n loc "%s was expected to have %s %O but got %s %s, because %s %s is not compatible with %s" what1 what2 expected1 what2 got1 what2 expected2 got2

let private circularity E n loc what x1 x2 α x =
    use N = var.reset_normalization
    let s = sprintf "unification between %ss %O and %O failed because %s variable %O occurs in %s %O and unification would produce an infinite %s" what x1 x2 what α what x what
    in
        E n loc ("%s" : StringFormat<_, _>) s


[< RequireQualifiedAccess >]
module Error =            
    
    // put here only those codes that need to be caught or detected while typing
    module Code =
        let type_mismatch = 200


    // unbound symbol errors

    let unbound_symbol loc x =
        Es 10 loc "variable identifier `%s` is undefined" x

    let unbound_type_constructor loc x =
        Es 11 loc "type constructor `%s` is undefined" x

    let unbound_data_constructor loc x =
        Es 12 loc "data constructor `%s` is undefined" x


    // misc errors 

    let duplicate_label loc l what =
        Es 100 loc "multiple occurrences of label '%s' in %s" l what  // this is gonna be removed when overloading of record labels will be implemented


    // type errors
    
    let type_mismatch loc expected1 got1 expected2 got2 =
        mismatch Et Code.type_mismatch loc (fun (x : ty) -> x.is_equivalent) "expression" "type" expected1 got1 expected2 got2

    let row_tail_circularity loc ρ tθ =
        Et 201 loc "unification fails because row type variable type variable %O occurs in the domain of substituion %O" ρ tθ

    let cannot_rewrite_row loc l r1 r2 =
        Et 202 loc "row type %O cannot be rewritten with label %s in order to match row type %O" r1 l r2

    let type_circularity loc (t1 : ty) (t2 : ty) tα (t : ty) =
        circularity Et 203 loc "type" t1 t2 tα t
        
    let value_not_resolved loc cs =
        Et 204 loc "expression will not evaluate to a ground value because some constraints are unresolved: %O" cs

    let instance_not_valid loc x t pt =
        Et 205 loc "overloaded instance `%s : %O` does not respect principal type %O" x t pt
    
    let value_restriction_non_arrow_in_letrec loc t =
        Et 206 loc "value restriction: values bound by let-rec must be arrow types, but got %O" t

    let data_constructor_codomain_invalid loc x c t =
        Et 207 loc "data constructor %s does not construct datatype %O because its codomain has type %O" x c t

    let closed_world_overload_constraint_not_resolved loc cx ct x t =
        // TODO: print a better message, just refer to the notion of closed-world overloading, without mentioning constraints
        Et 208 loc "when generalizing symbol `%O : %O` the constraint `%s : %O` has not been resolved and was referring to a closed-world overloaded symbol" x t cx ct

    let inferred_lambda_parameter_is_not_monomorphic loc x t =
        Et 209 loc "function parameter is used polymorphically without an explicit annotation: %s : %O" x t

    let skolemized_type_variable_escaped loc tsk =
        Et 210 loc "skolem type variable %O escaped" tsk

    let inferred_rec_definition_is_not_monomorphic loc x t =
        Et 211 loc "recursive definition is used polymorphically without an explicit annotation: %s : %O" x t

    let annotated_lambda_parameter_is_flex loc x (ϕ : fxty) =
        Et 212 loc "annotated function parameter %s : %O is a flexible type, but it must be a System-F type" x ϕ


    // pattern-related errors

    let variables_already_bound_in_pattern loc xs p =
        Es 300 loc "variables %s are bound multiple times in pattern %O" (flatten_stringables ", " xs) p

    let pattern_in_letrec loc p =
        Es 301 loc "let-rec supports only simple identifier bindings, but a pattern was used: %O" p

    let unbound_overloaded_symbol loc x =
        Es 302 loc "overload identifier %s is undefined" x

    let different_vars_in_sides_of_or_pattern loc xs =
        Es 303 loc "sides of or-pattern must match exactly the same variables: %s are missing" (flatten_stringables ", " xs)

    let type_patterns_not_exhaustive loc t =
        Es 304 loc "type patterns did not match input type: %O" t
    
    let same_vars_in_sides_of_or_pattern loc xs =
        Es 305 loc "sides of or-pattern must match different variables: %s are in common" (flatten_stringables ", " xs)

    let data_constructor_bound_to_wrong_symbol loc what x t =
        Es 306 loc "data constructor %s in pattern is already bound to %s : %O" x what t

    let invalid_pattern_application loc p =
        Et 307 loc "pattern application must have a data constructor as left-most term, but here is: " p


    // kind errors

    let kind_mismatch loc expected1 got1 expected2 got2 =
        mismatch Ek 400 loc (fun (x : kind) -> x.is_equivalent) "type expression" "kind" expected1 got1 expected2 got2

    let kind_circularity (loc : location) (k1 : kind) (k2 : kind) kα (k : kind) =
        circularity Ek 401 loc "kind" k1 k2 kα k

//    let type_variable_bound_to_generalized_kscheme loc x k =
//        let α = var.fresh_named x
//        Ek 402 loc "type variable %O used in place of type constructor %s :: %O" α x k


[< RequireQualifiedAccess >]
module Warn =
    let private W n loc pri (fmt : StringFormat<'a, _>) =
        use N = var.reset_normalization
        if Set.contains n Config.Report.disabled_warnings then null_L.warn Min fmt
        else L.nwarn n pri (StringFormat<location -> 'a, _> ("%O: " + fmt.Value)) loc

    let expected_unit_statement loc t =
        W 1 loc High "expected expression of type %O when used as statement, but got type %O" T_Unit t

    let cyclic_constraint loc x t =
        W 2 loc Min "constraint resolution would lead to indefinite recursion and `%O : %O` is suspended" x t

    let shadowing_overloaded_symbol loc x =
        W 3 loc Normal "symbol %s is already overloaded in this context: normal binding will imply shadowing" x

    let constraint_escaped_scope_of_overload loc cx ct x t =
        W 4 loc Normal "when generalizing symbol `%O : %O` the constraint `%s : %O` has escaped its overload scope and has been converted into a freevar constraint" x t cx ct

    let resolution_is_ambiguous loc x t cands =
        W 5 loc High "resolution of constraint `%s : %O` is ambiguous in this context. Manual resolution might be needed at invocation site in order to evaluate it to a ground value. \
        Current candidates are:\n%O"
            x t (mappen_strings (sprintf "   %O") "\n" cands)

    let freevar_shadowing loc x t =
        W 6 loc Low "freevar will shadow an ordinary variable or data constructor with the same name already bound in this scope: %O : %O" x t

    let manually_resolved_symbol_does_not_exist loc x t =
        W 7 loc Normal "symbol `%O : %O` specified in manual resolution does not appear among constraints" x t

    let manual_resolution_not_enough loc x t =
        W 8 loc High "symbol `%O : %O` specified in manual resolution still exists among constraints, thus it has not been resolved" x t

    let manually_resolved_symbol_does_respect_overload loc x t t' =
        W 9 loc High "symbol `%O : %O` specified in manual resolution refers to overload `%O : %O` but is not compatible the declared principal type" x t x t'

    let no_constraints_to_abstract loc =
        W 10 loc High "constraint set is empty, thus predicate abstraction takes place on any record type"

    let no_constraints_to_loosen loc =
        W 11 loc High "expression does not introduce constraints that could be loosened"

    let let_over_without_previous_let loc x =
        W 12 loc Low "closed-world overloading of symbol %s without a previous let non-over binding" x

    let unused_quantified_type_variable loc α t =
        W 13 loc Normal "quantified type variable %O does not occur in type %O" α t
//
//    let annot_flex_type_became_Ftype loc ϕ t =
//        W 14 loc Low "type annotation %O is a flexible type and is reduced to a standard (System-F) type: %O" ϕ t

    let unquantified_variables_in_type loc t =
        W 15 loc Low "type expression has unquantified type variables: %O" t

[< RequireQualifiedAccess >]
module Hint =
    let private H n loc pri (fmt : StringFormat<'a, _>) =
        use N = var.reset_normalization
        if Set.contains n Config.Report.disabled_hints then null_L.hint Unmaskerable fmt
        else L.nhint n pri (StringFormat<location -> 'a, _> ("%O: " + fmt.Value)) loc

    let unsolvable_constraint loc x t cx ct αs = 
        H 1 loc High "constraint `%s : %O` is unsolvable because type variables %s do not appear in %O : %O. This prevents automatic resolution to determine instances, therefore \
        manual resolution will be needed for evaluating a ground value"
            cx ct (flatten_stringables ", " αs) x t

    // TODO: is this hint message really not necessary anymore?
    let manually_resolved_symbol_refers_to_mupliple_constraints loc x t cs =
        H 2 loc Low "symbol `%O : %O` specified in manual resolution refers to multiple constraints sharing the same name. \
        Unification with user-specified type %O will apply in unpredicible order, possibly preventing the desired resolution to take place. \
        In case of undesired results, consider reordering manually resolved symbols or redesigning code in such a way that multiple occurrences are no more an issue.\n\
        Current constraints are:\n%O"
            x t t (mappen_strings (fun (x, t) -> sprintf "   %O : %O" x t) "\n" cs)

    let datacons_contains_env_fv loc c x tx =
        H 3 loc Normal "datatype %s defines a data constructor %s whose type %O has type variables that cannot be generalized" c x tx

    let scoped_tyvar_was_not_generalized loc α =
        H 4 loc Min "scoped type variable %O will not be generalized" α

    let auto_generalization_occurred_in_annotation loc t t' =
        H 5 loc Low "type annotation %O has been automatically generalized to %O" t t'

    let subsumption_in_annotated_binding loc tann ϕinf =
        H 6 loc High "type annotation %O is an instance of the inferred flex type %O, which may lead to a loss of type information, possibly introducing the need of additional type annotations in further code" tann ϕinf
