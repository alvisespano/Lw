(*
 * Lw
 * Typing/Report.Error.fs: type error Report.Error.ng
 * (C) 2000-2014 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Report

open FSharp.Common.Parsing
open FSharp.Common.Prelude
open FSharp.Common.Log
open Lw.Core
open Lw.Core.Absyn
open Lw.Core.Typing.Defs
open Lw.Core.Globals
open Printf
open System

type numeric_error (header, msg, n : int, loc) =
    inherit located_error (header, msg, loc)
    member val code = n

type type_error (msg, n, loc) =
    inherit numeric_error ("type error", msg, n, loc)

type kind_error (msg, n, loc) =
    inherit numeric_error ("kind error", msg, n, loc)

let flatten_and_trim_strings sep ss = flatten_strings sep (seq { for s : string in ss do let s = s.Trim () in if not <| String.IsNullOrWhiteSpace s then yield s })

let inline prompt ctx prefixes x (σ : ^s) o =
    let top_level = (^a : (member top_level_decl : bool) ctx)
    let log = if top_level then L.msg High else L.msg Normal
    let prefixes = List.distinct <| if top_level then prefixes else Config.Printing.Prompt.nested_decl_prefix :: prefixes
    use N = var.reset_normalization ()
    log "%s %s %O%s"
        (flatten_and_trim_strings Config.Printing.Prompt.prefix_sep (prefixes @ [x]))
        (^s : (static member binding_separator : string) ())
        σ
        (soprintf " = %O" o)

let private E' f n loc fmt = let N = var.reset_normalization () in throw_formatted (fun msg -> N.Dispose (); f (msg, n, loc)) fmt
let private E x = E' (fun args -> new type_error (args)) x
let private Ek x = E' (fun args -> new kind_error (args)) x
   
let private mismatch f n what1 what2 loc expected1 got1 expected2 got2 =
    use N = var.reset_normalization ()
    let s = sprintf "%s was expected to have %s %O but got %s %O" what1 what2 expected1 what2 got1
    let s = s + if expected1 <> expected2 && got1 <> got2 then sprintf ", because %s %O is not compatible with %O" what2 expected2 got2 else ""
    in
        f n loc ("%s" : StringFormat<_, _>) s


[< RequireQualifiedAccess >]
module Error =            

    // kind errors

    let kind_mismatch x = mismatch Ek 1 "type expression" "kind" x

    let kind_circularity loc (k1 : kind) (k2 : kind) α (k : kind) =
        Ek 2 loc "unification between kinds %O and %O failed because kind variable %O occurs in kind %O" k1 k2 α k

    let unbound_type_symbol loc x =
        Ek 3 loc "type variable or constructor %s is undefined" x


    // type errors
    
    let type_mismatch x = mismatch E 4 "expression" "type" x

    let row_tail_circularity loc ρ θ =
        E 5 loc "unification fails because row type variable type variable %O occurs in the domain of substituion %O" ρ θ

    let cannot_rewrite_row loc l r1 r2 =
        E 6 loc "row type %O cannot be rewritten with label %s in order to match row type %O" r1 l r2

    let circularity loc (t1 : ty) (t2 : ty) tα (t : ty) =
        E 7 loc "unification between types %O and %O failed because type variable %O occurs in type %O" t1 t2 tα t

    let variables_already_bound_in_pattern loc xs p =
        E 8 loc "variables %s are bound multiple times in pattern %O" (flatten_stringables ", " xs) p
        
    let value_not_resolved loc cs =
        E 9 loc "expression will not evaluate to a ground value because some constraints are unresolved: %O" (predicate.pretty_constraints cs)

    let duplicate_label loc l what =
        E 10 loc "multiple occurrences of label %s in %s" l what

    let unbound_symbol loc x =
        E 11 loc "variable identifier %s is undefined" x

    let pattern_in_letrec loc p =
        E 12 loc "let-rec supports only simple identifier bindings, but a pattern was used: %O" p

    let unbound_overloaded_symbol loc x =
        E 13 loc "overload identifier %s is undefined" x

    let instance_not_valid loc x t pt =
        E 14 loc "overloaded instance `%s : %O` does not respect principal type %O" x t pt

    let different_vars_in_sides_of_or_pattern loc xs =
        E 15 loc "sides of or-pattern must match exactly the same variables: %s are missing" (flatten_stringables ", " xs)
    
    let value_restriction_non_arrow_in_letrec loc t =
        E 16 loc "value restriction: values bound by let-rec must be arrow types, but got %O" t

    let type_patterns_not_exhaustive loc t =
        E 17 loc "type patterns did not match input type: %O" t

    let same_vars_in_sides_of_or_pattern loc xs =
        E 18 loc "sides of or-pattern must match different variables: %s are in common" (flatten_stringables ", " xs)

    let data_constructor_codomain_invalid loc x c t =
        E 19 loc "data constructor %s does not construct datatype %O because its codomain is type %O" x c t

    let data_constructor_bound_to_wrong_symbol loc what x t =
        E 20 loc "data constructor %s in pattern is already bound to %s : %O" x what t

    let unbound_data_constructor loc x =
        E 21 loc "data constructor %s is undefined" x

    let closed_world_overload_constraint_not_resolved loc cx ct x t =
        // TODO: print a better message, hiding the mention to constraints and referring to closed-world overloading only
        E 22 loc "when generalizing symbol `%O : %O` the constraint `%s : %O` has not been resolved and was referring to a closed-world overloaded symbol" x t cx ct

    let lambda_parameter_is_not_monomorphic loc x t =
        E 23 loc "function parameter is used polymorphically: %s : %O" x t


[< RequireQualifiedAccess >]
module Warn =
    let private W n loc pri fmt =
        if Set.contains n Config.Report.disabled_warnings then null_L.warn Unmaskerable fmt
        else L.nwarn n pri ("%O: " %+%% fmt) loc

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


[< RequireQualifiedAccess >]
module Hint =
    let private H n loc pri fmt =
        if Set.contains n Config.Report.disabled_hints then null_L.hint Unmaskerable fmt
        else L.nhint n pri ("%O: " %+%% fmt) loc

    let unsolvable_constraint loc x t cx ct αs = 
        H 1 loc Min "constraint `%s : %O` is unsolvable because type variables %s do not appear in %O : %O. This prevents automatic resolution to determine instances, therefore \
        manual resolution will be needed for evaluating a ground value"
            cx ct (flatten_stringables ", " αs) x t

    // TODO: is this hint message really unnecessary?
    let manually_resolved_symbol_refers_to_mupliple_constraints loc x t cs =
        H 2 loc Normal "symbol `%O : %O` specified in manual resolution refers to multiple constraints sharing the same name. \
        Unification with user-specified type %O will apply in unpredicible order, possibly preventing the desired resolution to take place. \
        In case of undesired results, consider reordering manually resolved symbols or redesigning code in such a way that multiple occurrences are no more an issue.\n\
        Current constraints are:\n%O"
            x t t (mappen_strings (fun (x, t) -> sprintf "   %O : %O" x t) "\n" cs)

