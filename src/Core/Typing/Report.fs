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

type Globals.logger with
    member this.norm l =
        let N = var.reset_normalization
        this.cont <- fun () -> N.Dispose ()
        l

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

let private circularity E n loc what x1 x2 α x =
    use N = var.reset_normalization
    let s = sprintf "unification between %ss %O and %O failed because %s variable %O occurs in %s %O and unification would produce an infinite %s" what x1 x2 what α what x what
    in
        E n loc ("%s" : StringFormat<_, _>) s


[< RequireQualifiedAccess >]
module Error =            
    
    // put here only those error codes that need to be caught, detected or reused by other parts of the program for some reason (e.g., UnitTest)
    module Code =
        let type_mismatch = 200
        let unbound_symbol = 10


    // unbound symbol errors

    let unbound_symbol loc x =
        Es Code.unbound_symbol loc "variable identifier `%s` is undefined" x

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
        // TODO: print a better message, just refer to closed-world overloading without mentioning constraints
        Et 208 loc "when generalizing symbol `%O : %O` the closed-world overloading constraint `%s : %O` has not been resolved" x t cx ct

    let inferred_type_is_not_monomoprhic loc what t =
        Et 209 loc "type inferred for %s is %O, which is not monomorphic: if you intented to use it polymorphically add an explicit annotation" what t

    let annotation_is_flex_but_expected_an_F_type loc (ϕ : fxty) =
        Et 210 loc "annotated type %O is a flexible type, but a System-F type was expected" ϕ

    let skolemized_type_variable_escaped loc tsk =
        Et 211 loc "skolem type variable %O escaped" tsk

    let illegal_pattern_in_rec_binding loc p =
        Et 212 loc "illegal pattern form in recursive binding: %O" p


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


// alert manager
//

[< RequireQualifiedAccess >]
module Alert =
    open System.Collections
    open System.Collections.Generic

    /// Opaque representation of manager state
    type state =
        val disabled : int Set option
        internal new (d) = { disabled =  d }

    type manager (disabled_by_default) =
        let mutable disabled_ : int Set option = Some disabled_by_default
        let mutable tracers : WeakReference<tracer> list = []

        member __.disable n =
            match disabled_ with
            | None     -> ()
            | Some set -> disabled_ <- Some (Set.add n set)

        member __.enable n =
            disabled_ <- Some (match disabled_ with
                               | None     ->  Set.singleton n
                               | Some set ->  Set.remove n set)

        member __.is_disabled n =
            match disabled_ with
            | None     -> true
            | Some set -> Set.contains n set

        member this.is_enabled n = not (this.is_disabled n)

        member __.state
            with get () = new state (disabled_)
            and set (st : state) = disabled_ <- st.disabled

        member __.disable_all = disabled_ <- None
        member __.enable_all = disabled_ <- Some Set.empty

        member this.tracer =
            let r = new tracer (this)
            tracers <- new WeakReference<tracer> (r) :: tracers
            r

        member private __.filter_tracers f =
            let tr = ref Unchecked.defaultof<tracer>
            tracers <- tracers |> List.filter (fun wtr ->
                    if wtr.TryGetTarget tr then
                        f !tr
                    else false)

        member this.remove_tracer tr0 = this.filter_tracers ((<>) tr0) 

        member this.log f n loc pri (fmt : StringFormat<'a, _>) =
            this.filter_tracers (fun tr -> tr.add n; true)
            if this.is_enabled n then L.norm f n pri (StringFormat<location -> 'a, _> ("%O: " + fmt.Value)) loc
            else null_L.msg Min fmt // uses msg channel but any would do, as it actually doesn't output


    and tracer (r : manager) =
        inherit disposable_base ()
        let mutable nums = Set.empty
        member internal __.add n = nums <- Set.add n nums
        member __.to_set = nums
        override this.cleanup_managed () = r.remove_tracer this
        interface IEnumerable<int> with
            member this.GetEnumerator () = (Set.toSeq nums).GetEnumerator ()
        interface IEnumerable with
            member this.GetEnumerator () = (this :> IEnumerable<int>).GetEnumerator () :> IEnumerator


// warnings and hints
//

let warnings = new Alert.manager (Config.Report.disabled_warnings)
let hints = new Alert.manager (Config.Report.disabled_hints)

[< RequireQualifiedAccess >]
module Warn =

    let private W n loc pri fmt = warnings.log L.nwarn n loc pri fmt

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

    let unquantified_variables_in_type loc t =
        W 14 loc Low "type expression has unquantified type variables: %O" t


[< RequireQualifiedAccess >]
module Hint =

    let private H n loc pri fmt = hints.log L.nhint n loc pri fmt

    let unsolvable_constraint loc x t cx ct αs = 
        H 1 loc High "constraint `%s : %O` is unsolvable because type variables %s do not appear in %O : %O. This prevents automatic resolution to determine instances, therefore \
        manual resolution will be needed for evaluating a ground value"
            cx ct (flatten_stringables ", " αs) x t

    // TODO: is this hint message really not necessary anymore?
    let manually_resolved_symbol_refers_to_mupliple_constraints loc x t cs =
        H 2 loc Low "symbol `%O : %O` specified in manual resolution refers to multiple constraints sharing the same name. \
        Unification with user-specified type %O will apply in unpredictable order, possibly preventing the desired resolution to take place. \
        In case of undesired results, consider manually reordering resolved symbols or redesigning code in such a way that multiple occurrences are no more an issue.\n\
        Current constraints are:\n%O"
            x t t (mappen_strings (fun (x, t) -> sprintf "   %O : %O" x t) "\n" cs)

    let datacons_contains_env_fv loc c x tx =
        H 3 loc Normal "datatype %s defines a data constructor %s whose type %O has type variables that cannot be generalized" c x tx

    let scoped_vars_wont_be_generalized loc what scoped_vars =
        H 4 loc Min "scoped %s variable%s %s won't be generalized" what (if Seq.length scoped_vars > 1 then "s" else "") (flatten_stringables ", " scoped_vars)

    let auto_generalization_occurred loc t t' =
        H 5 loc Low "type annotation %O has been automatically generalized to %O" t t'

    // TODO: this might become a warning that could be avoided by using a special instantiation operator ":>"
    let type_annotation_is_instantiation loc tann ϕinf =
        H 6 loc High "type annotation %O is an instance of the inferred type %O, which is more generic. \
        This is a loss of type information: additional type annotations may be needed to make further code work in relation to this, \
        or it may prevent first-class polymorphic uses"
            tann ϕinf
