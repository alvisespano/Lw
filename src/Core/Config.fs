(*
 * Lw
 * Config.fs: static configuration
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Config

open System
open Printf

(* -- Compilation Switches --
 *
 * Can be activated in the project panel as compilation symbols.
 *
 * DEBUG_VAR_NAMES          // print var number and make it clear whether it is named or anonymous
 * DEBUG_FRESH_VARS         // log when fresh vars are created
 * DEBUG_CONSTRAINTS
 * DEBUG_PERF
 * DEBUG_RESOLVE
 * DEBUG_INFERENCE          // print debug information at the end of each rule while inferring types
 * DEBUG_BEFORE_INFERENCE   // print debug information for each expression also BEFORE typing (useful for comparing what happens at each inference step)
 * DEBUG_HML                // turn on log for functions involved into HML type inference
 * DEBUG_UNI                // turn on log in unification functions
 * DEBUG_UNI_DEEP           // log even recursive calls of unification functions
 *
 * DISABLE_VAR_NORM       // turn off variable normalization
 * DISABLE_HML_FIXES        // disable little fixes done by me
 * ENABLE_HML_OPTS          // introduce a number of (hopefully not bugged) optimizations for HML inference
 * ENFORCE_NF_IN_UNI        // force types involved into unification to normal form
 * DEFINE_K_APP             // define K_App/K_Apps active patterns for kinds, and implement K_Arrow and K_Arrows though them: this is inefficient and unnecessary unless K_App is really needed
 *)

let reserved_id_fmt : StringFormat<string -> string> = "$%s"
let reserved_id s = sprintf reserved_id_fmt s

module Typing =

    module Names =
        let int_negate = "neg"
        let float_negate = "fneg"

        module Data =
            let list_nil = reserved_id "Nil"
            let list_cons = reserved_id "Cons"
            let option_none = "None"
            let option_some = "Some"

        module Type =
            let arrow = "->"
            let unit = "unit"
            let int = "int"
            let bool = "bool"
            let float = "float"
            let string = "string"
            let char = "char"
            let option = "option"
            let list = "list"

            // TODO: should reserved ids be used for these type constructors or should they have a publicly usable name?
            module Row =
                let special_char = '|'
                let record = "Record"
                let variant = "Variant"

        module Kind =  
            let star = "*" 
            let arrow = "->"
            let row = "Row"
            let htuple = "HTuple"


module Printing =

    let unicode_encoding = Text.Encoding.Unicode

    // dynamic configuration

    type dynamic_cfg () =
        let mutable greek_tyvars_ = false

        member __.unicode
            with get () = Console.OutputEncoding = unicode_encoding
            and set b =
                match b with
                | true  -> Console.OutputEncoding <- unicode_encoding
                           Console.InputEncoding <- unicode_encoding
                | false -> Console.OutputEncoding <- Text.Encoding.ASCII
                           Console.InputEncoding <- Text.Encoding.ASCII

        member this.greek_tyvars
            with get () = greek_tyvars_
            and set b =
                match b with
                | true  -> this.unicode <- true
                           greek_tyvars_ <- true
                | false -> greek_tyvars_ <- false
                
        member this.forall = if this.unicode then "\u2200\b" else "forall"
        member this.flex_forall =
            #if DEBUG_HML
            "Forall"
            #else
            this.forall
            #endif
        member this.bottom = if this.unicode then "⏊" else "_|_"

        member this.tyvar_range = if this.greek_tyvars then 'α', 'ζ' else 'a', 'z'
        member this.tyvar_quantified_fmt : Printf.StringFormat<_> = if this.greek_tyvars then "%s" else "'%s"
        member this.tyvar_unquantified_fmt : Printf.StringFormat<_> = if this.greek_tyvars then "_%s" else "'_%s"

    let dynamic = new dynamic_cfg ()

    // static configuration bindings

    let forall_prefix_sep = " "
    let type_annotation_sep = ":"
    let kind_annotation_sep = "::"
    let var_bound_sep = ":>"
    let substitution_sep = ":="
    let openworld_overload_constraint_fmt : StringFormat<string -> string> = "%s"
    let closedworld_overload_constraint_fmt : StringFormat<string -> string> = "!%s"
    let freevar_fmt : StringFormat<string -> string> = "'%s"
    let freevar_constraint_fmt = freevar_fmt
    let polycons_fmt : StringFormat<string -> string> = "`%s"
    let jk_inst_fmt : StringFormat<string -> int -> string> = "%s$%X"
    let constraint_id_fmt : StringFormat<string -> int -> string> = "%s#%X"
    let fresh_reserved_id : StringFormat<int -> string> = "?%d"
    let tuple_index_label_fmt : StringFormat<int -> string> = "#%d"
    let already_existing_named_var_fmt : StringFormat<string -> int -> string> = "%s%d" // this is needed for disambiguating the name of a named var that already existed and whose name conflicted
    #if DEBUG_VAR_NAMES
    let anonymous_var_fmt : StringFormat<string -> int -> string> = "%s?%d"
    let named_var_fmt : StringFormat<string -> int -> string> = "<%s>?%d"
    #endif
    let empty_prefix = "()"
    let ftype_instance_of_fxty_sep = "<:"
    let type_evaluation_sep = "="
    let skolemized_tyvar_fmt : StringFormat<string -> string> = "|%s|"

    module Prompt =
        let header_sep = " "            // used as separator for let, rec, val etc. qualifiers
        let nested_decl_prefix = "let"
        let rec_prefix = "rec"
        let type_prefix = "type"
        let value_prefix = "val"
        let type_decl_prefixes = [type_prefix]
        let value_decl_prefixes = [value_prefix]
        let data_decl_prefixes = ["data"]
        let rec_type_decl_prefixes = [rec_prefix; type_prefix]
        let rec_value_decl_prefixes = [rec_prefix; value_prefix]
        let overload_decl_prefixes = ["overload"]
        let datatype_decl_prefixes = ["datatype"]

module Log =
    open FSharp.Common.Log

    let cfg =
        let l = new config ()
        l.show_priority <- false
        l.show_datetime <- false
        l.show_urgency <- false
        l.show_thread <- true
        l

    let verbose_pretty_location = false
    let not_implemented_color = ConsoleColor.DarkRed
    let uni_color = ConsoleColor.Blue
    let resolve_color = ConsoleColor.Magenta
    let error_color = cfg.fatal_error_color

    let warn_header_fmt : StringFormat<_> = "WARN:%03d"
    let hint_header_fmt : StringFormat<_> = "HINT:%03d"
    let error_header_fmt : StringFormat<_> = "ERROR:%03d"

module Parsing =
    let line_bias = 0
    let col_bias = 0
    let detailed_error_context = false

module Report = 
    let mutable disabled_warnings : int Set = Set.empty
    let mutable disabled_hints : int Set = Set.empty

