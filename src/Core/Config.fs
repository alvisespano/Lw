(*
 * Lw
 * Config.fs: static configuration
 * (C) 2000-2014 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Config

open System
open Printf
open FSharp.Common.Prelude

(* -- Compilation Switches --
 *
 * Activate them in the project panel as compilation symbols.
 * Mind that logger special methods such as .mgu and .resolve are independent from these.
 *
 * DEBUG_TYVARS
 * DEBUG_MGU
 * DEBUG_CONSTRAINTS
 * DEBUG_PERF
 * DEBUG_RESOLVE
 *)

module Typing =
    let negate_symbol = "neg"

    let list_nil = "Nil"
    let list_cons = "Cons"

    module TyCons =
        let row_special_char = '|'

        module Rows =
            let record = "Record"
            let variant = "Variant"

    module KindCons =    
        let row = "Row"
        let htuple = "HTuple"

module Printing =

    // dynamic configuration

    type cfg () =
        let mutable greek_tyvars_ = false

        member __.unicode
            with get () = Console.OutputEncoding = Text.Encoding.Unicode
            and set b =
                match b with
                | true  -> Console.OutputEncoding <- Text.Encoding.Unicode
                | false -> Console.OutputEncoding <- Text.Encoding.ASCII

        member this.greek_tyvars
            with get () = greek_tyvars_
            and set b =
                match b with
                | true  -> this.unicode <- true
                           greek_tyvars_ <- true
                | false -> greek_tyvars_ <- false

        member this.forall = if this.unicode then "∀" else "forall "

        member this.tyvar_range = if this.greek_tyvars then 'α', 'ζ' else 'a', 'z'
        member this.tyvar_quantified_fmt : Printf.StringFormat<_> = if this.greek_tyvars then "%s" else "'%s"
        member this.tyvar_unquantified_fmt : Printf.StringFormat<_> = if this.greek_tyvars then "?%s" else "'_%s"

    let dynamic = new cfg ()

    // static configuration bindings

    let sep_in_forall = ", "
    let openworld_overload_constraint_fmt : StringFormat<string -> string> = "%s"
    let closedworld_overload_constraint_fmt : StringFormat<string -> string> = "!%s"
    let freevar_fmt : StringFormat<string -> string> = "'%s"
    let freevar_constraint_fmt = freevar_fmt
    let polycons_fmt : StringFormat<string -> string> = "`%s"
    let jk_inst_fmt : StringFormat<string -> int -> string> = "%s$%X"
    let cid_fmt : StringFormat<string -> int -> string> = "%s#%X"
    let fresh_reserved_id_fmt : StringFormat<int -> string> = "$%d"
    let wildcard_reserved_fmt : StringFormat<int -> string> = "_$%d"
    let tuple_index_label_fmt : StringFormat<int -> string> = "#%d"

    module Prompt =
        let prefix_sep = " "
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

    type config () =
        inherit FSharp.Common.Log.config ()
        member val test_threshold = Min with get, set
        override this.all_thresholds
            with set lv =
                base.all_thresholds <- lv
                this.test_threshold <- lv

    let cfg =
        let l = new config ()
        l.show_priority <- false
        l.show_datetime <- false
        l.show_urgency <- false
        l.show_thread <- true
        #if DEBUG
        l.all_thresholds <- Min
        #else
        #if RELEASE
        l.debug_threshold <- Unmaskerable
        l.msg_threshold <- High
        l.warn_threshold <- Low
        l.hint_threshold <- Normal
        #else
        #if TEST_PERFORMANCE
        l.debug_threshold <- Unmaskerable
        l.msg_threshold <- Normal
        l.warn_threshold <- Low
        l.hint_threshold <- Low
        #else
        #if TEST_FEATURES
        l.debug_threshold <- Low
        l.msg_threshold <- Low
        l.warn_threshold <- Min
        l.hint_threshold <- Min
        #endif
        #endif
        #endif
        #endif
        l

    let verbose_pretty_location = false
    let not_implemented_color = ConsoleColor.DarkRed
    let mgu_color = ConsoleColor.Blue
    let test_color = ConsoleColor.Yellow
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

