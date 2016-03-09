(*
 * Lw
 * Config.fs: static configuration
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.Config

open System
open Printf
open Lw.Core.Absyn
open FSharp.Common

(* -- Compilation Switches --
 *
 * Can be activated in the project panel as compilation symbols.
 *
 * DEBUG_INTRINSICS         // don't turn off log when typing intrinsics 
 *)

[<Measure>] type s

module Interactive =
    let mutable interactive_mode = false
    let prompt = ">"
    let pretty_prompt_decl x σ v = sprintf "%s : %O = %O" x σ v
    let pretty_prompt_expr σ v = pretty_prompt_decl "_" σ v
    let watchdog_interval = 5.0<s>
    let pretty_closure_max_length = 30
    let pretty_expr (e : expr) = truncate_string_with_ellipsis pretty_closure_max_length e.pretty
    let pretty_closure (x, e, _) = sprintf ": \\%s. %s :" x (pretty_expr e)
    let pretty_rec_closure (x, e, _) = sprintf ": __rec__ \\%s. %s :" x (pretty_expr e)

module Exit =
    let ok = 0
    let error = 1
    let unexpected_error = 2
    let ctrl_c = 3
    let not_implemented = 4
    
module Log =
    open FSharp.Common.Log

    let test_color = ConsoleColor.Blue
    let test_ok_color = ConsoleColor.Green
    let test_weak_ok_color = ConsoleColor.Yellow
    let test_failed_color = ConsoleColor.Red

    module Presets =
        let private l = Lw.Core.Config.Log.cfg

        let set_thresholds_for_interactive () =
            l.debug_threshold <- Normal
            #if DEBUG
            l.msg_threshold <- Low
            #else
            l.msg_threshold <- Normal
            #endif
            l.warn_threshold <- Min
            l.hint_threshold <- Min

        let set_thresholds_for_unit_test () =
            l.debug_threshold <- Unmaskerable
            l.msg_threshold <- High
            l.warn_threshold <- Min
            l.hint_threshold <- Min
            l.show_header_only_when_changes <- true

        let set_thresholds_for_interpreter () =
            #if DEBUG
            l.all_thresholds <- Min
            #else
            l.debug_threshold <- Unmaskerable
            l.msg_threshold <- High
            l.warn_threshold <- Low
            l.hint_threshold <- Normal
            #endif

        let set_thresholds_for_intrinsics () =
            #if DEBUG_INTRINSICS
            l.all_thresholds <- Min
            #else
            l.debug_threshold <- Unmaskerable
            l.msg_threshold <- Unmaskerable
            l.warn_threshold <- Normal
            l.hint_threshold <- Unmaskerable
            #endif

            