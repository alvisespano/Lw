(*
 * Lw
 * Config.fs: static configuration
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.Config

open System
open Printf
open Lw.Core.Absyn
open Lw.Core.Absyn.Misc
open Lw.Core.Absyn.Var
open Lw.Core.Absyn.Kind
open Lw.Core.Absyn.Sugar
open Lw.Core.Absyn.Ast
open FSharp.Common

(* -- Compilation Switches --
 *
 * Can be activated in the project panel as compilation symbols.
 *
 * DEBUG_INTRINSICS         // don't turn off log when typing intrinsics 
 *)

[<Measure>] type sec

type mode = Mode_Interpreter | Mode_Console | Mode_UnitTest

let mutable mode = Mode_Interpreter

module Console =
    let prompt = ">"
    let pretty_prompt_decl x σ v = sprintf "%s : %O = %O" x σ v
    let pretty_prompt_expr σ v = pretty_prompt_decl "_" σ v
    let watchdog_interval = 5.0<sec>
    let pretty_closure_max_length = 30
    let pretty_expr (e : expr) = truncate_string_with_ellipsis pretty_closure_max_length e.pretty
    let pretty_closure (x, e, _) = sprintf "| fun %s -> %s |" x (pretty_expr e)
    let pretty_rec_closure (x, e, _) = sprintf "| rec fun %s -> %s |" x (pretty_expr e)

module UnitTest =
    let multiple_results_item_fmt : StringFormat<_> = "%d"


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

    let cfg = Lw.Core.Config.Log.cfg
    
    module Presets =

        let set_thresholds_for_console () =
            cfg.debug_threshold <- Normal
            #if DEBUG
            cfg.msg_threshold <- Low
            #else
            cfg.msg_threshold <- Normal
            #endif
            cfg.warn_threshold <- Min
            cfg.hint_threshold <- Min

        let set_thresholds_for_unit_test () =
            #if DEBUG
            cfg.debug_threshold <- Normal
            cfg.msg_threshold <- Normal
            cfg.warn_threshold <- Min
            cfg.hint_threshold <- Min
            #else
            cfg.debug_threshold <- Unmaskerable
            cfg.msg_threshold <- High
            cfg.warn_threshold <- Min
            cfg.hint_threshold <- Normal
            #endif

        let set_thresholds_for_interpreter () =
            #if DEBUG
            cfg.all_thresholds <- Min
            #else
            cfg.debug_threshold <- Unmaskerable
            cfg.msg_threshold <- High
            cfg.warn_threshold <- Low
            cfg.hint_threshold <- Normal
            #endif

        let set_thresholds_for_intrinsics () =
            #if DEBUG_INTRINSICS
            cfg.all_thresholds <- Min
            #else
            cfg.debug_threshold <- Unmaskerable
            cfg.msg_threshold <- Unmaskerable
            cfg.warn_threshold <- Unmaskerable
            cfg.hint_threshold <- Unmaskerable
            #endif
