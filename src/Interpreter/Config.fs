(*
 * Lw
 * Config.fs: static configuration
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.Config

open System
open Printf
open FSharp.Common.Prelude
open Lw.Core.Absyn

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

    module Presets =
        let set_thresholds_for_interactive () =
            let l = Lw.Core.Config.Log.cfg
            l.debug_threshold <- Normal
            l.msg_threshold <- Low
            l.warn_threshold <- Min
            l.hint_threshold <- Min

        let set_thresholds_for_unit_test () =
            let l = Lw.Core.Config.Log.cfg
            l.debug_threshold <- Unmaskerable
            l.msg_threshold <- Low
            l.warn_threshold <- Min
            l.hint_threshold <- Min
