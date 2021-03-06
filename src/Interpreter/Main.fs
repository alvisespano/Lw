﻿(*
 * Lw
 * Main.fs: type checker
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.Main

open System
open FSharp.Common.Log
open FSharp.Common
open Lw.Core
open Lw.Core.Globals
open Lw.Interpreter.Intrinsic
open Lw.Interpreter.Globals


// workaround for preventing a bug on the event handler add/remove system: dummy handler that won't be removed for the whole application life-cycle
// for details see [http://stackoverflow.com/questions/22714211/removing-console-cancelkeypress-handler-once-disables-any-future-handling]
Console.CancelKeyPress.AddHandler (fun _ _ -> ())

let typecheck_prg (envs : Intrinsic.envs) prg =
    let st =  Typing.StateMonad.state.state0
    let (), st = Typing.Inference.W_program prg st
    in
        { envs with Γ = st.Γ; γ = st.γ; δ = st.δ }

let eval_prg (envs : Intrinsic.envs) prg =
    let Δ, vo = Eval.eval_prg Eval.context.uncancellable envs.Δ prg
    in
        { envs with Δ = Δ }, vo


// source file interpreter
//

type logger with
    member this.cputime name f x =
        let r, span = cputime f x
        #if DEBUG_PERF
        this.profile Normal "[%s] CPU time = %s" name span.pretty
        #endif
        r

    member this.best_cputime name1 name2 f1 f2 =
        let r1, t1 = cputime f1 ()
        let r2, t2 = cputime f2 ()
        let name1, t1, r1, name2, t2, r2 = if t1 < t2 then name1, t1, r1, name2, t2, r2 else name2, t2, r2, name1, t1, r1
        #if DEBUG_PERF
        this.profile Normal "[%s] faster than [%s] by CPU time = %s" name1 name2 ((t2 - t1).pretty)
        #endif
        r1

let interpret (envs : Intrinsic.envs) filename =
    let ctrl_c_handler = new ConsoleCancelEventHandler (fun _ args ->
        L.msg Unmaskerable "CTRL-C signal intercepted: forcing interpreter exit"
        exit Config.Exit.ctrl_c)
    Console.CancelKeyPress.AddHandler ctrl_c_handler
    let prg = Parsing.load_and_parse_program filename
    L.debug Low "input program:\n%O\n\n" prg
    let envs = L.cputime "type inference" (typecheck_prg envs) prg
    L.debug Low "translated program:\n%O\n\n" prg
    let envs, vo = L.cputime "eval" (eval_prg envs) prg
    match vo with
    | Some v -> L.msg Normal "return code = %O" v
    | None -> ()
    Console.CancelKeyPress.RemoveHandler ctrl_c_handler
    envs


[<EntryPoint>]
let main _ =
//    AppDomain.CurrentDomain.ProcessExit.Add (fun _ -> Threading.Thread.Sleep(2))
    let code =      
        try            
            Lw.Interpreter.Args.parse ()
            #if DEBUG
            L.msg Low "%s" (Args.credits ())
            L.debug Min "CWD: %s" System.Environment.CurrentDirectory
            #endif

            let mutable envs = Intrinsic.envs.envs0
            match Config.mode with
            | Config.Mode_UnitTest ->
                Config.Log.Presets.set_thresholds_for_unit_test ()
                UnitTester.test_sections_from_scratch UnitTest.All.all

            | Config.Mode_Interpreter ->
                Config.Log.Presets.set_thresholds_for_interpreter ()
                if not (String.IsNullOrWhiteSpace Args.filename) then
                    envs <- interpret envs Args.filename
                    0
                else failwith "no input source file specified"

            | Config.Mode_Console ->
                Config.Log.Presets.set_thresholds_for_console ()
                if not (String.IsNullOrWhiteSpace Args.filename) then
                    envs <- interpret envs Args.filename
                Console.read_and_eval_loop envs
                0

        with e -> handle_exn_and_return e

    exit code
