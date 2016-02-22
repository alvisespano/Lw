(*
 * Lw
 * Interactive.fs: interactive console
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.Interactive

open System
open System.Threading
open System.Diagnostics
open Lw.Core
open Lw.Core.Globals
open Lw.Interpreter.Intrinsic
open Lw.Core.Typing.Defs
open FSharp.Common.Prelude
open FSharp.Common.Log
open FSharp.Common


module A = Lw.Core.Absyn

let handle_exn : exn -> _  =
    let r code =
//        #if DEBUG
//        Diagnostics.Debugger.Break ()
//        #endif
        code
    function
    | :? Typing.Report.numeric_error as e   -> L.nerror e.code "%s" e.Message; Config.Exit.error
    | :? Parsing.located_error as e         -> L.fatal_error "%s" e.Message; Config.Exit.error
    | :? NotImplementedException as e       -> L.not_implemented "%s" e.Message; r Config.Exit.not_implemented
    | Failure s                         
    | Unexpected s as e                     -> L.unexpected_error "%s\n%O" s e.StackTrace; r Config.Exit.unexpected_error
    | e                                     -> L.unexpected_error "uncaught exception: %s\n%O" (pretty_exn_and_inners e) e.StackTrace; r Config.Exit.unexpected_error


let print_env_diffs (Γ1 : jenv) Γ2 (Δ1 : Eval.env) Δ2 =
    for (_, { jenv_value.scheme = σ }), (x, v) in Seq.zip (Γ2 - Γ1) (Δ2 - Δ1) do
        L.print_line (Config.Interactive.pretty_prompt_decl x σ v)

let print_decl_bindings (Γ : jenv) (Δ : Eval.env) d =
    for x in Typing.Ops.vars_in_decl d do
        let σ = Γ.lookup (Jk_Var x)
        let v = Δ.lookup x
        L.print_line (Config.Interactive.pretty_prompt_decl x σ v)

let read_and_interpret_loop (envs : Intrinsic.envs) =
    print_env_diffs Intrinsic.envs.envs0.Γ envs.Γ Intrinsic.envs.envs0.Δ envs.Δ
    L.msg Low "entering interactive mode"

    let default_ctrl_c_handler = new ConsoleCancelEventHandler (fun _ _ ->
        L.msg Unmaskerable "CTRL-C signal intercepted: forcing interactive exit"
        exit Config.Exit.ctrl_c)
    Console.CancelKeyPress.AddHandler default_ctrl_c_handler

    let rΔ = ref envs.Δ
    let st = ref { Typing.StateMonad.state.empty with Γ = envs.Γ; γ = envs.γ }
    let unM f x =
        let ctx = Typing.Defs.context.top_level
        let r, st' = f ctx x !st
        st := st'
        r

    let watchdog f =
        use cancellation_source = new CancellationTokenSource ()
        let eval_ctrl_c_handler =  new ConsoleCancelEventHandler (fun _ args ->
                L.msg Normal "CTRL-C signal intercepted: interrupting current evaluation"
                args.Cancel <- true
                cancellation_source.Cancel ())
        Console.CancelKeyPress.RemoveHandler default_ctrl_c_handler
        Console.CancelKeyPress.AddHandler eval_ctrl_c_handler
        let watcher =
            async {
                let p = Process.GetCurrentProcess ()
                while true do
                    do! Async.Sleep (int <| Config.Interactive.watchdog_interval * 1000.0)
                    L.hint High "evaluation is in progress (cpu time: %s)..." p.UserProcessorTime.pretty
            }
        async {
            try
                Async.Start (watcher, cancellation_source.Token)
                return f cancellation_source.Token
            finally
                cancellation_source.Cancel ()
                Console.CancelKeyPress.RemoveHandler eval_ctrl_c_handler
                Console.CancelKeyPress.AddHandler default_ctrl_c_handler
        } |> Async.RunSynchronously


    while true do
        try
            L.locked_apply <| fun () ->
                printf "\n%s " Config.Interactive.prompt
                stdout.Flush ()
            let W f e = watchdog (fun c -> cputime (f { Eval.context.cancellation_token = c } !rΔ) e)
            let tspan, vspan =
                match Parsing.parse_line stdin "STDIN" with
                | A.Line_Expr e ->
                    let t, tspan = cputime (unM Typing.Inference.W_expr) e
                    let v, vspan = W Eval.eval_expr e
                    L.print_line (Config.Interactive.pretty_prompt_expr t v)
                    tspan, vspan

                | A.Line_Decl d ->
                    let (), tspan = cputime (unM Typing.Inference.W_decl) d
                    let Δ', vspan = W Eval.eval_decl d
                    let Γ' = (!st).Γ
                    rΔ := Δ'
                    print_decl_bindings Γ' Δ' d
                    tspan, vspan
            let s = sprintf "-- typing %s / eval %s --" tspan.pretty vspan.pretty
            L.print_line (sprintf "%s%s" (spaces (Console.BufferWidth - s.Length)) s)

        with :? OperationCanceledException -> ()
           | e                             -> ignore <| handle_exn e


