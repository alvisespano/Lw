(*
 * Lw
 * Main.fs: type checker
 * (C) 2000-2014 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.Main

open System
open FSharp.Common.Prelude
open FSharp.Common.Log
open FSharp.Common
open Lw.Core
open Lw.Core.Globals
open Lw.Core.Typing.Defs
open System.Threading
open System.Diagnostics

module A = Lw.Core.Absyn

// workaround for preventing a bug on the event handler add/remove system: dummy handler that won't be removed for the whole application life-cycle
// for details see [http://stackoverflow.com/questions/22714211/removing-console-cancelkeypress-handler-once-disables-any-future-handling]
Console.CancelKeyPress.AddHandler (fun _ _ -> ())

let typecheck_prg (envs : Intrinsic.envs) prg =
    let st = { Typing.StateMonad.state.empty with Γ = envs.Γ; γ = envs.γ }
    let (), st = Typing.Inference.pt_program prg st
    in
        { envs with Γ = st.Γ; γ = st.γ; δ = st.δ }

let eval_prg (envs : Intrinsic.envs) prg =
    let Δ, vo = Eval.eval_prg Eval.context.non_cancellable envs.Δ prg
    in
        { envs with Δ = Δ }, vo


// source file interpreter
//

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

let handle_exn : exn -> _  =
    let r code =
        #if DEBUG
        Diagnostics.Debugger.Break ()
        #endif
        code
    function
    | :? Typing.Report.numeric_error as e   -> L.nerror e.code "%s" e.Message; Config.Exit.error
    | :? Parsing.located_error as e         -> L.fatal_error "%s" e.Message; Config.Exit.error
    | :? NotImplementedException as e       -> L.not_implemented "%s" e.Message; r Config.Exit.not_implemented
    | Failure s                         
    | Unexpected s as e                     -> L.unexpected_error "%s\n%O" s e.StackTrace; r Config.Exit.unexpected_error
    | e                                     -> L.unexpected_error "uncaught exception: %s\n%O" (pretty_exn_and_inners e) e.StackTrace; r Config.Exit.unexpected_error


// interactive console
//

let print_env_diffs (Γ1 : jenv) Γ2 (Δ1 : Eval.env) Δ2 =
    for (_, { jenv_value.scheme = σ }), (x, v) in Seq.zip (Γ2 - Γ1) (Δ2 - Δ1) do
        L.print_line (Config.Interactive.pretty_prompt_decl x σ v)

let print_decl_bindings (Γ : jenv) (Δ : Eval.env) d =
    for x in Typing.Utils.vars_in_decl d do
        let σ = Γ.lookup (Jk_Var x)
        let v = Δ.lookup x
        L.print_line (Config.Interactive.pretty_prompt_decl x σ v)

let interactive (envs : Intrinsic.envs) =
    print_env_diffs Intrinsic.envs0.Γ envs.Γ Intrinsic.envs0.Δ envs.Δ
    L.msg Low "entering interactive mode"

    let default_ctrl_c_handler = new ConsoleCancelEventHandler (fun _ args ->
        L.msg Unmaskerable "CTRL-C signal intercepted: forcing interactive exit"
        exit Config.Exit.ctrl_c)
    Console.CancelKeyPress.AddHandler default_ctrl_c_handler

    let rΔ = ref envs.Δ
    let st = ref { Typing.StateMonad.state.empty with Γ = envs.Γ; γ = envs.γ }
    let unM f x =
        let ctx = Typing.StateMonad.context.top_level
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
                    let t, tspan = cputime (unM Typing.Inference.pt_expr) e
                    let v, vspan = W Eval.eval_expr e
                    L.print_line (Config.Interactive.pretty_prompt_expr t v)
                    tspan, vspan

                | A.Line_Decl d ->
                    let (), tspan = cputime (unM Typing.Inference.pt_decl) d
                    let Δ', vspan = W Eval.eval_decl d
                    let Γ' = (!st).Γ
                    rΔ := Δ'
                    print_decl_bindings Γ' Δ' d
                    tspan, vspan
            let s = sprintf "-- typing %s / eval %s --" tspan.pretty vspan.pretty
            L.print_line (sprintf "%s%s" (new String (' ', Console.BufferWidth - s.Length)) s)

        with :? OperationCanceledException -> ()
           | e                             -> ignore <| handle_exn e



[<EntryPoint>]
let main _ =
    let code =      
        try
            Lw.Interpreter.Args.parse ()
            #if RELEASE
            #else
            L.msg Low "%s" (Args.credits ())
            L.debug Min "CWD: %s" System.Environment.CurrentDirectory
            #endif
            #if UNIT_TEST
            UnitTest.main ()
            #else
            if Config.Interactive.interactive_mode then
                Config.Log.set_thresholds_for_interactive ()
            let envs = ref Intrinsic.envs0
            if not (String.IsNullOrWhiteSpace Args.filename) then
                envs := interpret !envs Args.filename
            if Config.Interactive.interactive_mode then
                interactive !envs
            0
            #endif
        with e -> handle_exn e

    #if WAIT_FOR_KEY_AT_EXIT
    printfn "\n\npress any key to exit...\n"
    ignore <| System.Console.ReadKey ()
    #endif
    code