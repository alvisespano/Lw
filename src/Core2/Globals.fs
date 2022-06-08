﻿(*
 * Lw
 * Globals.fs: global stuff
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
 
module Lw.Core.Globals

open System
open FSharp.Common
open FSharp.Common.Log
open FSharp.Text


// error exception hierarchy
//

type location = Parsing.location

type located_error (header, message, loc : location) =
    inherit Exception (message)
    member val location = loc
    member val header = header
    abstract message_parts : string list
    abstract message_body : string

    default this.message_parts = [this.location.pretty; header; this.message_body] 
    default __.message_body = message

    override this.Message = this.message_parts |> Seq.filter (function "" -> false | _ -> true) |> mappen_strings (sprintf "%O") ": " 

type numeric_error (header, msg, code : int, loc) =
    inherit located_error (header, msg, loc)
    member val code = code

type static_error (header, msg, n, loc) =
    inherit numeric_error (header, msg, n, loc)
    new (msg, n, loc) = new static_error (static_error.error_name, msg, n, loc)
    static member error_name = "static error"

type syntax_error (message, loc) =
    inherit static_error (syntax_error.error_name, message, Config.Report.syntax_error_code, loc)
    static member internal locate_from_lexbuf (lexbuf : Lexing.LexBuffer<_>) = new location (lexbuf.StartPos, lexbuf.EndPos, line_bias = 0, col_bias = 1)
    new (message, lexbuf : Lexing.LexBuffer<char>) = new syntax_error (message, syntax_error.locate_from_lexbuf lexbuf)
    static member error_name = "syntax error"

type runtime_error (header, message, loc) =
    inherit located_error (header, message, loc)
    new (msg, loc) = new runtime_error (runtime_error.error_name, msg, loc)
    static member error_name = "runtime error"


// some global errors
//

module Report =

    module Error =
        let private E (loc : location) fmt = throw_formatted (fun msg -> new syntax_error (msg, loc)) fmt
    
        let invalid_pattern_in_function_binding loc p =
            E loc "invalid pattern form for function binding: %O" p



// log and profiling
//

type TimeSpan with
    member this.pretty =
        let ms = this.TotalMilliseconds
        in
            if ms < Double.Epsilon then sprintf "%d ticks" this.Ticks
            elif ms < 1000. then sprintf "%g ms" ms
            else sprintf "%g s" (ms / 1000.)

type logger () =
    inherit Log.console_logger (Config.Log.cfg)

    let default_cont = fun () -> ()
        
    member val cont = default_cont with get, set

    override this.actually_print (header, fgcol, markso, prio, s) =
        base.actually_print (header, fgcol, markso, prio, s)
        this.cont ()
        this.cont <- default_cont

    member this.not_implemented fmt = this.log_unleveled "NOT IMPLEMENTED" Config.Log.not_implemented_color fmt
    member this.uni pri fmt = this.log_leveled "UNI" Config.Log.uni_color this.cfg.debug_threshold pri fmt
    member this.resolve pri fmt = this.log_leveled "RESOLVE" Config.Log.resolve_color this.cfg.debug_threshold pri fmt

    member this.nhint n pri fmt =
        this.cfg.hint_header <- sprintf Config.Log.hint_header_fmt n
        this.hint pri fmt

    member this.nwarn n pri fmt =
        this.cfg.warn_header <- sprintf Config.Log.warn_header_fmt n
        this.warn pri fmt
    
    member this.nerror n fmt =
        this.log_unleveled (sprintf Config.Log.error_header_fmt n) Config.Log.error_color fmt



let L = new logger ()
let null_L = new null_logger (Config.Log.cfg)


;;

// dispose logger at exit

AppDomain.CurrentDomain.ProcessExit.Add (fun _ -> L.close)
