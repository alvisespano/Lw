(*
 * Lw
 * Globals.fs: global stuff
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
 
module Lw.Core.Globals

open System
open FSharp.Common
open FSharp.Common.Log

open Microsoft.FSharp.Text


// error exception hierarchy
//

type location = Parsing.location
//    inherit Parsing.location
//    new (filename : string, line : int, col : int, ?end_line : int, ?end_col : int, ?line_bias : int, ?col_bias : int) =
//        { inherit Parsing.location (filename, line, col, ?end_line = end_line, ?end_col = end_col, ?line_bias = line_bias, ?col_bias = col_bias) }
//
//    new (p1, ?p2, ?line_bias, ?col_bias) =
//        { inherit Parsing.location (p1, ?p2 = p2, ?line_bias = line_bias, ?col_bias = col_bias) }
//
//    new () = { inherit Parsing.location () }


type located_error (header, message, loc : location) =
    inherit Exception (message)
    member val location = loc
    member val header = header
    abstract message_parts : string list
    abstract message_body : string

    default this.message_parts = [this.location.pretty; header; this.message_body] 
    default this.message_body = message

    override this.Message = this.message_parts |> Seq.filter (function "" -> false | _ -> true) |> mappen_strings (sprintf "%O") ": " 


type static_error (header, msg, loc) =
    inherit located_error (header, msg, loc)

type runtime_error (header, message, loc) =
    inherit located_error (header, message, loc)

type syntax_error (message, loc) =
    inherit static_error ("syntax error", message, loc)

    static member internal locate_from_lexbuf (lexbuf : Lexing.LexBuffer<_>) =
        new location (lexbuf.StartPos, lexbuf.EndPos, line_bias = 0, col_bias = 1)

    new (message, lexbuf : Lexing.LexBuffer<char>) =
        new syntax_error (message, syntax_error.locate_from_lexbuf lexbuf)

type static_numeric_error (header, msg, n : int, loc) =
    inherit static_error (header, msg, loc)
    member val code = n




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

    member this.not_implemented fmt = this.custom_error Config.Log.not_implemented_color "NOT IMPLEMENTED" fmt
    member this.uni pri fmt = this.custom_debug Config.Log.uni_color "UNI" pri fmt
    member this.resolve pri fmt = this.custom_debug Config.Log.resolve_color "RESOLVE" pri fmt
    member this.test pri fmt = this.custom Config.Log.test_color "TEST" Config.Log.cfg.test_threshold pri fmt

    member this.nhint n pri fmt =
        this.cfg.hint_header <- Some (sprintf Config.Log.hint_header_fmt n)
        this.hint pri fmt

    member this.nwarn n pri fmt =
        this.cfg.warn_header <- Some (sprintf Config.Log.warn_header_fmt n)
        this.warn pri fmt
    
    member this.nerror n fmt =
        this.custom_error Config.Log.error_color (sprintf Config.Log.error_header_fmt n) fmt


let L = new logger ()
let null_L = new null_logger (Config.Log.cfg)

;;

// dispose logger at exit

AppDomain.CurrentDomain.ProcessExit.Add (fun _ -> L.close)
