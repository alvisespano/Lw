(*
 * Lw
 * Globals.fs: global stuff
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
 
module Lw.Core.Globals

open System
open FSharp.Common
open FSharp.Common.Log
open FSharp.Common.Prelude

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
