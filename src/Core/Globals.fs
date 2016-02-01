(*
 * Lw
 * Globals.fs: global stuff
 * (C) 2000-2014 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
 
module Lw.Core.Globals

open System
open FSharp.Common
open FSharp.Common.Log
open FSharp.Common.Prelude
open Lw.Core.Absyn

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
    member this.mgu fmt = this.custom_debug Config.Log.mgu_color "MGU" Min fmt
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

    member this.cputime name f x =
        let r, span = cputime f x
        #if DEBUG_PERF
        this.perf Normal "[%s] CPU time = %s" name span.pretty
        #endif
        r

    member this.best_cputime name1 name2 f1 f2 =
        let r1, t1 = cputime f1 ()
        let r2, t2 = cputime f2 ()
        let name1, t1, r1, name2, t2, r2 = if t1 < t2 then name1, t1, r1, name2, t2, r2 else name2, t2, r2, name1, t1, r1
        #if DEBUG_PERF
        this.perf Normal "[%s] faster than [%s] by CPU time = %s" name1 name2 ((t2 - t1).pretty)
        #endif
        r1

let L = new logger ()
let null_L = new null_logger (Config.Log.cfg)

;;

// dispose logger at exit

AppDomain.CurrentDomain.ProcessExit.Add (fun _ -> L.close)
