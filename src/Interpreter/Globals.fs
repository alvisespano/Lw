(*
 * Lw Interpreter
 * Globals.fs: global stuff
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
 
module Lw.Interpreter.Globals

open Lw.Core
open Lw.Core.Globals
open System
open FSharp.Common.Prelude


// global exception handler
//

let handle_exn exit (e : exn) =
    match e with
    | :? numeric_error as e         -> L.nerror e.code "%s" e.Message; exit Config.Exit.error
    | :? located_error              -> L.fatal_error "%s" e.Message; exit Config.Exit.error
    | :? NotImplementedException    -> L.not_implemented "%s" e.Message; exit Config.Exit.not_implemented
    | Failure s                         
    | Unexpected s                  -> L.unexpected_error "%s\n%O" s e.StackTrace; exit Config.Exit.unexpected_error
    | e                             -> L.unexpected_error "uncaught exception: %s\n%O" (pretty_exn_and_inners e) e.StackTrace; exit Config.Exit.unexpected_error

let handle_exn_and_exit x = handle_exn exit x

let handle_exn_and_return x = handle_exn id x
    