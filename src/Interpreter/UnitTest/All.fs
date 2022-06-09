(*
 * Lw
 * UnitTest/Main.fs: unit test entrypoint
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.UnitTest.All

open Lw.Interpreter.UnitTester


let all : section list =
    [
    Custom.all   // custom tests for stuff that is not the language, e.g. internal algorithms etc.
    TypeEquivalence.all
    Basic.all   // needed as they introduce some basic bindings
    HML.all
    Records.all
    ] |> List.concat
    
