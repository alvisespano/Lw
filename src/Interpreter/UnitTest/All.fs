(*
 * Lw
 * UnitTest/Main.fs: unit test entrypoint
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.UnitTest.All

open Lw.Interpreter.UnitTester


let all : section list =
    [
    // custom tests for stuff that is not the language, e.g. internal algorithms etc.
    //Custom.all 

    //TypeEquivalence.all

    // needed as they introduce some basic bindings

    //Basic.all 

    //HindleyMilner.all 

    //Records.all

    HML.all
    ] |> List.concat
    
