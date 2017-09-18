(*
 * Lw
 * UnitTest/Main.fs: unit test entrypoint
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.UnitTest.All

open Lw.Interpreter.UnitTester
open Lw.Interpreter.UnitTester.Aux


let temp1 : section =
    "Temp1", [ ShowSuccessful; Verbose; ShowHints; ShowWarnings; (*Dependencies (Basic.all @ [HML.defs])*) ],
    [
    "let id x = x",                                 typed_ok_ [ShowWarning 10]
    "let id x = x",                                 typed_ok_ [HideWarning 10]

//    "let ids = [id]",                               typed_ok
//
//    "let ids : forall 'a. list ('a -> 'a) = ids
//     in
//        map poly ids",                              wrong_type_ [ShowHint 123]
    ]

let all : section list =
    [
<<<<<<< HEAD
    [temp1]
    //Custom.all   // custom tests for non-in-language stuff
    //TypeEquivalence.all
    //Basic.all   // needed as they introduce some basic bindings
    //HML.all
=======
    //[temp1]
    //Other.all   // misc custom tests for non-language bits
    TypeEquivalence.all
    //Basic.all   // needed as they introduce some basic bindings
    HML.all
>>>>>>> origin/development
    //Records.all
    ] |> List.concat
    
