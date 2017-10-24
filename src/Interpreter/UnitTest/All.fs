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

    "forall ('b :> forall 'b. 'b -> 'b). forall 'a. 'a -> 'b",                              type_eq "forall ('b :> forall 'b. 'b -> 'b). forall 'a. ('a -> 'b)"
    "forall ('b :> forall 'b. 'b -> 'b). forall 'a. 'a -> 'b",                              type_neq "forall ('b :> forall 'b. 'b -> 'b). (forall 'a. 'a) -> 'b"


//    "let ids = [id]",                               typed_ok
//
//    "let ids : forall 'a. list ('a -> 'a) = ids
//     in
//        map poly ids",                              wrong_type_ [ShowHint 123]
    ]

let all : section list =
    [
    [temp1]
    Custom.all      
    TypeEquivalence.all
    Basic.all  
    Records.all
    HML.all
    ] |> List.concat
    
