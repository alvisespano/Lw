(*
 * Lw
 * UnitTest/Main.fs: unit test entrypoint
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.UnitTest.All

open Lw.Interpreter.UnitTester
open Lw.Interpreter.UnitTester.Aux

// just for testing and comparing with F#
module private InFSharp =
    let rec foldr f l z =
        match l with
        | [] -> z
        | x :: xs -> f x (foldr f xs z)


let temp1 : section =
    "Temp1", [ShowSuccessful; Verbose; ShowHints; ShowWarnings; Dependencies (Basic.all @ [HML.defs])],
    [
    "let ids = [id]",                               typed_ok

    "let ids : forall 'a. list ('a -> 'a) = ids
     in
        map poly ids",                              wrong_type_ [ShowHint 12]
    ]

let all : section list =
    [
//    [temp1]
    Other.all   // misc custom tests for non-language bits
    TypeEquivalence.all
    Basic.all   // needed as they introduce some basic bindings
    HML.all
    ] |> List.concat
    
