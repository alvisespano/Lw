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
    "Temp1", [ShowSuccessful; Verbose; ShowHints; ShowWarnings],
    [
    "let id x = x",                                         typed_ok_as "'a -> 'a"
    "let id : 'a -> 'a = id in id 1, id true",              wrong_type
    "let id : forall 'a. 'a -> 'a = id in id 1, id true",   typed_ok_as_ "int * bool" [Unbind]
    "let id : 'a -> 'a = id in id",                         typed_ok_as_ "'a -> 'a" [NoAutoGen]
    ]

let all : section list =
    [
    [temp1]
//    Other.all   // misc custom tests for non-language bits
//    TypeEquivalence.all
//    Basic.all   // needed as they introduce some basic bindings
//    HML.all
    ] |> List.concat
    
