(*
 * Lw
 * UnitTest/Main.fs: unit test entrypoint
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.UnitTest.All

open Lw.Interpreter.UnitTest
open Lw.Interpreter.UnitTester

// just for testing and comparing with F#
module private InFSharp =
    let rec foldr f l z =
        match l with
        | [] -> z
        | x :: xs -> f x (foldr f xs z)



let all : section list =
    [
    TypeEquivalence.all
    Basic.all
    HML.all
    ] |> List.concat
    
