(*
 * Lw
 * UnitTest/Main.fs: unit test entrypoint
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.UnitTest.Main

open Lw.Interpreter.UnitTest.Engine

module private InFSharp =
    let rec foldr f l z =
        match l with
        | [] -> z
        | x :: xs -> f x (foldr f xs z)


open Lw.Interpreter.UnitTest.TypeEquality
open Lw.Interpreter.UnitTest.Basic
open Lw.Interpreter.UnitTest.HML


let all : section list =
    [
    type_equality
//        intrinsics
//        scoping
//        type_annotations
//        scoped_type_variables
//        lists
//        hindley_milner
//        hml
//        higher_rank
    ]
    
let main () =
    test_sections all




