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
    "Temp1", [flag.ShowSuccessful; flag.ShowInput],
    [
    "forall 'a 'b. 'a -> 'b",                   type_neq_ "forall 'a 'b. 'a -> 'c" [flag.DisableWarning 13]
    "int",                                      type_eq "int"

    "let id x = x",                             type_ok "'a -> 'a"
    "let ids = [id]",                           type_ok "forall ('a :> forall 'b. 'b -> 'b). list 'a"

    // TODO: move these to real test sections
    "let ids : list ('a -> 'a) = ids in ids",               type_ok_ "list ('a -> 'a)" [flag.NoAutoGen; flag.EnableHint 6; flag.EnableHint 4; flag.EnableWarnings]
    "let ids : list ('a -> 'a) = ids",                      type_ok_ "forall 'a. list ('a -> 'a)" [flag.Unbind; flag.EnableHints]

//    "let ids : forall 'a. list ('a -> 'a) = ids in ids",    type_ok "forall 'a. list ('a -> 'a)"
//    "let ids : list (forall 'a. 'a -> 'a) = ids in ids",    type_ok "list (forall 'a. 'a -> 'a)"
//
//    "let poly (f : forall 'a. 'a -> 'a) =
//        f 1, f true",                           type_ok "(forall 'a. 'a -> 'a) -> int * bool"
//
//    "let rec map f = function
//        | [] -> []
//        | x :: xs -> f x :: map f xs",          type_ok "('a -> 'b) -> list 'a -> list 'b"
//            
//    "let ids : list (forall 'a. 'a -> 'a) = ids
//     in
//        map poly ids",                          type_ok "list (int * bool)"
//
//    "let ids : list ('a -> 'a) = ids
//     in
//        map poly ids",                          wrong_type
//
//    "let ids : forall 'a. list ('a -> 'a) = ids
//     in
//        map poly ids",                          wrong_type
//
//    "let ids : forall ('a :> forall 'b. 'b -> 'b) . list 'a = ids
//     in
//        map poly ids",                          type_ok "list (int * bool)"
    ]

let all : section list =
    [
    Other.all
    [temp1]
//    TypeEquivalence.all
//    Basic.all   // these are needed as they introduce some basic bindings
//    HML.all
    ] |> List.concat
    
