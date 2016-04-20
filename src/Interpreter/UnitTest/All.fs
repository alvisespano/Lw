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
//    "forall 'a ('b :> _|_). 'a -> 'b",          type_eq "forall 'a. forall 'b. 'a -> 'b"
//    "forall 'a ('b :> _|_). 'a -> 'b",          type_eq "forall 'a. forall 'b. 'a -> 'b"


    "let id x = x",                             type_ok "'a -> 'a"
    "let ids = [id]",                           type_ok "forall ('a :> forall 'b. 'b -> 'b). list 'a"
    "let ids : list ('a -> 'a) = ids in ids",   type_ok "forall 'a. list ('a -> 'a)"

    "let poly (f : forall 'a. 'a -> 'a) =
        f 1, f true",                           type_ok "(forall 'a. 'a -> 'a) -> int * bool"

    "let rec map f = function
        | [] -> []
        | x :: xs -> f x :: map f xs",          type_ok "('a -> 'b) -> list 'a -> list 'b"
            
    "let ids : list (forall 'a. 'a -> 'a) = ids
     in
        map poly ids",                          type_ok "list (int * bool)"

    // these 2 are equal thanks to automatic generalization
    "let ids : list ('a -> 'a) = ids
     in
        map poly ids",                          type_ok "list (int * bool)"

    "let ids : forall 'a. list ('a -> 'a) = ids
     in
        map poly ids",                          type_ok "list (int * bool)"

    "let ids : forall ('a :> forall 'b. 'b -> 'b) . list 'a = ids
     in
        map poly ids",                          type_ok "list (int * bool)"
    ]

let all : section list =
    [
    [temp1]
//    TypeEquivalence.all
//    Basic.all
//    HML.all
    ] |> List.concat
    
