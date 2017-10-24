
module Lw.Interpreter.UnitTest.Basic

open Lw.Interpreter.UnitTester
open Lw.Interpreter.UnitTester.Aux

let intrinsics : section =
    "Intrinsics", [],
    [
    "[]",                                       typed_ok_as "list 'a"
    "[1; 2]",                                   typed_ok_as "list int"
    "true 1",                                   wrong_type
    "true :: false :: true",                    wrong_type
    "'a' :: 'b' :: 'c' :: []",                  typed_ok_as "list char"
    "'a' :: 'b' :: ['c']",                      typed_ok_as "list char"
    "[true; 2]",                                wrong_type
    "(Some 0 :: [None]) :: [[Some 2]]",         typed_ok_as "list (list (option int))"
    "[None]",                                   typed_ok_as "list (option 'a)"
    "1 + 3",                                    typed_ok_as "int"
    "if 1 then () else ()",                     wrong_type
    ]

let scoping : section =
    "Scoping", [],
    [
    "let id x = x in id true",                  typed_ok_as "bool"
    "id 1",                                     unbound_error
    "let f x = x",                              typed_ok_as "'a -> 'a"
    "let g x = f x",                            typed_ok_as "'a -> 'a"
    ]

let type_annotations : section =
    "Type Annotations", [],
    [
    "fun f x y -> ((f : 'a -> 'a) x, y) : _ * int",         typed_ok_as "('a -> 'a) -> 'a -> int -> 'a * int"
    "fun f (x : 'x) y -> ((f : 'a -> _) x, y) : _ * int",   typed_ok_as "('x -> 'a) -> 'x -> int -> 'a * int"
    "fun f (x : 'b) y -> ((f : _ -> 'a) x, y) : 'a * _",    typed_ok_as "('b -> 'a) -> 'b -> 'c -> 'a * 'c"
    ]

let scoped_type_variables : section =
    "Scoped Type Variables", [HideHints],
    [ 
    "let i (x : 'bar) = x in i 1, i true, i",   wrong_type     // this is considered non-top-level also in OCaml, so no generalization
    "let y =
        let i (x : 'foo) = x
        in
            i 1, i true",                       wrong_type
    ]

let lists : section =
    "Lists", [KeepBindingsAtEnd],
    [
    "let rec map f = function
        | [] -> []
        | x :: xs -> f x :: map f xs",          typed_ok_as "('a -> 'b) -> list 'a -> list 'b"
    "let rec fold f z = function
        | [] -> z
        | x :: xs -> fold f (f z x) xs",        typed_ok_as "('b -> 'a -> 'b) -> 'b -> list 'a -> 'b"
    "let rec foldr f l z =
        match l with
        | [] -> z
        | x :: xs -> f x (foldr f xs z)",       typed_ok_as "('a -> 'b -> 'b) -> list 'a -> 'b -> 'b"
    "let rec append l1 l2 =
        match l1 with
        | [] -> l2
        | x :: xs -> x :: append xs l2",        typed_ok_as "list 'a -> list 'a -> list 'a"
    "let append1 l x = append l [x]",           typed_ok_as "list 'a -> 'a -> list 'a"
    "let single x = [x]",                       typed_ok_as "'a -> list 'a"
    ]

let hindley_milner : section =
    "Hindley-Milner", [KeepBindingsAtEnd],
    [
    "fun x -> x",                               typed_ok_as "forall 'a. 'a -> 'a"
    "fun f x -> f x",                           typed_ok_as "forall 'a 'b. ('a -> 'b) -> 'a -> 'b"
    "fun a, b -> a",                            wrong_syntax
    "let inc n = n + 1",                        typed_ok_as "int -> int"
    "inc true",                                 wrong_type
    "let i = fun x -> x in i i",                typed_ok_as "forall 'a. 'a -> 'a"
    "fun i -> i i",                             type_errn 203
    "fun i -> (i 1, i true)",                   type_errn 200
    "let app f x = f x",                        typed_ok_as "('a -> 'b) -> 'a -> 'b"
    "let revapp x f = f x",                     typed_ok_as "'a -> ('a -> 'b) -> 'b"
    "let poly f = f 1, f true",                 wrong_type
    "let rec map f = function
            | [] -> []
            | x :: xs -> f x :: map2 f xs
     and map2 = id map
     and id x = x
     in
         id",                                   typed_ok_as "(('a -> 'b) -> list 'a -> list 'b) -> ('a -> 'b) -> list 'a -> list 'b"
    "map2",                                     unbound_error        
    "let id x = x",                             typed_ok_as "forall 'a. 'a -> 'a"
    ]


let all : section list =
    [
    intrinsics
    scoping
    type_annotations
    scoped_type_variables
    lists
    hindley_milner
    ]

