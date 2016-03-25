
module Lw.Interpreter.UnitTest.Basic

open Lw.Interpreter.UnitTest.Engine.Tests

let intrinsics =
    "Intrinsics",
    [
    "[]",                                       type_ok "list 'a"
    "[1; 2]",                                   type_ok "list int"
    "true 1",                                   wrong_type
    "true :: false :: true",                    wrong_type
    "'a' :: 'b' :: 'c' :: []",                  type_ok "list char"
    "'a' :: 'b' :: ['c']",                      type_ok "list char"
    "[true; 2]",                                wrong_type
    "(Some 0 :: [None]) :: [[Some 2]]",         type_ok "list (list (option int))"
    "[None]",                                   type_ok "list (option 'a)"
    "1 + 3",                                    type_ok "int"
    "if 1 then () else ()",                     wrong_type
    ]

let scoping =
    "Scoping",
    [
    "let id x = x in id true",                  type_ok "bool"
    "id 1",                                     unbound_error
    ]

let type_annotations =
    "Type Annotations",
    [
    "fun f x y -> ((f : 'a -> 'a) x, y) : _ * int",         type_ok "('a -> 'a) -> 'a -> int -> 'a * int"
    "fun f (x : 'x) y -> ((f : 'a -> _) x, y) : _ * int",   type_ok "('x -> 'a) -> 'x -> int -> 'a * int"
    "fun f (x : 'b) y -> ((f : _ -> 'a) x, y) : 'a * _",    type_ok "('b -> 'a) -> 'b -> 'c -> 'a * 'c"
    ]

let scoped_type_variables =
    "Scoped Type Variables",
    [
    "let i (x : 'bar) = x in i 1, i true, i",   wrong_type  // this is considered non-top-level also in OCaml, so no generalization
    "let y =
        let i (x : 'foo) = x
        in
            i 1, i true",                       wrong_type
    ]

let lists =
    "Lists",
    [
    "let rec map f = function
        | [] -> []
        | x :: xs -> f x :: map f xs",          type_ok "('a -> 'b) -> list 'a -> list 'b"
    "let rec fold f z = function
        | [] -> z
        | x :: xs -> fold f (f z x) xs",        type_ok "('b -> 'a -> 'b) -> 'b -> list 'a -> 'b"
    "let rec foldr f l z =
        match l with
        | [] -> z
        | x :: xs -> f x (foldr f xs z)",       type_ok "('a -> 'b -> 'b) -> list 'a -> 'b -> 'b"
    "let rec append l1 l2 =
        match l1 with
        | [] -> l2
        | x :: xs -> x :: append xs l2",        type_ok "list 'a -> list 'a -> list 'a"
    "let append1 l x = append l [x]",           type_ok "list 'a -> 'a -> list 'a"
    "let single x = [x]",                       type_ok "forall 'a. 'a -> list 'a"
    ]

let hindley_milner =
    "Hindley-Milner",
    [
    "fun x -> x",                               type_ok "forall 'a. 'a -> 'a"
    "fun f x -> f x",                           type_ok "forall 'a 'b. ('a -> 'b) -> 'a -> 'b"
    "fun a, b -> a",                            wrong_syntax
    "let inc n = n + 1",                        type_ok "int -> int"
    "inc true",                                 wrong_type
    "let i = fun x -> x in i i",                type_ok "forall 'a. 'a -> 'a"
    "fun i -> i i",                             type_errn 203
    "fun i -> (i 1, i true)",                   type_errn 200
    "let id x = x",                             type_ok "forall 'a. 'a -> 'a"
    "let app f x = f x",                        type_ok "('a -> 'b) -> 'a -> 'b"
    "let revapp x f = f x",                     type_ok "'a -> ('a -> 'b) -> 'b"
    "let poly f = f 1, f true",                 wrong_type
    "let rec map f = function
            | [] -> []
            | x :: xs -> f x :: map2 f xs
        and map2 = id map
        and id x = x
        in
            id",                                   type_ok "(('a -> 'b) -> list 'a -> list 'b) -> ('a -> 'b) -> list 'a -> list 'b"
    "map2",                                     unbound_error        
    ]


let all =
    [
    intrinsics
    scoping
    type_annotations
    scoped_type_variables
    lists
    hindley_milner
    ]

