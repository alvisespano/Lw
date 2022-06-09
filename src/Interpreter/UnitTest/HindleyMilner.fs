
module Lw.Interpreter.UnitTest.HindleyMilner

open Lw.Interpreter.UnitTester
open Lw.Interpreter.UnitTester.Aux

module Code = Lw.Core.Typing.Report.Error.Code


let misc =
    { name = "Hindley-Milner"
      flags = [KeepAllBindings]
      entries = [
        "fun x -> x",                               typed_ok_as "forall 'a. 'a -> 'a"
        "fun f x -> f x",                           typed_ok_as "forall 'a 'b. ('a -> 'b) -> 'a -> 'b"
        "fun a, b -> a",                            wrong_syntax
        "let inc n = n + 1",                        typed_ok_as "int -> int"
        "inc true",                                 wrong_type
        "let i = fun x -> x in i i",                typed_ok_as "forall 'a. 'a -> 'a"
        "fun i -> i i",                             type_errn Code.type_circularity
        "fun i -> (i 1, i true)",                   type_errn Code.unification_mismatch
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
        "map2",                                     unbound_symbol_error        
        "let id x = x",                             typed_ok_as "forall 'a. 'a -> 'a"
        ]
    }

// taken from: https://github.com/aedans/Hindley-Milner/blob/master/src/test/kotlin/io/github/aedans/hm/HindleyMilnerTest.kt
let aedans =
    { name = "Hindley-Milner Aedans"
      flags = []
      entries = [
        "λx -> true",                               typed_ok_as "a -> bool"
        "fun x -> fun y -> true",                   typed_ok_as "a -> b -> bool"
        "fun x -> x",                               typed_ok_as "a -> a"

        "fun x -> fun y -> x y",                    typed_ok_as "a -> b -> a -> b"
        "fun x -> fun y -> fun z -> x y z",         typed_ok_as "(a -> b) -> (b -> c) -> b -> c"
        "fun x -> x true",                          typed_ok_as "(bool -> a) -> a"
        "(fun x -> x true",                         typed_ok_as "bool"

        "fun x -> x x",                             type_errn Code.type_circularity

        "if true then true else true",              typed_ok_as "bool"
        "fun x -> if x then true else x",           typed_ok_as "bool -> bool"
        "fun x -> if x then x else x",              typed_ok_as "bool -> bool"
        "fun x -> fun y -> if x then y else x",     typed_ok_as "bool -> bool -> bool"
        "fun x -> fun y -> fun z ->
            if x then y else z",                    typed_ok_as "bool -> a -> a -> a"
        "fun x -> if x then x else (x true)",       wrong_type  // UnableToUnify
        ]
    }


let all : section list =
    [
    misc
    aedans
    ]