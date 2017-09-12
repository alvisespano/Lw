
module Lw.Interpreter.UnitTest.TypeEquivalence

open Lw.Interpreter.UnitTester
open Lw.Interpreter.UnitTester.Aux

let type_equivalence : section =
    "Type Equivalence", [],
    [
    "'a",                                       type_eq "'a"
    "'a",                                       type_eq "'b"
    "'e",                                       type_eq "'q"
    "int * int",                                type_eq "int * int"
    "int * float",                              type_eq "int * float"
    "int * float",                              type_neq "float * int"
    "int * int",                                type_neq "int * int * int"
    "int * bool",                               type_neq "int * bool * int"
    "'a * int",                                 type_eq "'a * int"
    "'a -> 'b",                                 type_neq "'a * 'b"
    "'a -> 'b",                                 type_eq "'a -> 'c"
    "'a -> 'b",                                 type_neq "'a -> 'a"
    "'c -> 'e",                                 type_eq "'a -> 'b"

    "int",                                      type_eq "int"
    "bool",                                     type_neq "string"

    "forall 'a 'b. 'a -> 'b",                   type_eq "forall 'a 'b. 'a -> 'b"
    "forall 'a 'b. 'a -> 'b",                   type_eq "forall 'a 'b. 'b -> 'a"
    "forall 'a 'b. 'a -> 'b",                   type_eq "forall 'b 'a. 'a -> 'b"
    "forall 'a 'b. 'a -> 'b",                   type_eq "forall 'b 'a. 'b -> 'a"
    "forall 'a 'b. 'a -> 'b -> 'b",             type_neq "forall 'a 'b. 'a -> 'a -> 'b"
    "forall 'a 'b. 'a -> 'b -> 'b",             type_eq "forall 'b 'a. 'a -> 'b -> 'b"
    "forall 'a 'b. 'a -> 'b -> 'b",             type_eq "forall 'b 'a. 'b -> 'a -> 'a"
    "forall 'a 'b. 'a -> 'b",                   type_neq "forall 'a. 'a -> int"
    "forall 'a 'b. 'a -> 'b",                   type_neq_ "forall 'a 'b. 'a -> 'c" [HideWarning 13]

    "forall 'a ('b :> _|_). 'a -> 'b",           type_eq "forall 'a. forall 'b. 'a -> 'b"

    "forall ('a :> forall 'b. 'b -> 'b). list 'a",                      type_eq "forall ('f :> forall 'f. 'f -> 'f). list 'f"
    "forall ('a :> forall 'b. 'b -> 'b). list 'a",                      type_eq "forall ('a :> forall 'b. 'b -> 'b). list 'a"
    "forall ('a :> forall 'b. 'b -> 'b) 'c. list ('a * 'c)",            type_eq "forall 'c ('a :> forall 'b. 'b -> 'b). list ('a * 'c)"
    "forall ('a :> forall 'b. 'b -> 'b) 'c 'd. list ('a * 'c * 'd)",    type_eq "forall 'd ('a :> forall 'b. 'b -> 'b) 'c. list ('a * 'c * 'd)"
    "forall ('a :> forall 'b. 'b -> 'b) 'b. list ('a * 'b)",            type_eq "forall 'b ('a :> forall 'b. 'b -> 'b). list ('a * 'b)"

    // scoping of quantified vars in type equivalence by reusing var names within foralls
    "forall ('b :> forall 'b. 'b -> 'b). list 'b",                      type_eq "forall ('f :> forall 'f. 'f -> 'f). list 'f"
    "forall ('b :> forall 'b. 'b -> 'x). list 'b",                      type_eq "forall ('f :> forall 'f. 'f -> 'y). list 'f"

    // arrow and forall associativity
    "forall ('b :> forall 'b. 'b -> 'b). (forall 'a. 'a -> 'a) -> 'b",                      type_eq "forall ('b :> forall 'b. 'b -> 'b). 'b -> 'b"
    "forall ('b :> forall 'b. 'b -> 'b). (forall 'a. 'a -> 'a) -> 'b",                      type_eq "forall ('b :> forall 'c. 'c -> 'c). (forall 'a. 'a -> 'a) -> 'b"
    "forall ('b :> forall 'b. 'b -> 'b). (forall 'a. 'a -> 'a) -> 'b",                      type_neq "(forall 'a. 'a -> 'a) -> (forall 'a. 'a -> 'a)"
    "forall ('b :> forall 'b. 'b -> 'b). (forall 'a. 'a -> 'a) -> 'b",                      type_eq "forall 'b. (forall 'a. 'a -> 'a) -> ('b -> 'b)"
    "forall ('b :> forall 'b. 'b -> 'b). (forall 'a. 'a -> 'a) -> 'b",                      type_eq "forall 'b. (forall 'a. 'a -> 'a) -> 'b -> 'b"
    "(forall 'a. 'a -> 'a) -> (forall 'a. 'a -> 'a)",                                       type_eq "(forall 'a. 'a -> 'a) -> (forall 'a. 'a -> 'a)"

    "forall 'a. 'a -> 'a",                                                                  type_eq "forall 'a. ('a -> 'a)"
    "forall 'a. 'a -> 'a",                                                                  type_neq "(forall 'a. 'a) -> 'a"
    
    "forall ('b :> forall 'b. 'b -> 'b). forall 'a. 'a -> 'b",                              type_eq "forall ('b :> forall 'b. 'b -> 'b). forall 'a. ('a -> 'b)"
    "forall ('b :> forall 'b. 'b -> 'b). forall 'a. 'a -> 'b",                              type_neq "forall ('b :> forall 'b. 'b -> 'b). (forall 'a. 'a) -> 'b"

    ]

let all =
    [
    type_equivalence
    ]