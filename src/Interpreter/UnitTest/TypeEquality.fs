
module Lw.Interpreter.UnitTest.TypeEquality

open Lw.Interpreter.UnitTester.Aux

let type_equality =
    "Type Equality",
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
    "forall 'a 'b. 'a -> 'b",                   type_neq "forall 'a 'b. 'a -> 'c"

    "forall ('a :> forall 'b. 'b -> 'b). list 'a",                      type_eq "forall ('f :> forall 'f. 'f -> 'f). list 'f"
    "forall ('a :> forall 'b. 'b -> 'b). list 'a",                      type_eq "forall ('a :> forall 'b. 'b -> 'b). list 'a"
    "forall ('a :> forall 'b. 'b -> 'b) 'c. list ('a * 'c)",            type_eq "forall 'c ('a :> forall 'b. 'b -> 'b). list ('a * 'c)"
    "forall ('a :> forall 'b. 'b -> 'b) 'c 'd. list ('a * 'c * 'd)",    type_eq "forall 'd ('a :> forall 'b. 'b -> 'b) 'c. list ('a * 'c * 'd)"
    "forall ('a :> forall 'b. 'b -> 'b) 'b. list ('a * 'b)",            type_eq "forall 'b ('a :> forall 'b. 'b -> 'b). list ('a * 'b)"

    // test scoping of quantified vars in type equivalence by reusing var names withing foralls
    "forall ('b :> forall 'b. 'b -> 'b). list 'b",                      type_eq "forall ('f :> forall 'f. 'f -> 'f). list 'f"
    "forall ('b :> forall 'b. 'b -> 'x). list 'b",                      type_eq "forall ('f :> forall 'f. 'f -> 'y). list 'f"
    ]

let all =
    [
    type_equality
    ]