
module Lw.Interpreter.UnitTest.Records

open Lw.Interpreter.UnitTester
open Lw.Interpreter.UnitTester.Aux

let records =
    "Records", [],
    [
    "{}",                                       wrong_syntax
    "{ a = 1 }",                                typed_ok_as "{ a : int }"
    "{ a = 1; b = true }",                      typed_ok_as "{ a : int; b : bool }"
    "let r = { a = 1 }",                        typed_ok_as "{ a : int }"
    "{ b = true | r }",                         typed_ok_as "{ a : int; b : bool }"
    ]
    
let all : section list =
    [
    records
    ]

