
module Lw.Interpreter.UnitTest.Custom

open Lw.Interpreter.UnitTester
open Lw.Interpreter.UnitTester.Aux
open FSharp.Common.Collections

let cset1 : section =
    "cset1", [],
    let a = cset [1..5]
    let b = cset [2..5]
    let c = cset [6..9]
    let U = cset.universe
    let E = cset.empty
    [
    custom <| fun () -> a + b = a
    custom <| fun () -> a + c - a = c
    custom <| fun () -> a.intersect b = b
    custom <| fun () -> c >= a
    custom <| fun () -> U - a = a.complement
    custom <| fun () -> U - U = E
    ]



let all : section list =
    [
    cset1
    ]

