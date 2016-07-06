
module Lw.Interpreter.UnitTest.Other

open Lw.Interpreter.UnitTester
open Lw.Interpreter.UnitTester.Aux
open FSharp.Common.Collections

let cset : section =
    "cset", [],
    let a = cset [1..5]
    let b = cset [2..5]
    let c = cset [6..9]
    [
    custom (fun () -> a + b = a)
    custom (fun () -> a + c - a = c)
    custom (fun () -> a.intersect b = b)
    custom (fun () -> c >= a)
    ]



let all : section list =
    [
    cset
    ]

