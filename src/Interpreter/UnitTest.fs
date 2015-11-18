(*
 * Lw
 * Test.fs: test modules
 * (C) 2000-2014 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.UnitTest

open System
open FSharp.Common.Prelude
open FSharp.Common.Log
open FSharp.Common
open Lw.Core.Typing.Defs

#if UNIT_TEST

module Lazyness =

    type [<NoComparison>] llist<'a> = 
        | Nil
        | Cons of Lazy<'a> * Lazy<llist<'a>>
    with
        override this.ToString() = 
            let rec R = function 
                | Nil -> ""
                | Cons(x, l) -> sprintf "%O; %O" x.Value l
            in
                sprintf "[%s]" (R this)
    
    let rec lmap f = function 
        | Nil -> Nil
        | Cons (x, l) -> Cons (f x, lazy lmap f l.Value)
    
    let rec lzip l1 l2 = 
        match l1, l2 with
        | Nil, Nil -> Nil
        | Cons (x1, xs1), Cons (x2, xs2) -> Cons (lazy (x1.Value, x2.Value), lazy lzip xs1.Value xs2.Value)
        | _ -> unexpected "zip" __SOURCE_FILE__ __LINE__
    
    let lmap2 f l1 l2 = lmap (function Lazy (x, y) -> f x y) (lzip l1 l2)
    
    let ltail = function
        | Nil -> unexpected "empty list" __SOURCE_FILE__ __LINE__
        | Cons (_, xs) -> xs.Value

// NOTE: non riesco neanche a scriverla: ci sono troppi lazy! :P
//    let rec fibs = Cons (lazy 0, lazy Cons (lazy 1, lazy lmap2 (fun (x : Lazy<_>) (y : Lazy<_>) -> lazy x.Value + y.Value) fibs (ltail fibs.Value)))
//    
//    let fibi i = List.nth fibs.Value i


module Computations =

    open Computation

    let main () =
        L.debug Normal "start" 
        let s3 =
            str {
                yield 'a'
                yield 'b'
                yield! "ciao"
                let a = byte_of_char 'A'
                for c in [1uy .. 10uy] do
                    yield char_of_byte (a + c)
                yield! "end"
            }
        L.debug Normal "s3 = %O" s3
        0
        



module Patterns =

    let t1, t2, t3 = T_Int, T_Bool, T_Unit
    let arr = T_Arrows [t1; t2; t3]
    let ap = T_Apps [t1; t2; t3]
    
    let main () =
        L.debug Normal "arr = %O" arr
        L.debug Normal "ap = %O" ap
        0


let main = Computations.main
    
#endif