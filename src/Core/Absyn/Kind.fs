(*
 * Lw
 * Absyn/Kind.fs: kind definition and related stuff
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Absyn.Kind

#nowarn "60"

open System
open System.Collections.Generic
open FSharp.Common
open Lw.Core
open FSharp.Common.Log
open FSharp.Common.Parsing
open Lw.Core.Globals
open Lw.Core.Absyn.Misc
open Lw.Core.Absyn.Var
open Lw.Core.Absyn.Sugar


type [< NoComparison; NoEquality; Diagnostics.DebuggerDisplay("{ToString()}") >] kind =
    | K_Var of var
    | K_Cons of ident * kind list
with
    interface annotable with
        member __.annot_sep = Config.Printing.kind_annotation_sep


// kind active patterns
//

let K_Id x = K_Cons (x, [])
let (|K_Id|_|) = function
    | K_Cons (x, []) -> Some x
    | _ -> None

#if DEFINE_K_APP
let K_App (k1, k2) =
    match k1 with
    | K_Cons (x, ks) -> K_Cons (x, ks @ [k2])
    | k0 -> unexpected "leftmost term '%O' of kind application '%O %O' is not an identifier" __SOURCE_FILE__ __LINE__ k0 k1 k2
let (|K_App|_|) = function
    | K_Cons (x, Mapped List.rev (klast :: Mapped List.rev ks)) -> Some (K_App (K_Cons (x, ks), klast))
    | _ -> None

let K_Apps, (|K_Apps0|), (|K_Apps|_|) = make_apps K_App (|K_App|_|)
let K_Arrow, (|K_Arrow|_|) = let A = Config.Typing.Names.Kind.arrow in make_arrow_by_apps (K_Id A) K_Apps (function K_Id x when x = A -> Some () | _ -> None) (|K_Apps|_|)
#else
let K_Arrow (k1, k2) = K_Cons (Config.Typing.Names.Kind.arrow, [k1; k2])
let (|K_Arrow|_|) = function
    | K_Cons (s, [k1; k2]) when s = Config.Typing.Names.Kind.arrow -> Some (k1, k2)
    | _ -> None
#endif

let K_Arrows, (|K_Arrows1|), (|K_Arrows|_|) = make_arrows K_Arrow (|K_Arrow|_|)

let K_Star = K_Id Config.Typing.Names.Kind.star
let (|K_Star|_|) = function
    | K_Id s when s = Config.Typing.Names.Kind.star -> Some ()
    | _ -> None

type kind with
    member this.is_star =
        match this with
        | K_Star -> true
        | _ -> false

let K_Row = K_Cons (Config.Typing.Names.Kind.row, [])
let (|K_Row|_|) = function
    | K_Cons (name, []) when name = Config.Typing.Names.Kind.row -> Some ()
    | _ -> None

let K_HTuple ks = K_Cons (Config.Typing.Names.Kind.htuple, ks)
let (|K_HTuple|_|) = function
    | K_Cons (name, ks) when name = Config.Typing.Names.Kind.htuple -> Some ks
    | _ -> None

type kind with
    member this.pretty =
        let (|A|_|) = function
            | K_Var _ 
            | K_Cons (_, []) as k -> Some k
            | _ ->  None
        let rec R = function
            | K_Var α                       -> sprintf "%O" α
            | K_Arrow (K_Arrow _ as k1, k2) -> sprintf "(%s) -> %s" (R k1) (R k2)
            | K_Arrow (k1, k2)              -> sprintf "%s -> %s" (R k1) (R k2)
            | K_HTuple ([] | [_])           -> unexpected "empty or unary tuple kind" __SOURCE_FILE__ __LINE__
            | K_HTuple ks                   -> sprintf "(%s)" (mappen_strings R ", " ks)
            | K_Cons (x, [])                -> x
            | K_Cons (x, [A k])             -> sprintf "%s %s" x (R k)
            | K_Cons (x, ks)                -> sprintf "%s (%s)" x (mappen_strings R ", " ks)
        in
            R this

    override this.ToString () = this.pretty

    static member fresh_var = K_Var var.fresh

type kinded_param = kind id_param

type kinded_var_param = param<var, kind>

let pretty_row sep binder = function
    | [], Some x -> sprintf "%O :: %O" x K_Row
    | xes, xo ->
        let s = mappen_strings (fun (x, e) -> sprintf "%s %s %O" x binder e) sep xes
        in
            match xo with
                | None   -> s
                | Some x -> sprintf "%s | %O" s x