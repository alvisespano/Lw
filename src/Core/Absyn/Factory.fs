(*
 * Lw
 * Absyn/Factory.fs: active pattern and constructor factories
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Absyn.Factory

open System
open System.Collections.Generic
open FSharp.Common
open Lw.Core
open FSharp.Common.Log
open FSharp.Common.Parsing
open Lw.Core.Globals
open Lw.Core.Absyn.Misc

// application grouper
//

let (|Application|) (|App|_|) (|R|_|) = // (|R|_|) matches right-hand atoms
    let (|L|_|) = function
        | App _ | R _ as x -> Some x
        | _ -> None
    in function
    | (L e1, R e2)  -> sprintf "%O %O" e1 e2
    | (e1, R e2)    -> sprintf "(%O) %O" e1 e2
    | (L e1, e2)    -> sprintf "%O (%O)" e1 e2
    | (e1, e2)      -> sprintf "(%O) (%O)" e1 e2

/// This function produces active patterns and constructors for manipulating multiple occurrences of the given single-occurrence active pattern and constructor.
/// For example, it can produce the 'T_Arrows' constructor and the respective pattern, given the single-occurrence 'T_Arrow' constructor and pattern.
/// In details, this function returns the triple cs', (|Ps0'|), (|Ps'|_|) where:
///     cs' is the multiple-occurence constructor;
///     (|Ps0'|) is the non-optional version of the multiple-occurence pattern, defined in such a way that it always matches and returns something even when there are no occurrences (or a single occurrence, depending on the semantics);
///     (|Ps'|_|) is the optional version of the multiple-occurence pattern, matching successfully only at least one occurrence.
/// Arguments are grouped into 2 tuples:
///    the first is a triple where cs is the multiple-occurrence constructor parametric on the single-occurrence constructor c1,
///                                 Ps is the optional version of the multiple-occurrence pattern parametric on the single-occurrence pattern P1,
///                                 Ps0 is the non-optional version od the multiple-occurrence pattern parametric on the optional one, created using Ps;
///    the second group consists of the last 2 curried arguments where
///                                         c1 is the actual single-occurrence constructor,
///                                         P1 is the actual single-occurrence pattern.
/// Reccomended use of this function is in curried form, i.e. defining and passing the first tupled argument only;
/// further code will eventually need to pass the second tuple with actual single-occurrence constructor and pattern.
let make_patterns (cs, (|Ps|_|), (|Ps0|)) (c1 : 'a -> 'b) ((|P1|_|) : 'b -> 'a option) = 
    let (|Ps|_|) x = (|Ps|_|) (|P1|_|) x
    in
        cs c1, (|Ps0|) (|Ps|_|), (|Ps|_|)


// arrows active pattern creator

let make_arrow_by_apps arrow_cons apps (|Arrow_Cons|_|) (|Apps|_|) = 
    let Arrow (t1, t2) = apps [arrow_cons; t1; t2]
    let (|Arrow|_|) = function
        | Apps [Arrow_Cons; τ1; τ2] -> Some (τ1, τ2)
        | _ -> None
    in
        Arrow, (|Arrow|_|)

let make_arrows_by f (|F|) =
    let rec Arrows arrow = function
        | []        -> unexpected "empty list of Arrows items" __SOURCE_FILE__ __LINE__
        | [F x]     -> x
        | x :: xs   -> arrow (x, f (Arrows arrow xs))
    let rec (|Arrows|_|) (|Arrow|_|) = function
        | Arrow (x1, F (Arrows (|Arrow|_|) l)) -> Some (x1 :: l)
        | Arrow (x1, x2)                       -> Some [x1; x2]
        | _                                    -> None
    let (|Arrows1|) (|Arrows|_|) = function
        | Arrows xs -> xs
        | x         -> [f x]
    in
        make_patterns (Arrows, (|Arrows|_|), (|Arrows1|))


// apps active pattern creator

let make_apps_by f (|F|) =
    let rec Apps app = function
        | []    -> unexpected "empty or singleton list of Apps items" __SOURCE_FILE__ __LINE__
        | [F x] -> x
        | l     -> let xs, x = List.takeButLast l in app (f (Apps app xs), x)
    let rec (|Apps|_|) (|App|_|) = function
        | App (F (Apps (|App|_|) l), x2) -> Some (l @ [x2])
        | App (x1, x2)                   -> Some [x1; x2]
        | _  -> None
    let (|Apps1|) (|Apps|_|) = function
        | Apps xs -> xs
        | x       -> [f x]
    in
        make_patterns (Apps, (|Apps|_|), (|Apps1|))

/// Homogeneous version using identity as projection
let make_arrows x = make_arrows_by identity identity x
let make_apps x = make_apps_by identity identity x

// foralls active pattern creator

let Foralls forall = function
    | [], t -> t
    | αs, t -> List.foldBack (fun α t -> forall (α, t)) αs t

let rec (|Foralls|_|) (|Forall|_|) = function
    | Forall (α, Foralls (|Forall|_|) (αs, t)) -> Some (α :: αs, t)
    | Forall (α, t)                            -> Some ([α], t)
    | _                                        -> None

let (|Foralls0|) (|Foralls|_|) = function
    | Foralls (αs, t) -> αs, t
    | t               -> [], t

let make_foralls x = make_patterns (Foralls, (|Foralls|_|), (|Foralls0|)) x

// rows active pattern creator

let Row_based_Tuple tup ps = tup (List.mapi (fun i p -> tuple_index_label (i + 1), p) ps, None)
let (|Row_based_Tuple|_|) (|Tup|_|) = function
    | Tup ((x1, _) :: _ as bs, None) when x1 = tuple_index_label 1 -> Some (List.map snd bs)
    | _ -> None

let make_rows rowed ((|Rowed|_|) : id -> _ -> _) =
    let Record = rowed Config.Typing.Names.Type.Row.record
    let (|Record|_|) = (|Rowed|_|) Config.Typing.Names.Type.Row.record
    let Variant = rowed Config.Typing.Names.Type.Row.variant
    let (|Variant|_|) = (|Rowed|_|) Config.Typing.Names.Type.Row.variant
    let Tuple = Row_based_Tuple Record
    let (|Tuple|_|) = (|Row_based_Tuple|_|) (|Record|_|)
    in
        Record, Variant, Tuple, (|Record|_|), (|Variant|_|), (|Tuple|_|)

