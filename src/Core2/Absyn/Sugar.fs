(*
 * Lw
 * Absyn/Sugar.fs: pattern and constructor factories for syntactic sugars
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Absyn.Sugar

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
let make_arrows x = make_arrows_by id id x
let make_apps x = make_apps_by id id x

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

let make_rows rowed ((|Rowed|_|) : ident -> _ -> _) =
    let Record = rowed Config.Typing.Names.Type.Row.record
    let (|Record|_|) = (|Rowed|_|) Config.Typing.Names.Type.Row.record
    let Variant = rowed Config.Typing.Names.Type.Row.variant
    let (|Variant|_|) = (|Rowed|_|) Config.Typing.Names.Type.Row.variant
    let Tuple = Row_based_Tuple Record
    let (|Tuple|_|) = (|Row_based_Tuple|_|) (|Record|_|)
    in
        Record, Variant, Tuple, (|Record|_|), (|Variant|_|), (|Tuple|_|)


// lambda with cases on argument

let make_lambda_cases lambda matchh id cases =
    let loc = let (p : node<_>), _, _ = List.head cases in p.loc
    let L = Lo loc
    let x = fresh_reserved_id ()
    in
        L <| lambda ((x, None), (L <| matchh (L <| id x, cases)))

// lambda with multiples arguments creator

let make_lambda_patts (|P_Annot|_|) (|P_Tuple|_|) (|P_Var|_|) (|P_Wildcard|_|) (|P_Custom|_|) lambda lambda_with_cases = function
    | [], _ -> unexpected "empty lambda parameter list" __SOURCE_FILE__ __LINE__
    | ps, e ->
        List.foldBack (fun (p : node<_>) (e : node<_>) ->
                let loc = p.loc
                let rec f = function
                    | P_Annot (ULo (P_Var x), t) -> Lo loc <| lambda ((x, Some t), e)
                    | P_Tuple ([_] | [])         -> unexpected "empty or unary tuple pattern" __SOURCE_FILE__ __LINE__
                    | P_Var x                    -> Lo loc <| lambda ((x, None), e)
                    | P_Wildcard                 -> Lo loc <| lambda ((fresh_reserved_id (), None), e)
                    | P_Custom p e e'            -> Lo loc e'
                    | _                          -> lambda_with_cases [p, None, e]
                in
                    f p.value)
            ps e

// lambda with cases over multiple curried arguments

let make_lambda_curried_cases lambdas p_var var matchh tuple p_tuple =
    let tuple = function
        | [e : node<_>] -> e.value
        | es  -> tuple es
    let p_tuple = function
        | [p : node<_>] -> p.value
        | ps  -> p_tuple ps
    in function
        | [ps, None, e] -> lambdas (ps, e)
        | (p0 : node<_> :: _ as ps0, _, _) :: cases' as cases ->
            let len0 = List.length ps0
            let Lo0 x = Lo p0.loc x
            for ps, _, _ in cases' do
                if List.length ps <> len0 then
                    raise (syntax_error (sprintf "number of function parameters expected to be %d across all cases" len0, p0.loc))
            let ids = List.init len0 (fun _ -> fresh_reserved_id ())
            let pars f = List.mapi (fun i (p : node<_>) -> Lo p.loc <| f ids.[i]) ps0
            let cases = List.map (fun (ps, weo, e) -> Lo0 <| p_tuple ps, weo, e) cases
            in
                lambdas (pars p_var, Lo0 <| matchh (Lo0 <| tuple (pars var), cases))

        | l -> unexpected "ill-formed lambda case list: %O" __SOURCE_FILE__ __LINE__ l

// multiple let-decls in let..in series

let make_lets lett (ds, e) = List.foldBack (fun d e -> Lo e.loc <| lett (d, e)) ds e

// recursive lambda sugar

let make_rec_lambda lambda_cases lett d_rec var ((x, t), cases) =
    let e = lambda_cases cases
    let L x = Lo (let _, _, e = List.head cases in (e : node<_>).loc) x
    in
        L <| lett (L <| d_rec [(x, t), e], L <| var x)

// annotated variable patterns (useful for detecting simple let or let-rec bindings)

let make_simple_var p_var p_annot (|P_Var|_|) (|P_Annot|_|) =
    let P_AnnotVar (x, τ) = p_annot (ULo (p_var x), τ)
    let P_SimpleVar = function
        | x, None   -> p_var x
        | x, Some τ -> P_AnnotVar (x, τ)
    let (|P_AnnotVar|_|) = function
        | P_Annot (ULo (P_Var x), τ) -> Some (x, τ)
        | _ -> None
    let (|P_SimpleVar|_|) = function
        | P_Var x           -> Some (x, None)
        | P_AnnotVar (x, τ) -> Some (x, Some τ)
        | _ -> None
    in
        P_SimpleVar, (|P_SimpleVar|_|)
