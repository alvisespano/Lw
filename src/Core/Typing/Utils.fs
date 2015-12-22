(*
 * Lw
 * Typing/Utils.fs: typing utilities
 * (C) 2000-2014 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Utils

open FSharp.Common.Prelude
open FSharp.Common.Log
open FSharp.Common
open Lw.Core.Absyn
open Lw.Core.Globals
open Lw.Core.Typing
open Lw.Core.Typing.Defs

let vars_in_term (|Var|Leaf|Nodes|) =
    let rec R = function
        | Var x  -> Set.singleton x
        | Leaf   -> Set.empty
        | Nodes ps as p0 ->
            List.fold (fun set p ->
                    let set' = R p
                    let xs = Set.intersect set set'
                    in
                        if Set.isEmpty xs then Set.union set set'
                        else Report.Error.variables_already_bound_in_pattern (p : node<_, _>).loc xs p0)
                Set.empty ps
    in
        R

let rec vars_in_kind k =
    Computation.set {
        match k with
        | K_Var α        -> yield α
        | K_Cons (_, ks) -> for k in ks do yield! vars_in_kind k }

//let rec vars_in_ty t =
//    Computation.set {
//        match t with
//        | T_Var (α, k)     -> yield α; yield! vars_in_kind k
//        | T_Cons (_, k)    -> yield! vars_in_kind k
//        | T_HTuple (ts, k) -> for t in ts do yield! vars_in_ty t; yield! vars_in_kind k
//        | T_App (t1, t2)   -> yield! vars_in_ty t1; yield! vars_in_ty t2
//        | T_Closure ( kind }

let vars_in_patt p =
    let (|Var|Leaf|Nodes|) (p : patt) =
        match p.value with
        | P_Var x        -> Var x
        | P_PolyCons _
        | P_Cons _
        | P_Lit _
        | P_Wildcard     -> Leaf
        | P_Annot (p, _) 
        | P_As (p, _)    -> Nodes [p]
        | P_App (p1, p2)
        | P_Or (p1, p2) 
        | P_And (p1, p2) -> Nodes [p1; p2]
        | P_Record bs    -> Nodes [for _, p in bs -> p]
        | P_Tuple ps     -> Nodes ps
    in
        vars_in_term (|Var|Leaf|Nodes|) p

let vars_in_ty_patt : ty_patt -> _ =
    let (|Var|Leaf|Nodes|) (p : ty_patt) =
        match p.value with
        | Tp_Var x         -> Var x
        | Tp_Cons _ 
        | Tp_Wildcard      -> Leaf
        | Tp_Annot (p, _) 
        | Tp_As (p, _)     -> Nodes [p]
        | Tp_App (p1, p2) 
        | Tp_Or (p1, p2) 
        | Tp_And (p1, p2)  -> Nodes [p1; p2]
        | Tp_HTuple ps     -> Nodes ps        
        | Tp_Row (xps, po) -> Nodes (List.map snd xps @ (match po with None -> [] | Some p -> [p]))
    in
        vars_in_term (|Var|Leaf|Nodes|)

let rec vars_in_decl (d : decl) =
    let B = Computation.set
    let pars bs = B { for b in bs do let x, _ = b.par in yield x }
    let inline ids bs = B { for b in bs do yield (^x : (member id : id) b) }
    in
        B {
            match d.value with
            | D_Bind bs     -> for b in bs do yield! vars_in_patt b.patt
            | D_Rec bs      -> yield! pars bs
            | D_Type bs     -> yield! pars bs
            | D_Kind bs     -> yield! ids bs
            | D_Overload bs -> yield! ids bs
            | D_Open _      -> ()
            | D_Datatype b  -> yield b.id
            | D_Reserved_Multi ds -> for d in ds do yield! vars_in_decl d
        }


let E_CId (c : constraintt) = Id c.pretty_as_translated_id
let E_Jk (jk : jenv_key) = Id jk.pretty_as_translated_id
let P_CId (c : constraintt) = P_Var c.pretty_as_translated_id
let P_Jk (jk : jenv_key) = P_Var jk.pretty_as_translated_id

let possibly_tuple L0 e tuple cs =
    match [ for c in cs -> L0 (e c) ] with
    | []  -> unexpected "empty tuple" __SOURCE_FILE__ __LINE__
    | [p] -> p
    | ps  -> L0 (tuple ps)
