﻿(*
 * Lw
 * Test.fs: test modules
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.UnitTest.Engine

open System
open FSharp.Common
open FSharp.Common.Log
open Lw.Core
open Lw.Core.Parsing
open Lw.Core.Globals
open Lw.Core.Absyn
open Lw.Core.Absyn.Misc
open Lw.Core.Absyn.Var
open Lw.Core.Absyn.Kind
open Lw.Interpreter
open Lw.Interpreter.Intrinsic
open Lw.Core.Absyn.Ast
open Lw.Core.Typing.Defs
open Lw.Core.Typing.Inference
open Lw.Core.Typing.Meta
open Lw.Core.Typing.Ops
open Lw.Core.Typing.Report
open Lw.Core.Typing.StateMonad
open PPrint

type logger with
    member this.test pri fmt = this.log_leveled "TEST" Config.Log.test_color Min pri fmt
    member this.test_ok fmt = this.log_unleveled "OK" Config.Log.test_ok_color fmt
    member this.test_weak_ok fmt = this.log_unleveled "WEAK" Config.Log.test_weak_ok_color fmt
    member this.test_failed fmt = this.log_unleveled "FAIL" Config.Log.test_failed_color fmt

[< RequireQualifiedAccess >]
type flag =
    | Verbatim

[< RequireQualifiedAccess >]
type [< NoComparison; NoEquality >] result =
    | TypedOk of string option * flag list
    | StaticError of Type * int option
    | TypeEq of string * bool

[< RequireQualifiedAccess >]
type score = Ok | Failed | Weak
with
    override this.ToString () = this.pretty
    member this.pretty =
        match this with
        | score.Ok      -> "OK"
        | score.Failed  -> "FAILED"
        | score.Weak    -> "WEAK"



// TODO: reuse this for interactive as well
type typechecker () =
    let st0 = Typing.StateMonad.state.state0
    let mutable st = st0

    member private __.unM f x =
        let ctx0 = context.as_top_level_decl
        let r, st1 = f ctx0 x st
        st <- st1
        r
                
    member __.reset_state = st <- st0

    member this.W_expr e = this.unM W_expr e
    member this.W_decl d = this.unM W_decl d
    member this.Wk_and_eval_fxty_expr τ = this.unM Wk_and_eval_fxty_expr τ
    
    member __.auto_generalize loc (t : ty) = t.auto_generalize loc st.Γ
    member __.lookup_var_Γ x = (st.Γ.lookup (jenv_key.Var x)).scheme.fxty

    member this.parse_fxty_expr s =
        let τ =
            try parse_fxty_expr s
            with :? syntax_error as e -> unexpected "syntax error while parsing type expression: %s\n%O" __SOURCE_FILE__ __LINE__ s e
        this.reset_state
        let ϕ, _ = this.Wk_and_eval_fxty_expr τ
        this.reset_state
        ϕ

    member this.parse_ty_expr_and_auto_gen s =
        match this.parse_fxty_expr s with
        | Fx_F_Ty t -> Fx_F_Ty <| this.auto_generalize (new location ()) t
        | ϕ         -> ϕ



[< RequireQualifiedAccess >]
type [< NoEquality; NoComparison >] parsed =
    | Expr of expr
    | Decl of decl
with
    override this.ToString () = this.pretty
    member this.pretty =
        match this with
        | Expr e -> sprintf "<EXPR> %s" e.pretty
        | Decl d -> sprintf "<DECL> %s" d.pretty

    member this.pretty_translated =
        let inline p (e : ^e) = match (^e : (member translated : _) e) with Translated u -> (^u : (member pretty : string) u)
        match this with
        | Expr e -> sprintf "<EXPR> %s" (p e)
        | Decl d -> sprintf "<DECL> %s" (p d)
        


// PPrint extensions
//
      
let colon2 = txt Config.Printing.kind_annotation_sep
let norm x = txt (use N = var.reset_normalization in sprintf "%O" x)   // normalize vars in case parameter x has type ty of fxty
let fxty (x : fxty) = norm x
let ty (x : ty) = norm x
let kind (x : kind) = norm x

let pp_infos l =
    let l = Seq.map (fun (s : string, doc) -> sprintf "%s: " (s.TrimEnd [|':'; ' '|]), doc) l
    let w = Seq.maxBy (fst >> String.length) l |> fst |> String.length
    in
      [ for s : string, doc : Doc in l do
            yield (txt s |> fill w) </> doc
      ] |> vsep |> align

let typed_infos (ϕ, t, k) = ["flex type", ϕ; "F-type", t; "kind", k]

let expected_infos (ϕok : fxty) = ["expected", pp_infos <| typed_infos (fxty ϕok, ty ϕok.ftype, kind ϕok.kind)]

let static_error_infos (input : string) (e : static_error) =
    let term =
        let x = e.location.absolute_col
        let y = e.location.absolute_end_col
        in
            input.Substring (x, y - x)
    in
      [ "raised", txt (e.header.ToUpper ())
        "code", fmt "%d" e.code
        "at", fmt "%O" e.location
        "term", txt term
        "message", txt e.message_body ]


// logging and pprint shorcuts
//

type logger with
    member __.pp (L : PrintfFormat<_, _, _, _> -> _) doc = L "%s" <| render None doc

let test_ok esit infs = L.pp L.test_ok (pp_infos (["esist", txt esit] @ infs)); score.Ok

let test_failed msg infs = L.pp L.test_failed (pp_infos (["reason", txt msg] @ infs)); score.Failed

let test_weak_ok esit infs = L.pp L.test_weak_ok (pp_infos (["esit", txt esit] @ infs)); score.Weak

let testing pri doc = L.pp (L.test pri) doc


// testers
//

let compare_test eq_fxty eq_ty eq_kind (ϕres : fxty) (ϕok : fxty) =
    let tb = eq_ty ϕok.ftype ϕres.ftype
    let kb = eq_kind ϕok.kind ϕres.kind
    let ϕb =
        match ϕres.is_really_flex, ϕok.is_really_flex with
        | true, true   -> eq_fxty ϕres ϕok
        | false, true  -> false
        | true, false
        | false, false -> tb
    in
        ϕb, tb, kb

let compare_test_eq = compare_test (fun (x : fxty) y -> x.is_equivalent y) (fun (x : ty) y -> x.is_equivalent y) (fun (x : kind) y -> x.is_equivalent y)   

let compare_test_verbatim =
    let p x =
        use N = var.reset_normalization
        let r = sprintf "%O" x
        in
            r.Replace (Config.Printing.dynamic.flex_forall, Config.Printing.dynamic.forall)     // replace capitalized Forall with the lowercase one
    let (===) a b = p a = p b
    in
        compare_test (===) (===) (===)


let decl_dummy_ty = Fx_F_Ty T_Unit

type entry = string * result
type section = string * entry list

let entry_info sec n = "entry", txt (sprintf "#%d in section \"%s\"" (n + 1) sec)
let ok_or_no_info b doc = (txt (sprintf "(%s)" (if b then "OK" else "NO"))) <+> doc
                                 
let parse_expr_or_decl s =
    try parsed.Expr (parse_expr s)
    with :? syntax_error ->
        try parsed.Decl (parse_decl s)
        with :? syntax_error -> reraise ()
           | e               -> unexpected "syntax error while parsing expression or declaration: %s\n%O" __SOURCE_FILE__ __LINE__ s e

let typecheck_expr_or_decl (tchk : typechecker) sec n input =
    testing Min (txt "input:" </> txt input)
    let p = parse_expr_or_decl input
    testing Low (txt "parsed:" </> fmt "%O" p)
    let ϕ =
        match p with
        | parsed.Expr e -> tchk.W_expr e
        | parsed.Decl d ->
            tchk.W_decl d
            match d.value with
            | D_Bind [{ patt = ULo (P_Var x) | ULo (P_Annot (ULo (P_Var x), _)) }]
            | D_Rec [{ par = x, _ }] ->
                tchk.lookup_var_Γ x

            | _ -> decl_dummy_ty
    in
        ϕ, fun (ϕb, tb, kb) -> [ "translated", txt p.pretty_translated
                                 "inferred", pp_infos <| typed_infos (ok_or_no_info ϕb (fxty ϕ), 
                                                                      ok_or_no_info tb (ty ϕ.ftype),
                                                                      ok_or_no_info kb (kind ϕ.kind)) ]

let test_entry (tchk : typechecker) sec n ((s1, res) : entry) =
    let infs0 = [ entry_info sec n ]
    match res with
    | result.TypeEq (s2, is_eq) ->
        testing Low (txt s1 <+> txt "=" <+> txt s2)
        let ϕ1 = tchk.parse_fxty_expr s1
        let ϕ2 = tchk.parse_fxty_expr s2
        testing Low (fxty ϕ1 <+> txt "=" <+> fxty ϕ2)
        let t1 = ϕ1.ftype
        let t2 = ϕ2.ftype
        let k1 = ϕ1.kind
        let k2 = ϕ2.kind
        let b1 = ϕ1.is_equivalent ϕ2
        let b2 = t1.is_equivalent t2
        let b3 = k1.is_equivalent k2
        let infs =
            infs0 @
            [ //"parsed", txt s1 <+> txt "=" <+> txt s2
              "flex types", ok_or_no_info b1 (fxty ϕ1 <+> txt "=" <+> fxty ϕ2)
              "F-types", ok_or_no_info b2 (ty t1 <+> txt "=" <+> ty t2)
              "kinds", ok_or_no_info b3 (kind k1 <+> txt "=" <+> kind k2) ]
        let test_ok' = if is_eq then test_ok else test_failed
        let test_failed' = if is_eq then test_failed else test_ok
        in
            (match b1, b2, b3 with
            | true, true, true  -> test_ok' "types are equivalent" 
            | true, true, false -> test_weak_ok "types are equivalent but kinds are different" 
            | true, false, _    -> test_weak_ok "flex types are equivalent but F-types are different"
            | false, true, _    -> test_weak_ok "F-types are equivalent but flex types are different"
            | false, false, _   -> test_failed' "types are different")
                infs

    | result.TypedOk (so, flags) ->
        let is_enabled flag = List.contains flag flags
        let ϕok =
            match so with
            | Some s -> try tchk.parse_ty_expr_and_auto_gen s
                        with e -> unexpected "%s" __SOURCE_FILE__ __LINE__ (pretty_exn_and_inners e)   
            | None   -> decl_dummy_ty
        in
            try
                let ϕres, infs1 = typecheck_expr_or_decl tchk sec n s1
                let compare_test = if is_enabled flag.Verbatim then compare_test_verbatim else compare_test_eq
                let b3 = compare_test ϕres ϕok
                let infs1 = infs0 @ infs1 b3
                let infs2 = expected_infos ϕok
                in
                    match b3 with
                    | true, true, true  -> test_ok "all ok" infs1
                    | true, false, true -> test_weak_ok "F-types are different" (infs1 @ infs2)
                    | false, true, true -> test_weak_ok "flex types are different" (infs1 @ infs2)
                    | true, false, false
                    | false, true, false -> test_failed "type is ok but kind is not" (infs1 @ infs2)
                    | _                  -> test_failed "types expected to be equal" (infs1 @ infs2)
            with :? static_error as e ->
                test_failed "unwanted static error" <| infs0 @ static_error_infos s1 e @ expected_infos ϕok
                    
    | result.StaticError (T, codeo) ->
        assert (let t = typeof<static_error> in t = T || T.IsSubclassOf t)
        try
            let _, infs1 = typecheck_expr_or_decl tchk sec n s1
            in
                test_failed
                    (something (sprintf "expected static error %d") "expected a static error" codeo)
                    (infs0 @ infs1 (false, false, false) @ [something (sprintf "static error %d expected") "any static error expected" codeo, txt T.Name])
        with :? static_error as e ->
            let tb = let t = e.GetType() in t = T || t.IsSubclassOf T
            let cb = match codeo with
                     | None   -> true
                     | Some n -> n = e.code
            in
                (match tb, cb with
                | true, true   -> test_ok "justly rejected"
                | true, false  -> test_weak_ok "static error type is right but error code is wrong"
                | false, true  -> test_weak_ok "error code is right but static error type is wrong"
                | false, false -> test_failed "wrong static error type and code")
                    <| infs0 @ static_error_infos s1 e


let score_infos scores =
    [score.Ok; score.Weak; score.Failed] @ scores   // trick for making countBy always count at least 1 for each kind of score
    |> List.countBy identity
    |> List.sortBy (fst >> function score.Ok -> 1 | score.Weak -> 2 | score.Failed -> 3)
    |> List.map (fun (score, n) -> sprintf "%O" score, fmt "%d" (n  - 1))   // n-1 because of the trick above

let section_infos sec (span : TimeSpan) (scores : score list) =
    ["section", txt sec; "entries", fmt "%d" scores.Length; "cpu time", txt span.pretty; "results", pp_infos (score_infos scores)]

let test_section tchk ((sec, entries) : section) =
    let scores, span = cputime (List.mapi (fun i -> test_entry tchk sec i)) entries
    let infs = section_infos sec span scores
    L.pp (L.msg High) (pp_infos infs)
    scores

let test_sections secs =
    let tchk = new typechecker ()
    let scores, span = cputime (fun () -> List.map (test_section tchk) secs |> List.concat) () 
    let infs = section_infos (mappen_strings fst ", " secs) span scores
    L.pp (L.msg Unmaskerable) (pp_infos infs)
    List.sumBy (function score.Ok | score.Weak -> 1 | _ -> 0) scores


module Tests =
    let type_ok s = result.TypedOk (Some s, [])
    let type_is s = result.TypedOk (Some s, [flag.Verbatim])
    let type_eq s = result.TypeEq (s, true)
    let type_neq s = result.TypeEq (s, false)
    let ok = result.TypedOk (None, [])
    let wrong< 'exn when 'exn :> static_error > codeo = result.StaticError (typeof<'exn>, codeo)
    let wrong_type = wrong<type_error> None
    let wrong_syntax = wrong<syntax_error> None
    let static_errn code = wrong<static_error> (Some code)
    let type_errn code = wrong<type_error> (Some code)
    let unbound_error = static_errn 10

