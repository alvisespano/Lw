(*
 * Lw
 * Test.fs: test modules
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.UnitTester

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
open Lw.Core.Typing.Equivalence
open PPrint

type logger with
    member this.testing fmt = this.log_unleveled "TEST" Config.Log.test_color fmt
    member this.test_ok fmt = this.log_unleveled "OK" Config.Log.test_ok_color fmt
    member this.test_weak_ok fmt = this.log_unleveled "WEAK" Config.Log.test_weak_ok_color fmt
    member this.test_failed fmt = this.log_unleveled "FAIL" Config.Log.test_failed_color fmt

[< RequireQualifiedAccess >]
type flag =
    | Verbatim
    | Unbind
    | KeepBindingsAtEnd
    | ShowSuccessful
    | ShowInput
    | NoAutoGen
    | No of flag
with
    static member private fold_flags p flag flags =
        List.fold (fun r ->
                function flag' when flag = flag'     -> true
                       | No flag' when flag = flag'  -> false
                       | _                           -> r)
            false flags |> p
    static member is_enabled = flag.fold_flags id

[< RequireQualifiedAccess >]
type [< NoComparison; NoEquality >] result =
    | TypedOk of string option
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
    let mutable st = Typing.StateMonad.state.state0
    let ctx0 = context.as_top_level_decl

    member private __.unM f x =
        let r, st1 = f ctx0 x st
        st <- st1
        r
                
    member private __.unM_member f =
        let M = new type_inference_builder (ctx0)
        let r, st1 = f M st
        st <- st1
        r

    member this.W_expr e = this.unM W_expr e
    member this.W_decl d = this.unM W_decl d
    member this.Wk_and_eval_fxty_expr τ = this.unM Wk_and_eval_fxty_expr τ
    
    member this.auto_generalize (t : ty) = this.unM_member <| fun M -> M.auto_generalize false t
    member __.lookup_var_Γ x = (st.Γ.lookup (jenv_key.Var x)).scheme.fxty

    member __.envs
        with get () = st.Γ, st.γ, st.δ
        and set (Γ, γ, δ) = st <- { st with Γ = Γ; γ = γ; δ = δ }

    member this.parse_fxty_expr (s, ?autogen) =
        let autogen = defaultArg autogen false
        let τ =
            try parse_fxty_expr s
            with :? syntax_error as e -> unexpected "syntax error while parsing type expression: %s\n%O" __SOURCE_FILE__ __LINE__ s e
        let st1 = st
        let ϕ, _ = this.Wk_and_eval_fxty_expr τ
        st <- st1
        match τ, ϕ with
        | τ, Fx_F_Ty t -> τ, Fx_F_Ty <| (if autogen then this.auto_generalize else id) t
        | r            -> r



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
        

let error_name_of_type (T : Type) : string = T.GetProperty("error_name").GetGetMethod().Invoke(T, [||]) |> unbox
//let inline error_name_of_exn (_ : ^e) = (^e : (static member error_name : string) ())
let error_name_of_exn (e : static_error) = error_name_of_type (e.GetType ())

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
      [ "raised", txt (error_name_of_exn e)
        "code", fmt "%d" e.code
        "at", fmt "%O" e.location
        "term", txt term
        "message", txt e.message_body ]


// entries and sections
//

//let decl_dummy_ty = Fx_F_Ty T_Unit

type entry = string * (result * flag list)
type section = string * flag list * entry list

type section_data = {
    name : string
    num : int
    flags : flag list
}

type entry_data = {
    section : section_data
    input : string
    flags : flag list
}
with
    member this.is_enabled fl = flag.is_enabled fl (this.flags @ this.section.flags)

let entry_info sec n = "entry", txt (sprintf "#%d in section \"%s\"" (n + 1) sec)
let ok_or_no_info b doc = (txt (sprintf "(%s)" (if b then "OK" else "NO"))) <+> doc


// logging and pprint shorcuts
//

type logger with
    member __.pp (L : PrintfFormat<_, _, _, _> -> _) doc = L "%s" <| render None doc

let test_ok (ed : entry_data) esit infs =
    if ed.is_enabled flag.ShowSuccessful then
        L.pp L.test_ok (pp_infos (["esist", txt esit] @ infs))
    score.Ok

let test_failed msg infs = L.pp L.test_failed (pp_infos (["reason", txt msg] @ infs)); score.Failed

let test_weak_ok esit infs = L.pp L.test_weak_ok (pp_infos (["esit", txt esit] @ infs)); score.Weak

let testing (ed : entry_data) doc =
    if ed.is_enabled flag.ShowInput then
        L.pp L.testing doc


// compares
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


// testers
//
                                 
let parse_expr_or_decl s =
    try parsed.Expr (parse_expr s)
    with :? syntax_error ->
        try parsed.Decl (parse_decl s)
        with :? syntax_error -> reraise ()
           | e               -> unexpected "syntax error while parsing expression or declaration: %s\n%O" __SOURCE_FILE__ __LINE__ s e


let test_entry (tchk : typechecker) sd ((s1, (res, flags)) : entry) =
    let infs0 = [ entry_info sd.name sd.num ]
    let ed = { section = sd; input = s1; flags = flags }
    let test_ok = test_ok ed
    let testing = testing ed
    
    let typecheck_expr_or_decl () =
        testing (txt "input:" </> txt ed.input)
        let p = parse_expr_or_decl ed.input
        testing (txt "parsed:" </> fmt "%O" p)
        let ϕ =
            match p with
            | parsed.Expr e -> tchk.W_expr e
            | parsed.Decl d ->
                let envs0 = tchk.envs
                tchk.W_decl d
                match d.value with
                | D_RecBind [{ patt = ULo (P_SimpleVar (x, _)) }]
                | D_Bind [{ patt = ULo (P_SimpleVar (x, _)) }] ->
                    let r = tchk.lookup_var_Γ x
                    if ed.is_enabled flag.Unbind then
                        tchk.envs <- envs0
                    r

                | d -> not_implemented "%O" __SOURCE_FILE__ __LINE__ d
        in
            ϕ, fun (ϕb, tb, kb) -> [ "translated", txt p.pretty_translated
                                     "inferred", pp_infos <| typed_infos (ok_or_no_info ϕb (fxty ϕ), 
                                                                          ok_or_no_info tb (ty ϕ.ftype),
                                                                          ok_or_no_info kb (kind ϕ.kind)) ]

    match res with
    | result.TypeEq (s2, is_eq) ->
        testing (txt "input:" </> txt s1 <+> txt "=" <+> txt s2)
        let τ1, ϕ1 = tchk.parse_fxty_expr s1
        let τ2, ϕ2 = tchk.parse_fxty_expr s2
        testing (txt "parsed:" </> fmt "%O" τ1 <+> txt "=" <+> fmt "%O" τ2)
        let t1 = ϕ1.ftype
        let t2 = ϕ2.ftype
        let k1 = ϕ1.kind
        let k2 = ϕ2.kind
        let b1 = ϕ1.is_equivalent ϕ2
        let b2 = t1.is_equivalent t2
        let b3 = k1.is_equivalent k2
        let infs =
            infs0 @
            [ "flex types", ok_or_no_info b1 (fxty ϕ1 <+> txt "=" <+> fxty ϕ2)
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

    | result.TypedOk (Some s) ->        
        let ϕok = tchk.parse_fxty_expr (s, not (ed.is_enabled flag.NoAutoGen)) |> snd
        in
            try
                let ϕres, infs1 = typecheck_expr_or_decl ()
                let compare_test = if ed.is_enabled flag.Verbatim then compare_test_verbatim else compare_test_eq
                let b3 = compare_test ϕres ϕok
                let infs1 = infs0 @ infs1 b3
                let infs2 = expected_infos ϕok
                in
                    match b3 with
                    | true, true, true  -> test_ok "all ok" infs1
                    | true, false, true -> test_weak_ok "F-type is wrong" (infs1 @ infs2)
                    | false, true, true -> test_weak_ok "flex type is wrong" (infs1 @ infs2)
                    | true, false, false
                    | false, true, false -> test_failed "types are ok but kind is wrong" (infs1 @ infs2)
                    | _                  -> test_failed "types are wrong" (infs1 @ infs2)
            with :? static_error as e ->
                test_failed (sprintf "unwanted %s" (error_name_of_exn e)) <| infs0 @ static_error_infos s1 e @ expected_infos ϕok

    | result.TypedOk None ->        
        try
            let _, infs1 = typecheck_expr_or_decl ()
            let infs1 = infs0 @ infs1 (true, true, true)
            in
                test_ok "typed ok" infs1
        with :? static_error as e ->
            test_failed (sprintf "unwanted %s" (error_name_of_exn e)) <| infs0 @ static_error_infos s1 e
                    
    | result.StaticError (T, codeo) ->
        assert (let t = typeof<static_error> in t = T || T.IsSubclassOf t)
        try
            let _, infs1 = typecheck_expr_or_decl ()
            let errname = error_name_of_type T
            in
                test_failed
                    (something (sprintf "expected %s code %d" errname) (sprintf "expected some %s" errname) codeo)
                    (infs0 @ infs1 (false, false, false))
        with :? static_error as e ->
            let tb = let t = e.GetType() in t = T || t.IsSubclassOf T
            let errname = error_name_of_exn e
            let cb = match codeo with
                     | None   -> true
                     | Some n -> n = e.code
            in
                (match tb, cb with
                | true, true   -> test_ok "justly rejected"
                | true, false  -> test_weak_ok (sprintf "%s is right but error code %d is wrong" errname e.code)
                | false, true  -> test_weak_ok (sprintf "error code %d is right but %s is wrong" e.code errname)
                | false, false -> test_failed (sprintf "wrong %s and code %d" errname e.code)
                ) <| infs0 @ static_error_infos s1 e


let score_infos scores =
    [score.Ok; score.Weak; score.Failed] @ scores   // trick for making countBy always count at least 1 for each kind of score
    |> List.countBy id
    |> List.sortBy (fst >> function score.Ok -> 1 | score.Weak -> 2 | score.Failed -> 3)
    |> List.map (fun (score, n) -> sprintf "%O" score, fmt "%d" (n  - 1))

let section_infos sec (span : TimeSpan) (scores : score list) =
    ["section", txt sec; "entries", fmt "%d" scores.Length; "cpu time", txt span.pretty; "results", pp_infos (score_infos scores)]

let test_section (tchk : typechecker) ((sec, flags, entries) : section) =
    let envs0 = tchk.envs
    let scores, span = cputime (List.mapi (fun i -> test_entry tchk { name = sec; num = i; flags = flags })) entries
    let infs = section_infos sec span scores
    L.pp (L.msg High) (pp_infos infs)
    if not <| flag.is_enabled flag.KeepBindingsAtEnd flags then
        tchk.envs <- envs0
    scores

let test_sections (secs : section list) =
    let tchk = new typechecker ()
    let scores, span = cputime (fun () -> List.map (test_section tchk) secs |> List.concat) () 
    let infs = section_infos (mappen_strings (fun (name, _, _) -> name) ", " secs) span scores
    L.pp (L.msg Unmaskerable) (pp_infos infs)
    List.sumBy (function score.Ok | score.Weak -> 1 | _ -> 0) scores


// shortcuts for unit tests

module Aux =
    let type_ok_ s l : result * flag list = result.TypedOk (Some s), l
    let type_is_ s l : result * flag list = result.TypedOk (Some s), [flag.Verbatim] @ l
    let type_eq_ s l : result * flag list = result.TypeEq (s, true), l
    let type_neq_ s l : result * flag list = result.TypeEq (s, false), l
    let ok_ l : result * flag list = result.TypedOk None, l

    let type_ok s = type_ok_ s []
    let type_is s = type_is_ s []
    let type_eq s = type_eq_ s []
    let type_neq s = type_neq_ s []
    let ok = ok_ []

    let wrong_< 'exn when 'exn :> static_error > codeo l : result * flag list = result.StaticError (typeof<'exn>, codeo), l
    let wrong_type_ = wrong_<type_error> None
    let wrong_syntax_ = wrong_<syntax_error> None
    let static_errn_ code = wrong_<static_error> (Some code)
    let type_errn_ code = wrong_<type_error> (Some code)
    let unbound_error_ = static_errn_ 10

    let wrong codeo = wrong_ codeo []
    let wrong_type = wrong_type_ []
    let wrong_syntax = wrong_syntax_ []
    let static_errn code = static_errn_ code []
    let type_errn code = type_errn_ code []
    let unbound_error = unbound_error_ []
