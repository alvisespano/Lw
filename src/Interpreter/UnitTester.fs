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
open Lw.Core.Typing
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
    | DisableWarning of int
    | DisableWarnings
    | DisableHint of int
    | DisableHints
    | EnableWarning of int
    | EnableWarnings
    | EnableHint of int
    | EnableHints
    | No of flag
with
    static member private fold_flags p flag flags =
        List.fold (fun r -> function flag' when flag = flag'     -> true
                                   | No flag' when flag = flag'  -> false
                                   | _                           -> r)
            false flags |> p

    static member is_enabled = flag.fold_flags id

[< RequireQualifiedAccess >]
type [< NoComparison; NoEquality >] result =
    | TypedOk of string option
    | StaticError of Type * int option
    | TypeEq of string * bool

[< RequireQualifiedAccess; CustomEquality; CustomComparison >]
type score = Ok | Failed | Weak
with
    override this.ToString () = this.pretty

    override x.Equals y = CustomCompare.equals_by score.to_int x y

    override x.GetHashCode () = CustomCompare.hash_by score.to_int x
    
    interface System.IComparable with
        member x.CompareTo y = CustomCompare.compare_by score.to_int x y

    member this.pretty =
        match this with
        | score.Ok      -> "OK"
        | score.Failed  -> "FAILED"
        | score.Weak    -> "WEAK"

    static member to_int = function
        | score.Ok     -> 1
        | score.Weak   -> 2
        | score.Failed -> 3


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
    member this.all_flags = this.flags @ this.section.flags
    member this.is_flag_enabled fl = flag.is_enabled fl this.all_flags
    member this.enabled_flags = List.filter this.is_flag_enabled this.all_flags


let entry_info sec n = "entry", txt (sprintf "#%d in section \"%s\"" (n + 1) sec)
let ok_or_no_info b doc = (txt (sprintf "(%s)" (if b then "OK" else "NO"))) <+> doc


// logging and pprint shorcuts
//

type logger with
    member __.pp (L : PrintfFormat<_, _, _, _> -> _) doc = L "%s" <| render None doc

//let test_ok (ed : entry_data) result infs =
//    if ed.is_flag_enabled flag.ShowSuccessful then
//        L.pp L.test_ok (pp_infos (["result", result] @ infs))
//    score.Ok
//
//let test_failed reason infs = L.pp L.test_failed (pp_infos (["reason", reason] @ infs)); score.Failed
//
//let test_weak_ok issue infs = L.pp L.test_weak_ok (pp_infos (["issue", issue] @ infs)); score.Weak

       


// compares
//

let fxty_compare_test eq_fxty eq_ty eq_kind (ϕres : fxty) (ϕok : fxty) =
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

let fxty_compare_test_eq = fxty_compare_test (fun (x : fxty) y -> x.is_equivalent y) (fun (x : ty) y -> x.is_equivalent y) (fun (x : kind) y -> x.is_equivalent y)   

let fxty_compare_test_verbatim =
    let p x =
        use N = var.reset_normalization
        let r = sprintf "%O" x
        in
            r.Replace (Config.Printing.dynamic.flex_forall, Config.Printing.dynamic.forall)     // replace capitalized Forall with the lowercase one
    let (===) a b = p a = p b
    in
        fxty_compare_test (===) (===) (===)

let tyeq_compare_test (ϕ1 : fxty) (ϕ2 : fxty) =
    let t1 = ϕ1.ftype
    let t2 = ϕ2.ftype
    let k1 = ϕ1.kind
    let k2 = ϕ2.kind
    let b1 = ϕ1.is_equivalent ϕ2
    let b2 = t1.is_equivalent t2
    let b3 = k1.is_equivalent k2
    in
        b1, b2, b3


// testers
//
                                 
let parse_expr_or_decl s =
    try parsed.Expr (parse_expr s)
    with :? syntax_error ->
        try parsed.Decl (parse_decl s)
        with :? syntax_error -> reraise ()
           | e               -> unexpected "syntax error while parsing expression or declaration: %s\n%O" __SOURCE_FILE__ __LINE__ s e


let test_entry (tchk : typechecker) sd ((s1, (res, flags)) : entry) =
    let entry_infs = [ entry_info sd.name sd.num ]
    let ed = { section = sd; input = s1; flags = flags }

    let print_result score result infs =
        let infs = pp_infos (["result", result] @ infs)
        match score with
        | score.Ok when ed.is_flag_enabled flag.ShowSuccessful -> L.pp L.test_ok infs
        | score.Weak -> L.pp L.test_weak_ok infs
        | score.Failed -> L.pp L.test_failed infs
        | _ -> ()

    let testing doc =
        if ed.is_flag_enabled flag.ShowInput then
            L.pp L.testing doc


    // deal with flags for hint and warning manipulation
    use wtracer = Report.warnings.tracer
    use htracer = Report.hints.tracer
    use D =
        let disps =
            let undo f g = f (); disposable_by g
            let restore (r : Report.Alert.manager) = let x = r.state in fun () -> r.state <- x
            let disable_all (r : Report.Alert.manager) = undo (fun () -> r.disable_all) (restore r)
            let disable1 (r : Report.Alert.manager) n = undo (fun () -> r.disable n) (restore r)
            let enable_all (r : Report.Alert.manager) = undo (fun () -> r.enable_all) (restore r)
            let enable1 (r : Report.Alert.manager) n = undo (fun () -> r.enable n) (restore r)
            let w = Report.warnings
            let h = Report.hints
            in
              [ for flag in ed.enabled_flags do
                    match flag with
                    | flag.DisableWarnings  -> yield disable_all w
                    | flag.DisableHints     -> yield disable_all h
                    | flag.DisableWarning n -> yield disable1 w n
                    | flag.DisableHint n    -> yield disable1 h n

                    | flag.EnableWarnings  -> yield enable_all w
                    | flag.EnableHints     -> yield enable_all h
                    | flag.EnableWarning n -> yield enable1 w n
                    | flag.EnableHint n    -> yield enable1 h n
                    
                    | _ -> ()         
              ]
        in
            disposable_by (fun () -> for d in List.rev disps do d.Dispose ())   // dispose in reverse order for restoring state correctly

    let expected_hints =
        Computation.B.set {
            for flag in ed.enabled_flags do
                match flag with
                | flag.DisableHint n
                | flag.EnableHint n -> yield n
                | _ -> ()
        }
    let expected_warns =
        Computation.B.set {
            for flag in ed.enabled_flags do
                match flag with
                | flag.DisableWarning n
                | flag.EnableWarning n -> yield n
                | _ -> ()
        }

    let wh_infs () =
        let flatten (tr : Report.Alert.tracer) expected =
            let f n = sprintf "%d%s" n (if Set.contains n expected then "" else "(?)")
            in
                txt (mappen_stringables f ", " tr)
        in
            [ "warnings", flatten wtracer expected_warns
              "hints", flatten htracer expected_hints ]
    
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
                    if ed.is_flag_enabled flag.Unbind then
                        tchk.envs <- envs0
                    r

                | d -> not_implemented "%O" __SOURCE_FILE__ __LINE__ d
        in
            ϕ,
            (fun (ϕb, tb, kb) -> [ yield "translated", txt p.pretty_translated
                                   yield "inferred", pp_infos <| typed_infos (ok_or_no_info ϕb (fxty ϕ), 
                                                                       ok_or_no_info tb (ty ϕ.ftype),
                                                                       ok_or_no_info kb (kind ϕ.kind))])

    let wh_scores () =
        let l name (tr : Report.Alert.tracer) expected =
            let traced = Set.ofSeq tr
            let f set fmt = if not (Set.isEmpty set) then [score.Weak, sprintf fmt name (flatten_stringables ", " set)] else []
            in
                [ yield! f (traced - expected) "some unexpected %ss: %s"
                  yield! f (expected - traced) "some expected %ss were not shot: %s" ]
        in
            [ yield! l "warning" wtracer expected_warns
              yield! l "hint" htracer expected_hints ]

    match res with

    // type equality
    | result.TypeEq (s2, is_eq) ->
        testing (txt "input:" </> txt s1 <+> txt "=" <+> txt s2)
        let τ1, ϕ1 = tchk.parse_fxty_expr s1
        let τ2, ϕ2 = tchk.parse_fxty_expr s2
        testing (txt "parsed:" </> fmt "%O" τ1 <+> txt "=" <+> fmt "%O" τ2)
        let b1, b2, b3 = tyeq_compare_test ϕ1 ϕ2
        let infs =
            [ "flex types", ok_or_no_info b1 (fxty ϕ1 <+> txt "=" <+> fxty ϕ2)
              "F-types", ok_or_no_info b2 (ty ϕ1.ftype <+> txt "=" <+> ty ϕ2.ftype)
              "kinds", ok_or_no_info b3 (kind ϕ1.kind <+> txt "=" <+> kind ϕ2.kind) ]
        let ok' = if is_eq then score.Ok else score.Failed
        let failed' = if is_eq then score.Failed else score.Ok
        let scores = 
          [
            (match b1, b2, b3 with
            | true, true, true  -> ok', "types are equivalent" 
            | true, true, false -> failed', "types are equivalent but kinds are different" 
            | true, false, _    -> score.Weak, "flex types are equivalent but F-types are different"
            | false, true, _    -> score.Weak, "F-types are equivalent but flex types are different"
            | false, false, _   -> failed', "types are different")
          ]
        in
            scores, infs

    // typability with specific type result
    | result.TypedOk (Some s) ->        
        let ϕok = tchk.parse_fxty_expr (s, not (ed.is_flag_enabled flag.NoAutoGen)) |> snd            
        in
            try
                let ϕres, infs1 = typecheck_expr_or_decl ()
                let compare_test = if ed.is_flag_enabled flag.Verbatim then fxty_compare_test_verbatim else fxty_compare_test_eq
                let b3 = compare_test ϕres ϕok
                let infs = infs1 b3 @ expected_infos ϕok
                let scores =
                  [
                    (match b3 with
                    | true, true, true  -> score.Ok, "type is correct" 
                    | true, false, true -> score.Weak, "F-type is wrong"
                    | false, true, true -> score.Weak, "flex type is wrong"
                    | true, false, false
                    | false, true, false -> score.Failed, "types are ok but kind is wrong"
                    | _                  -> score.Failed, "types are wrong")
                  ]
                in
                    scores, infs

            with :? static_error as e ->
                [score.Failed, sprintf "unwanted %s" (error_name_of_exn e)],
                    static_error_infos s1 e @ expected_infos ϕok

    // generic typability
    | result.TypedOk None ->        
        try
            let _, infs1 = typecheck_expr_or_decl ()
            let infs1 = infs1 (true, true, true)
            in
                [score.Ok, "typed successfully"], infs1
        with :? static_error as e ->
            [score.Failed, sprintf "unwanted %s" (error_name_of_exn e)], static_error_infos s1 e

    // expected static error                
    | result.StaticError (T, codeo) ->
        assert (let t = typeof<static_error> in t = T || T.IsSubclassOf t)
        try
            let _, infs1 = typecheck_expr_or_decl ()
            let errname = error_name_of_type T
            in
                [score.Failed, something (sprintf "expected %s code %d" errname) (sprintf "expected some %s" errname) codeo],
                    (infs1 (false, false, false))
        with :? static_error as e ->
            let tb = let t = e.GetType () in t = T || t.IsSubclassOf T
            let errname = error_name_of_exn e
            let cb = match codeo with
                     | None   -> true
                     | Some n -> n = e.code
            let scores =
              [
                yield (match tb, cb with
                       | true, true   -> score.Ok, "justly rejected"
                       | true, false  -> score.Weak, sprintf "%s is right but error code %d is wrong" errname e.code
                       | false, true  -> score.Weak, sprintf "error code %d is right but %s is wrong" e.code errname
                       | false, false -> score.Failed, sprintf "wrong %s and code %d" errname e.code)
              ]
            in
                scores, static_error_infos s1 e

    // process score rusults
    |> fun (scores, infs) ->
        let infs = entry_infs @ infs @ wh_infs ()
        let scores = wh_scores () @ scores    // append scores related to warnings and hints
        let score1 = List.maxBy fst scores |> fst
        let msgs = List.filter (fun (score, _) -> score <= score1) scores |> List.map snd
        let result =
            match List.length msgs with
            | 0 -> txt "unknown reason"
            | 1 -> txt msgs.[0]
            | len -> pp_infos [ for i = 1 to len do yield sprintf "%d" i, txt msgs.[i - 1] ]
        print_result score1 result infs
        score1


// section management
//

let score_infos scores =
    [score.Ok; score.Weak; score.Failed] @ scores   // trick for making countBy always count at least 1 for each kind of score
    |> List.countBy id
    |> List.sortBy fst
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



// some shortcuts to be used by unit tests
//

module Aux =
    open Lw.Core.Typing.Report

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
    let unbound_error_ = static_errn_ Error.Code.unbound_symbol

    let wrong codeo = wrong_ codeo []
    let wrong_type = wrong_type_ []
    let wrong_syntax = wrong_syntax_ []
    let static_errn code = static_errn_ code []
    let type_errn code = type_errn_ code []
    let unbound_error = unbound_error_ []
