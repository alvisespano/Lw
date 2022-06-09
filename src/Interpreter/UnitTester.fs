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
open Lw.Core.Typing.Report
open PPrint

type logger with
    member __.pp (L : PrintfFormat<_, _, _, _> -> _) doc = L "%s" <| render None doc
    member this.testing fmt = this.log_unleveled "TEST" Config.Log.test_color fmt
    member this.test_ok fmt = this.log_unleveled "OK" Config.Log.test_ok_color fmt
    member this.test_weak_ok fmt = this.log_unleveled "WEAK" Config.Log.test_weak_ok_color fmt
    member this.test_failed fmt = this.log_unleveled "FAIL" Config.Log.test_failed_color fmt


[< NoComparison >]
type flag =
    | Verbatim
    | Unbind
    | KeepAllBindings
    | ShowSuccessful
    | Verbose
    | NoAutoGen
    | HideWarning of int
    | HideWarnings
    | HideHint of int
    | HideHints
    | ShowWarning of int
    | ShowWarnings
    | ShowHint of int
    | ShowHints
    | Dependencies of section list
with
//    static member try_pick (|Flag|_|) flgs = List.tryPick (function Flag x -> Some x | _ -> None) flgs
    static member choose (|Flag|_|) flgs = List.choose (function Flag x -> Some x | _ -> None) flgs
    static member is_enabled (|Flag|_|) flgs = Option.isSome <| List.tryPick (|Flag|_|) flgs 
    member flg.is_in flgs = flag.is_enabled (function flg' when flg' = flg -> Some () | _ -> None) flgs


and [< NoComparison; CustomEquality; RequireQualifiedAccess  >] result =
    | TypedOk of string option
    | StaticError of (Type * int option)
    | TypeEq of (string * bool)
    | Custom of (unit -> bool)

    override this.GetHashCode () =
        match this with
        | TypedOk x     -> hash (1, x)
        | StaticError x -> hash (2, x)
        | TypeEq x      -> hash (3, x)
        | Custom _      -> unexpected_case __SOURCE_FILE__ __LINE__ this
    
    override x.Equals yobj =
        CustomCompare.equals_with (fun a b ->
            match a, b with
            | TypedOk x, TypedOk y          -> x = y
            | TypeEq x, TypeEq y            -> x = y
            | StaticError x, StaticError y  -> x = y
            | _                             -> false)
            x yobj

and entry = string * (result * flag list)
and section = { name : string; flags : flag list; entries : entry list }



[< RequireQualifiedAccess; CustomEquality; CustomComparison >]
type score = Ok | Weak | Failed
with     
    override x.Equals y = CustomCompare.equals_by int x y
    override x.GetHashCode () = CustomCompare.hash_by int x
    
    interface System.IComparable with
        member x.CompareTo y = CustomCompare.compare_by int x y

    override this.ToString () = this.pretty
    member this.pretty =
        match this with
        | score.Ok      -> "OK"
        | score.Failed  -> "FAILED"
        | score.Weak    -> "WEAK"

    static member op_Implicit s =
        match s with
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
let error_name_of_exn (e : static_error) = error_name_of_type (e.GetType ())


// PPrint facilities
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

let expected_static_error_infos T ecodeo =
    let t = error_name_of_type T
    in
        ["expected", txt <| match ecodeo with None -> t | Some n -> sprintf "%s %d" t n ]


// entries and sections
//

type section_data (sec : section) =
    member this.is_flag_enabled (|Flag|_|) = flag.is_enabled (|Flag|_|) this.flags
    member this.contains_flag (flg : flag) = flg.is_in this.flags
    member val name = sec.name
    member val entries = sec.entries
    abstract flags : flag list
    default val flags = sec.flags

type entry_data (sd : section_data, num, input, res, flags) =
    inherit section_data { name = sd.name; flags = sd.flags; entries = sd.entries }
    member val input = input
    member val num = num
    member val res = res
    override val flags = sd.flags @ flags   // order is right: section flags before entry flags

let entry_info sec n = "entry", txt (sprintf "#%d in section \"%s\"" (n + 1) sec)
let ok_or_no_info b doc = (txt (sprintf "(%s)" (if b then "OK" else "NO"))) <+> doc



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
    let eq a b = p a = p b
    in
        fxty_compare_test eq eq eq

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


let test_entry (tchk : typechecker) (sd : section_data) num ((input, (res, flags)) : entry) =
    let entry_infs = [ entry_info sd.name num ]
    let ed = new entry_data (sd, num, input, res, flags)

    let print_result score msgs infs =
        let result =
            match List.length msgs with
            | 0 -> txt "unknown reason"
            | 1 -> txt msgs.[0]
            | len -> pp_infos [ for i = 1 to len do yield sprintf Config.UnitTest.multiple_results_item_fmt i, txt msgs.[i - 1] ]
        let infs = pp_infos ([sprintf "result%s" (if List.length msgs > 1 then "s" else ""), result] @ infs)
        match score with
        | score.Ok when ed.contains_flag ShowSuccessful -> L.pp L.test_ok infs
        | score.Weak -> L.pp L.test_weak_ok infs
        | score.Failed -> L.pp L.test_failed infs
        | _ -> ()

    let log doc =
        if ed.contains_flag Verbose then
            L.pp L.testing doc


    // deal with flags for hint and warning manipulation
    use D =
        // set initial state of managers
        Report.warnings.disable_all
        Report.hints.disable_all
        // create disposables for both managers
        let f (m : Alert.manager) = let x = m.state in disposable_by <| fun () -> m.state <- x
        in
            disposable_by <| fun () -> (f Report.warnings).Dispose (); (f Report.hints).Dispose ()
         
    use wtracer = Report.warnings.tracer
    use htracer = Report.hints.tracer

    let expected_hints, expected_warns =
        let U = Alert.cset.universe
        let E = Alert.cset.empty
        let W = Report.warnings
        let H = Report.hints
        in
            List.fold (fun (h, w) -> function
                        | HideWarnings  -> W.disable_all; h, U
                        | HideHints     -> H.disable_all; U, w
                        | HideWarning n -> W.disable n; h, w.add n
                        | HideHint n    -> H.disable n; h.add n, w

                        | ShowWarnings  -> W.enable_all; h, U
                        | ShowHints     -> H.enable_all; U, w
                        | ShowWarning n -> W.enable n; h, w.add n
                        | ShowHint n    -> H.enable n; h.add n, w
                        | _             -> h, w)
                (E, E) ed.flags

    let wh_infs () =
        let flatten (tr : Alert.tracer) (expected : Alert.cset) =
            let f n = sprintf "%d%s" n (if expected.contains n then "" else "(?)")
            in
                txt (mappen_stringables f ", " tr)
        in
            [ "warnings", flatten wtracer expected_warns
              "hints", flatten htracer expected_hints ]
    
    let typecheck_expr_or_decl () =
        log (txt "input:" </> txt ed.input)
        let p = parse_expr_or_decl ed.input
        log (txt "parsed:" </> fmt "%O" p)
        let ϕ =
            match p with
            | parsed.Expr e ->
                tchk.W_expr e

            | parsed.Decl d ->
                let envs0 = tchk.envs
                tchk.W_decl d
                match d.value with
                | D_RecBind [{ patt = ULo (P_SimpleVar (x, _)) }]
                | D_Bind [{ patt = ULo (P_SimpleVar (x, _)) }] ->
                    let r = tchk.lookup_var_Γ x
                    if ed.contains_flag Unbind then
                        tchk.envs <- envs0
                        log (txt "restoring:" </> txt x <+> txt ":" <+> fxty (tchk.lookup_var_Γ x))
                    r

                | d -> not_implemented "%O" __SOURCE_FILE__ __LINE__ d
        in
            ϕ,
            (fun (ϕb, tb, kb) -> [ yield "translated", txt p.pretty_translated
                                   yield "inferred", pp_infos <| typed_infos (ok_or_no_info ϕb (fxty ϕ), 
                                                                       ok_or_no_info tb (ty ϕ.ftype),
                                                                       ok_or_no_info kb (kind ϕ.kind))])

    let wh_scores () =
        let l name (tr : Alert.tracer) (expected : Alert.cset) =
            let traced = tr |> Set |> Alert.cset
            //L.debug Normal "%s: traced = %O  expected = %O" name traced expected
            let f (cset : Alert.cset) fmt = if not (cset.is_empty || cset.is_complemented) then [score.Weak, sprintf fmt name cset.pretty] else []
            in
                [ yield! f (traced - expected) "some unexpected %ss: %s"
                  yield! f (expected - traced) "some expected %ss were not shot: %s" ]
        in
            [ yield! l "warning" wtracer expected_warns
              yield! l "hint" htracer expected_hints ]

    match res with

    // custom test
    | result.Custom f ->
        log (txt "custom test")
        (try if f () then (score.Ok, "custom test successful") else (score.Failed, "custom test failed")
         with e -> (score.Failed, sprintf "custom test raised exception: %s" (pretty_exn_and_inners e))), []

    // type equality
    | result.TypeEq (s2, is_eq) ->
        log (txt "input:" </> txt input <+> txt "=" <+> txt s2)
        let τ1, ϕ1 = tchk.parse_fxty_expr input
        let τ2, ϕ2 = tchk.parse_fxty_expr s2
        log (txt "parsed:" </> fmt "%O" τ1 <+> txt "=" <+> fmt "%O" τ2)
        let b1, b2, b3 = tyeq_compare_test ϕ1 ϕ2
        let infs =
            [ "flex types", ok_or_no_info b1 (fxty ϕ1 <+> txt "=" <+> fxty ϕ2)
              "F-types", ok_or_no_info b2 (ty ϕ1.ftype <+> txt "=" <+> ty ϕ2.ftype)
              "kinds", ok_or_no_info b3 (kind ϕ1.kind <+> txt "=" <+> kind ϕ2.kind) ]
        let ok' = if is_eq then score.Ok else score.Failed
        let failed' = if is_eq then score.Failed else score.Ok
        let score = 
            match b1, b2, b3 with
            | true, true, true  -> ok', "types are equivalent" 
            | true, true, false -> failed', "types are equivalent but kinds are different" 
            | true, false, _    -> score.Weak, "flex types are equivalent but F-types are different"
            | false, true, _    -> score.Weak, "F-types are equivalent but flex types are different"
            | false, false, _   -> failed', "types are different"
        in
            score, infs

    // typability with specific type result
    | result.TypedOk (Some s) ->        
        let ϕok = tchk.parse_fxty_expr (s, not (ed.contains_flag NoAutoGen)) |> snd            
        in
            try
                let ϕres, infs1 = typecheck_expr_or_decl ()
                let compare_test = if ed.contains_flag Verbatim then fxty_compare_test_verbatim else fxty_compare_test_eq
                let b3 = compare_test ϕres ϕok
                let infs = infs1 b3 @ expected_infos ϕok
                let score =
                    match b3 with
                    | true, true, true  -> score.Ok, "type is correct" 
                    | true, false, true -> score.Weak, "F-type is wrong"
                    | false, true, true -> score.Weak, "flex type is wrong"
                    | true, false, false
                    | false, true, false -> score.Failed, "types are ok but kind is wrong"
                    | _                  -> score.Failed, "types are wrong"          
                in
                    score, infs

            with :? static_error as e ->
                (score.Failed, sprintf "unwanted %s" (error_name_of_exn e)),
                    static_error_infos input e @ expected_infos ϕok

    // generic typability
    | result.TypedOk None ->        
        try
            let _, infs1 = typecheck_expr_or_decl ()
            let infs1 = infs1 (true, true, true)
            in
                (score.Ok, "typed successfully"), infs1
        with :? static_error as e ->
            (score.Failed, sprintf "unwanted %s" (error_name_of_exn e)), static_error_infos input e

    // expected static error                
    | result.StaticError (T, codeo) ->
        assert (let t = typeof<static_error> in t = T || T.IsSubclassOf t)
        try
            let _, infs1 = typecheck_expr_or_decl ()
            let errname = error_name_of_type T
            in
                (score.Failed, something (sprintf "expected %s code %d" errname) (sprintf "expected some %s" errname) codeo),
                    (infs1 (false, false, false))
        with :? static_error as e ->
            let tb = let t = e.GetType () in t = T
            let errname = error_name_of_exn e
            let cb = match codeo with
                     | None   -> true
                     | Some n -> n = e.code
            let score =
                match tb, cb with
                | true, true   -> score.Ok, "correctly rejected"
                | true, false  -> score.Weak, sprintf "%s is right but error code %d is wrong" errname e.code
                | false, true  -> score.Failed, sprintf "wrong %s" errname
                | false, false -> score.Failed, sprintf "wrong code %d and %s" e.code errname
            in
                score, static_error_infos input e @ expected_static_error_infos T codeo

    // process score rusults
    |> fun (score0, infs) ->
        let infs = entry_infs @ infs @ match res with result.Custom _ -> [] | _ -> wh_infs ()   // appending warns and hints doesn't make sense for Custom
        let scores = score0 :: match res with result.Custom _ -> [] | _ -> wh_scores ()
        let score1 = List.maxBy fst scores |> fst
        let msgs = List.filter (fun (score, _) -> score <= score1) scores |> List.map snd
        print_result score1 msgs infs
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

type tested_sections () =
    let tbl = new Collections.Generic.Dictionary<string, score list> ()
    
    member __.search s =
        match tbl.TryGetValue s with
        | true, scores -> Some scores
        | false, _     -> None

    member __.add s scores = tbl.Add (s, scores)

let private tested_sections = new tested_sections ()

let rec test_section (tchk : typechecker) (sec : section) =
    let sd = new section_data (sec)
    match tested_sections.search sd.name with
    | Some scores -> scores
    | None ->
        let _ = sd.flags |> flag.choose (function 
            | Dependencies secs -> Some <| test_sections tchk [ for sec in secs do yield { sec with flags = KeepAllBindings :: sec.flags } ]
            | _ -> None)
        let envs0 = tchk.envs
        let scores, span = cputime (List.mapi (fun i e -> let r = test_entry tchk sd i e in r)) sd.entries
        let infs = section_infos sd.name span scores
        L.pp (L.msg High) (pp_infos infs)
        if not <| KeepAllBindings.is_in sd.flags then
            tchk.envs <- envs0
        tested_sections.add sd.name scores
        scores

and test_sections (tchk : typechecker) (secs : section list) =
    let scores, span = cputime (fun () -> List.map (test_section tchk) secs |> List.concat) () 
    let infs = section_infos (mappen_strings (fun sec -> sec.name) ", " secs) span scores
    L.pp (L.msg Unmaskerable) (pp_infos infs)
    List.sumBy (function score.Ok | score.Weak -> 1 | _ -> 0) scores

let test_sections_from_scratch = test_sections (new typechecker ())


// some shortcuts to be used by unit tests
//

module Aux =
    let typed_ok_as_ s l : result * flag list = result.TypedOk (Some s), l
    let typed_ok_ l : result * flag list = result.TypedOk None, l
    let type_is_ s l : result * flag list = result.TypedOk (Some s), [Verbatim] @ l
    let type_eq_ s l : result * flag list = result.TypeEq (s, true), l
    let type_neq_ s l : result * flag list = result.TypeEq (s, false), l

    let custom_ f l = "", (result.Custom f, l)
    let custom f = custom_ f []

    let typed_ok_as s = typed_ok_as_ s []
    let typed_ok = typed_ok_ []
    let type_is s = type_is_ s []
    let type_eq s = type_eq_ s []
    let type_neq s = type_neq_ s []

    let wrong_< 'exn when 'exn :> static_error > codeo l : result * flag list = result.StaticError (typeof<'exn>, codeo), l
    let wrong_type_ = wrong_<type_error> None
    let wrong_syntax_ = wrong_<syntax_error> None
    let static_errn_ code = wrong_<static_error> (Some code)
    let type_errn_ code = wrong_<type_error> (Some code)
    let unbound_symbol_error_ = static_errn_ Error.Code.unbound_symbol

    let wrong codeo = wrong_ codeo []
    let wrong_type = wrong_type_ []
    let wrong_syntax = wrong_syntax_ []
    let static_errn code = static_errn_ code []
    let type_errn code = type_errn_ code []
    let unbound_symbol_error = unbound_symbol_error_ []
