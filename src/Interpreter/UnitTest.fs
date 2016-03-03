(*
 * Lw
 * Test.fs: test modules
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.UnitTest

#if UNIT_TEST

open System
open FSharp.Common
open FSharp.Common.Log
open Lw.Core
open Lw.Core.Parsing
open Lw.Core.Globals
open Lw.Core.Absyn
open Lw.Core.Typing.Defs
open Lw.Core.Typing.Inference
open Lw.Core.Typing.Meta
open Lw.Core.Typing.Ops
open Lw.Core.Typing.Report
open Lw.Core.Typing.StateMonad
open PPrint

type logger with
    member this.test pri fmt = this.custom Config.Log.test_color "TEST" Min pri fmt
    member this.test_ok fmt = this.custom Config.Log.test_ok_color "OK" Min Low fmt
    member this.test_weak_ok fmt = this.custom Config.Log.test_weak_ok_color "WEAK" Min Low fmt
    member this.test_failed fmt = this.custom_error Config.Log.test_failed_color "FAIL" fmt

[< RequireQualifiedAccess >]
type flag =
    | Verbatim

[< RequireQualifiedAccess >]
type [< NoComparison; NoEquality >] result =
    | Ok of string option * flag list
    | Wrong of Type

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
    let mutable st = { state.empty with Γ = Intrinsic.envs.envs0.Γ; γ = Intrinsic.envs.envs0.γ }

    member private __.unM f x =
        let ctx0 = context.top_level
        let r, st1 = f ctx0 x st
        st <- st1
        r
                
    member this.W_expr e = this.unM W_expr e
    member this.W_decl d = this.unM W_decl d
    member this.Wk_and_eval_ty_expr_fx τ = this.unM Wk_and_eval_ty_expr_fx τ
    
    member __.auto_generalize loc (t : ty) = t.auto_generalize loc st.Γ
    member __.lookup_var_Γ x = (st.Γ.lookup (Jk_Var x)).scheme.fxty

    member this.parse_expected_ty_expr s =
        let τ =
            try parse_ty_expr s
            with :? syntax_error as e -> unexpected "syntax error while parsing type expression: %s\n%O" __SOURCE_FILE__ __LINE__ s e
        let ϕ, k = this.Wk_and_eval_ty_expr_fx τ
        assert (ϕ.kind = k)
        let ϕ =
            match ϕ with
            | Fx_F_Ty t -> Fx_F_Ty <| this.auto_generalize (new location ()) t
            | _         -> ϕ
        in
            ϕ

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
        

let parse_expr_or_decl s =  // TODO: support parsing of type expressions and kinds as well, so everything can be tested
    try parsed.Expr (parse_expr s)
    with :? syntax_error ->
        try parsed.Decl (parse_decl s)
        with :? syntax_error -> reraise ()
           | e               -> unexpected "syntax error while parsing expression or declaration: %s\n%O" __SOURCE_FILE__ __LINE__ s e



// PPrint extensions
//
      
let colon2 = txt Config.Printing.kind_annotation_sep

let any x = txt (use N = var.reset_normalization in sprintf "%O" x)   // normalize vars in case parameter x has type ty of fxty

let pp_infos l =
    let l = Seq.map (fun (s : string, doc) -> sprintf "%s: " (s.TrimEnd [|':'; ' '|]), doc) l
    let w = Seq.maxBy (fst >> String.length) l |> fst |> String.length
    in
      [ for s : string, doc : Doc in l do
            yield (txt s |> fill w) </> doc
      ] |> vsep |> align

let typed_infos (ϕ, t, k) = ["flex type", ϕ; "F-type", t; "kind", k]

let expected_infos (ϕok : fxty) = ["expected", pp_infos <| typed_infos (any ϕok, any ϕok.ftype, any ϕok.kind)]

let static_error_infos (input : string) (e : static_error) =
    let term =
        let x = e.location.absolute_col
        let y = e.location.absolute_end_col
        in
            input.Substring (x, y - x)
    in
        ["raised", txt (e.header.ToUpper ()); "at", any e.location; "term", txt term; "message", txt e.message_body]


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

type var with
    member this.anonymize =
        match this with
        | Va (n, _) -> Va (n, None)

type kind with
    member this.anonymize_vars =
        match this with
        | K_Var α        -> K_Var α.anonymize
        | K_Cons (x, ks) -> K_Cons (x, List.map (fun (k : kind) -> k.anonymize_vars) ks)

type ty with
    member this.anonymize_vars =
        match this with
        | T_Forall (α, t)        -> T_Forall (α.anonymize, t.anonymize_vars)
        | T_Cons (x, k)          -> T_Cons (x, k.anonymize_vars)
        | T_Var (α, k)           -> T_Var (α.anonymize, k.anonymize_vars)
        | T_HTuple ts            -> T_HTuple (List.map (fun (t : ty) -> t.anonymize_vars) ts)
        | T_App (t1, t2)         -> T_App (t1.anonymize_vars, t2.anonymize_vars)
        | T_Closure (x, Δ, τ, k) -> T_Closure (x, Δ, τ, k.anonymize_vars)

type fxty with
    member this.anonymize_vars =
        match this with
        | Fx_Forall ((α, t1), t2) -> Fx_Forall ((α.anonymize, t1.anonymize_vars), t2.anonymize_vars)
        | Fx_Bottom k             -> Fx_Bottom k.anonymize_vars
        | Fx_F_Ty t               -> Fx_F_Ty t.anonymize_vars


let compare_test eq_ty eq_fxty eq_kind (ϕres : fxty) (ϕok : fxty) =
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

let compare_test_eq = compare_test (=) (=) (=)

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

let test_entry (tchk : typechecker) sec n ((input, res) : entry) =
    let typecheck1 s =
        testing Min (txt "input:" </> txt s)
        let p = parse_expr_or_decl s
        testing Low (txt "parsed:" </> any p)
        let ϕ =
            match p with
            | parsed.Expr e -> tchk.W_expr e
            | parsed.Decl d ->
                tchk.W_decl d
                match d.value with
                | D_Bind [{ patt = ULo (P_Var x) }] -> tchk.lookup_var_Γ x
                | _                                 -> decl_dummy_ty
        let inf o b = (txt (sprintf "(%s)" (if b then "OK" else "NO"))) <+> any o
        in
            ϕ, fun (ϕb, tb, kb) -> [ "entry", txt (sprintf "#%d in section \"%s\"" (n + 1) sec)
                                     "translated", txt p.pretty_translated
                                     "inferred", pp_infos <| typed_infos (inf ϕ ϕb, inf ϕ.ftype tb, inf ϕ.kind kb) ]
    in
        match res with
        | result.Ok (so, flags) ->
            let is_enabled flag = List.contains flag flags
            let ϕok =
                match so with
                | Some s -> try tchk.parse_expected_ty_expr s
                            with e -> unexpected "%s" __SOURCE_FILE__ __LINE__ (pretty_exn_and_inners e)   
                | None   -> decl_dummy_ty
            in
                try
                    let ϕres, infs1 = typecheck1 input
                    let compare_test = if is_enabled flag.Verbatim then compare_test_verbatim else compare_test_eq
                    let b3 = compare_test ϕres ϕok
                    let infs2 = expected_infos ϕok
                    let infs1 = infs1 b3
                    in
                        match b3 with
                        | true, true, true  -> test_ok "all ok" infs1
                        | true, false, true -> test_weak_ok "F-type are different" (infs1 @ infs2)
                        | false, true, true -> test_weak_ok "flex types are different" (infs1 @ infs2)
                        | true, false, false
                        | false, true, false -> test_failed "type is ok but kind is not" (infs1 @ infs2)
                        | _                  -> test_failed "expected to be ok" (infs1 @ infs2)
                with :? static_error as e ->
                    test_failed "unwanted static error" <| static_error_infos input e @ expected_infos ϕok
                    
        | result.Wrong T ->
            assert T.IsSubclassOf typeof<static_error>
            try
               let _, infs1 = typecheck1 input
               test_failed "expected to be wrong" <| infs1 (false, false, false) @ ["error expected", txt T.Name]
            with :? static_error as e ->
                if (let t = e.GetType() in t = T || t.IsSubclassOf T) then
                    test_ok "justly rejected" <| static_error_infos input e
                else reraise ()


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


// unit tests
//


module Tests =

    let type_ok s = result.Ok (Some s, [])
    let type_is s = result.Ok (Some s, [flag.Verbatim])
    let ok = result.Ok (None, [])
    let wrong< 'exn when 'exn :> static_error > = result.Wrong typeof<'exn>
    let wrong_type = wrong<type_error>
    let wrong_syntax = wrong<syntax_error>

    let test_in_fsharp = fun f (x : 'b) y -> ((f : _ -> 'a) x, y) : 'a * _

    
    let all : section list =
     [
      "Intrinsics",
      [
        "[]",                                       type_ok "list 'a"
        "[1; 2]",                                   type_ok "list int"
        "true 1",                                   wrong_type
        "true :: false :: true",                    wrong_type
        "'a' :: 'b' :: 'c' :: []",                  type_ok "list char"
        "'a' :: 'b' :: ['c']",                      type_ok "list char"
        "[true; 2]",                                wrong_type
        "(Some 0 :: [None]) :: [[Some 2]]",         type_ok "list (list (option int))"
        "[None]",                                   type_ok "list (option 'a)"
        "1 + 3",                                    type_ok "int"
        "if 1 then () else ()",                     wrong_type
      ]

      // TODO: make a section for testing the implementation of ty.Equals and fxty.Equals
      "Type Annotations",
      [
        "fun f x y -> ((f : 'a -> 'a) x, y) : _ * int",         type_ok "('a -> 'a) -> 'a -> int -> 'a * int"
        "fun f (x : 'x) y -> ((f : 'a -> _) x, y) : _ * int",   type_ok "('x -> 'a) -> 'x -> int -> 'a * int"
        "fun f (x : 'b) y -> ((f : _ -> 'a) x, y) : 'a * _",    type_ok "('b -> 'a) -> 'b -> 'c -> 'a * 'c"
      ]

      "Scoped Type Variables",
      [
        "let i (x : 'bar) = x in i 1, i true, i",   type_is "int * bool * (forall 'bar. 'bar -> 'bar)"
        "let y =
            let i (x : 'foo) = x
            in
                i 1, i true",                       type_ok "int * bool"    // generalization of scoped vars is valid
      ]

      "Lists",
      [
        "let rec map f = function
            | [] -> []
            | x :: xs -> f x :: map f xs",          type_ok "('a -> 'b) -> list 'a -> list 'b"
        "let rec fold f z = function
            | [] -> z
            | x :: xs -> fold f (f z x) xs",        type_ok "('b -> 'a -> 'b) -> 'b -> list 'a -> 'b"
      ]

      "ML Type Inference",
      [
        "fun x -> x",                               type_ok "forall 'a. 'a -> 'a"
        "fun f x -> f x",                           type_ok "forall 'a 'b. ('a -> 'b) -> 'a -> 'b"
        "fun a, b -> a",                            wrong_syntax
        "inc true",                                 wrong_type
        "let i = fun x -> x in i i",                type_ok "forall 'a. 'a -> 'a"
        "fun i -> i i",                             wrong_type // infinite type
        "fun i -> (i 1, i true)",                   wrong_type // polymorphic use of unannotated parameter
        "let id x = x",                             type_ok "forall 'a. 'a -> 'a"
        "let single x = [x]",                       type_ok "forall 'a. 'a -> list 'a"
      ]

      "HML",
      [
        "let i x = x in i 1, i true, i",            type_ok "int * bool * (forall 'a. 'a -> 'a)"
        "fun (i : forall 'a. 'a -> 'a) ->
            (i 1, i true)",                         type_ok "(forall 'a. 'a -> 'a) -> int * bool" // polymorphic use of annotated parameter
        "single id",                                type_ok "forall ('a :> forall 'b. 'b -> 'b). list 'a"
        "let const x y = x",                        type_ok "forall 'a 'b. 'a -> 'b -> 'a"
        "let const2 x y = y",                       type_ok "forall 'a 'b. 'a -> 'b -> 'b"
        "let choose x y = if x = y then x else y",  type_ok "forall 'a. 'a -> 'a -> 'a"
        "choose (fun x y -> x) (fun x y -> y)",     type_ok "forall 'a. 'a -> 'a -> 'a"
        "choose id",                                type_ok "forall ('a :> forall 'b. 'b -> 'b). 'a -> 'a"
      ]

     ]
    // impredicative application and higher rank arguments are fully supported    
    (*let HR = 
      [
        "xauto",    ok "forall a. (forall a. a -> a) -> a -> a"
        ,("auto", ok "(forall a. a -> a) -> (forall a. a -> a)")
        ,("\\(i :: forall a. a -> a) -> i i", ok "forall (a >= forall b. b -> b). (forall b. b -> b) -> a") -- ok "forall a. (forall a. a -> a) -> a -> a")
        ,("auto id", ok "forall a. a -> a")
        ,("apply auto id", ok "forall a. a -> a")
        ,("(single :: (forall a. a -> a) -> [forall a. a->a]) id", ok "[forall a. a-> a]")
        ,("runST (returnST 1)", ok "Int")
        ,("runST (newRef 1)", Wrong)
        ,("apply runST (returnST 1)", ok "Int")
        ,("map xauto ids", ok "forall a. [a -> a]")
        ,("map xauto (map xauto ids)", Wrong)
        ,("map auto ids", ok "[forall a. a -> a]")
        ,("map auto (map auto ids)", ok "[forall a. a -> a]")
        ,("head ids", ok "forall a. a -> a")
        ,("tail ids", ok "[forall a. a -> a]")
        ,("apply tail ids", ok "[forall a. a -> a]")
        ,("map head (single ids)", ok "[forall a. a -> a]")
        ,("apply (map head) (single ids)", ok "[forall a. a -> a]")

        -- check infinite poly types
        ,("(undefined :: some a. [a -> a] -> Int) (undefined :: some c. [(forall d. d -> c) -> c])", Wrong)
        ,("(undefined :: some a. [a -> a] -> Int) (undefined :: [(forall d. d -> d) -> (Int -> Int)])", Wrong)
        ,("(undefined :: some a. [a -> (forall b. b -> b)] -> Int) (undefined :: some c. [(forall d. d -> d) -> c])", ok "Int")

        -- these fail horribly in ghc: (choose auto id) is rejected while ((choose auto) id) is accepted -- so much for parenthesis :-)
        ,("choose id auto", ok "(forall a. a -> a) -> (forall a. a -> a)")
        ,("choose auto id", ok "(forall a. a -> a) -> (forall a. a -> a)")
        ,("choose xauto xauto", ok "forall a. (forall b. b -> b) -> a -> a")
        ,("choose id xauto", Wrong)
        ,("choose xauto id", Wrong)

        -- these fail too in ghc: (choose ids []) is accepted while (choose [] ids) is rejected
        ,("choose [] ids", ok "[forall a. a -> a]")
        ,("choose ids []", ok "[forall a. a -> a]")
    
        -- check escaping skolems
        ,("\\x -> auto x", Wrong)                                                                             -- escape in match
        ,("let poly (xs :: [forall a. a -> a]) = 1 in (\\x -> poly x)", Wrong)                              -- escape in apply
        ,("\\x -> (x :: [forall a. a -> a])", Wrong)                                                          -- escape in apply
        ,("\\x -> let polys (xs :: [forall a . a -> a]) = 1; f y = x in polys [f::some a. forall b. b -> a]",Wrong)  -- escape in unify (with rigid annotations, otherwise we get a skolem mismatch)
        ,("ids :: forall b. [forall a. a -> b]", Wrong)                                                       -- unify different skolems

        -- co/contra variance
        ,("let g (x::(forall a. a -> a) -> Int) = x id; f (x :: Int -> Int) = x 1 in g f", Wrong)                                      -- HMF is invariant
        ,("let g (x::(forall a. a -> a) -> Int) = x id; f (x :: Int -> Int) = x 1 in g (\\(x :: forall a. a -> a) -> f x)", ok "Int")  -- but we can always use explicit annotations to type such examples

        -- shared polymorphism
        ,("let f (x :: [forall a.a -> a]) = x in let g (x :: [Int -> Int]) = x in let ids = [id] in (f ids, g ids)", ok "([forall a. a -> a],[Int -> Int])")
      ]*)


    
let main () =
    test_sections Tests.all




(*
testsAll :: [Test]
testsAll
  = concat 
    [ testsHM             -- Hindley Milner
    , testsHR             -- Higher rank & impredicative
    , testsNary           -- N-ary applications, order of arguments
    , testsFlexible       -- Flexible bounds
    , testsExists         -- Encoding of existentials
    , testsRigidAnn       -- Rigid annotations
    , if (SupportPropagation `elem` features)      then testsProp     else []
    , if (SupportPropagateToArg `elem` features)   then testsPropArg  else []
    -- , testsRigid         -- Experimental "rigid" keyword
    ]

testsHM
  = -- standard Hindley-Milner tests
    [("\\x -> x", ok "forall a. a -> a")
    ,("\\f x -> f x", ok "forall a b. (a -> b) -> a -> b")
    ,("inc True", Wrong)
    ,("let i = \\x -> x in i i", ok "forall a. a -> a")
    ,("\\i -> i i", Wrong)              -- infinite type
    ,("\\i -> (i 1, i True)", Wrong)    -- polymorphic use of parameter
    ,("single id", ok "forall (a >= forall b. b -> b). [a]")
    ,("choose (\\x y -> x) (\\x y -> y)", ok "forall a. a -> a -> a")
    ,("choose id", ok "forall (a >= forall b. b -> b). a -> a")
    ]

testsHR
  = -- impredicative application and higher rank arguments are fully supported
    [("xauto",ok "forall a. (forall a. a -> a) -> a -> a")     -- just to show the types of xauto and auto
    ,("auto", ok "(forall a. a -> a) -> (forall a. a -> a)")
    ,("\\(i :: forall a. a -> a) -> i i", ok "forall (a >= forall b. b -> b). (forall b. b -> b) -> a") -- ok "forall a. (forall a. a -> a) -> a -> a")
    ,("auto id", ok "forall a. a -> a")
    ,("apply auto id", ok "forall a. a -> a")
    ,("(single :: (forall a. a -> a) -> [forall a. a->a]) id", ok "[forall a. a-> a]")
    ,("runST (returnST 1)", ok "Int")
    ,("runST (newRef 1)", Wrong)
    ,("apply runST (returnST 1)", ok "Int")
    ,("map xauto ids", ok "forall a. [a -> a]")
    ,("map xauto (map xauto ids)", Wrong)
    ,("map auto ids", ok "[forall a. a -> a]")
    ,("map auto (map auto ids)", ok "[forall a. a -> a]")
    ,("head ids", ok "forall a. a -> a")
    ,("tail ids", ok "[forall a. a -> a]")
    ,("apply tail ids", ok "[forall a. a -> a]")
    ,("map head (single ids)", ok "[forall a. a -> a]")
    ,("apply (map head) (single ids)", ok "[forall a. a -> a]")

    -- check infinite poly types
    ,("(undefined :: some a. [a -> a] -> Int) (undefined :: some c. [(forall d. d -> c) -> c])", Wrong)
    ,("(undefined :: some a. [a -> a] -> Int) (undefined :: [(forall d. d -> d) -> (Int -> Int)])", Wrong)
    ,("(undefined :: some a. [a -> (forall b. b -> b)] -> Int) (undefined :: some c. [(forall d. d -> d) -> c])", ok "Int")

    -- these fail horribly in ghc: (choose auto id) is rejected while ((choose auto) id) is accepted -- so much for parenthesis :-)
    ,("choose id auto", ok "(forall a. a -> a) -> (forall a. a -> a)")
    ,("choose auto id", ok "(forall a. a -> a) -> (forall a. a -> a)")
    ,("choose xauto xauto", ok "forall a. (forall b. b -> b) -> a -> a")
    ,("choose id xauto", Wrong)
    ,("choose xauto id", Wrong)

    -- these fail too in ghc: (choose ids []) is accepted while (choose [] ids) is rejected
    ,("choose [] ids", ok "[forall a. a -> a]")
    ,("choose ids []", ok "[forall a. a -> a]")
    
    -- check escaping skolems
    ,("\\x -> auto x", Wrong)                                                                             -- escape in match
    ,("let poly (xs :: [forall a. a -> a]) = 1 in (\\x -> poly x)", Wrong)                              -- escape in apply
    ,("\\x -> (x :: [forall a. a -> a])", Wrong)                                                          -- escape in apply
    ,("\\x -> let polys (xs :: [forall a . a -> a]) = 1; f y = x in polys [f::some a. forall b. b -> a]",Wrong)  -- escape in unify (with rigid annotations, otherwise we get a skolem mismatch)
    ,("ids :: forall b. [forall a. a -> b]", Wrong)                                                       -- unify different skolems

    -- co/contra variance
    ,("let g (x::(forall a. a -> a) -> Int) = x id; f (x :: Int -> Int) = x 1 in g f", Wrong)                                      -- HMF is invariant
    ,("let g (x::(forall a. a -> a) -> Int) = x id; f (x :: Int -> Int) = x 1 in g (\\(x :: forall a. a -> a) -> f x)", ok "Int")  -- but we can always use explicit annotations to type such examples

    -- shared polymorphism
    ,("let f (x :: [forall a.a -> a]) = x in let g (x :: [Int -> Int]) = x in let ids = [id] in (f ids, g ids)", ok "([forall a. a -> a],[Int -> Int])")
    ]

testsExists
  = [-- simulating existential types
     ("let pack x f    = \\(open :: some b. forall a. (a,a -> Int) -> b) -> open (x,f); \
          \unpack ex f = ex f; \
          \existsB = pack True (\\b -> if b then 1 else 0); \
          \existsI = pack 1 id; \
          \exs     = [existsB,existsI]\   
      \in unpack (head exs) (\\ex -> (snd ex) (fst ex))"     
     ,ok "Int")
    ]

testsRigidAnn
  = -- test 'rigid' annotations, i.e. annotations are taken literally and do not instantiate or generalize
    [("single (id :: forall a. a -> a)", ok "forall (a >= forall b. b -> b). [a]")
    ,("(id :: forall a. a -> a) 1", ok "Int")   -- not all annotations are rigid
    ,("(id :: some a. a -> a) 1", ok "Int")
    ,("\\x -> ((\\y -> x) :: some a. forall b. b -> a)", ok "forall a. forall (b >= forall c. c -> a). a -> b")
    ,("\\(f :: forall a. a -> a) -> ((f f) :: forall a. a -> a)", ok "forall (a >= forall b. b -> b). (forall b. b -> b) -> a")
    ,("revapp (id :: forall a. a -> a) auto", ok "forall a. a -> a")
    ,("choose inc id", ok "Int -> Int")
    ,("choose inc (id :: forall a. a -> a)", if SupportRigidAnnotations `elem` features then Wrong else ok "Int -> Int")
    ,("choose inc (id :: some a. a -> a)", ok "Int -> Int")
    ]

testsNary
  = -- tests n-ary applications
    [("revapp id auto", ok "forall a. a -> a")     
    ,("let f = revapp id in f auto", ok "forall a. a -> a")   
    ,("let f = revapp (id :: forall a. a -> a) in f auto", ok "forall a. a -> a") 
     -- check functions that return polymorphic values
    ,("head ids 1", ok "Int")
    ,("auto id 1", ok "Int")
    ]
    
testsFlexible
  = -- test sharing of polymorphic types
    [("let ids = single id in (map auto ids, append (single inc) ids)", ok "([forall a. a -> a],[Int -> Int])")
    ,("single id",ok "forall (a >= forall b. b -> b). [a]")
    ,("choose id",ok "forall (a >= forall b. b -> b). a -> a")
    ,("choose id inc", ok "Int -> Int")
    ,("choose id auto", ok "(forall a. a -> a) -> (forall a. a -> a)")
    ,("\\x y -> x", ok "forall a. forall (b >= forall c. c -> a). a -> b")
    ]

testsRigid
  = [-- Experimental: the "rigid" keyword prevents instantiation or generalization of the principal type of an expression
     -- this is perhaps more convenient than writing an annotation (but not more expressive)
     ("single (rigid id)", ok "[forall a. a -> a]")  
    ,("let pauto (f :: forall a. a -> a) = rigid f in map pauto ids", ok "[forall a. a -> a]")
    ,("let pauto (f :: forall a. a -> a) = rigid f in map pauto (map pauto ids)", ok "[forall a. a -> a]")
    ,("\\x -> rigid (\\y -> x)", ok "forall a. a -> (forall b. b -> a)")
    ,("\\x -> rigid (\\y -> const x y)", ok "forall a. a -> (forall b. b -> a)")
    ,("let c x = rigid (\\y -> x) in \\x y -> c x y", ok "forall a b. a -> b -> a")
    ,("choose plus (\\x -> id)", ok "Int -> Int -> Int")
    ,("choose plus (\\x -> rigid id)", Wrong)      
    ,("choose inc (rigid id)", Wrong)  
    ,("choose id", ok "forall a. (a -> a) -> (a -> a)")
    ,("choose (rigid id)", ok "(forall a. a -> a) -> (forall a. a -> a)")
    ,("revapp (rigid id) auto", ok "forall a. a -> a")
    -- manipulate instantiation of each quantifier:
    ,("[const]", ok "forall a b. [a -> b -> a]")
    ,("[rigid const]", ok "[forall a b. a -> b -> a]")    
    ,("[const :: some a. forall b. a -> b -> a]", ok "forall a. [forall b. a -> b -> a]")
    ,("[const :: some b. forall a. a -> b -> a]", ok "forall b. [forall a. a -> b -> a]")
    ]

-- Type propagation tests
testsProp
  = [ -- test type propagation  (SupportPropagation `elem` features)
     ("(\\f -> f f) :: (forall a. a -> a) -> (forall a. a -> a)", ok "(forall a. a -> a) -> (forall a. a -> a)")
    ,("(let x = 1 in (\\f -> (f x, f True))) :: (forall a. a -> a) -> (Int,Bool)", ok "(forall a. a -> a) -> (Int,Bool)")
    ]
    ++
    [-- test type propagation through applications (SupportAppPropagation `elem` features)
     ("single id :: [forall a. a -> a]", ok "[forall a. a -> a]")
    ,("returnST 1 :: forall s. ST s Int", ok "forall s. ST s Int")
    ,("auto id :: Int -> Int", ok "Int -> Int")
    ,("head ids 1 :: Int", ok "Int")
    ,("head ids :: Int -> Int", ok "Int -> Int")
    ]

testsPropArg
  = [-- test type propagation to arguments (SupportPropagateToArg `elem` features)
     ("takeAuto (\\f -> f f)", ok "forall a. a -> a")
    ,("[id]: [ids]", ok "[[forall a. a -> a]]")
    ,("([id] :: [forall a. a -> a]) : [[\\x -> x]]", ok "[[forall a. a -> a]]")
    ,("apply takeAuto (\\f -> f f)", ok "forall a. a -> a")
    ,("revapp (\\f -> f f) takeAuto", ok "forall a. a -> a")
    ,("apply (\\f -> choose auto f) (auto :: (forall a. a -> a) -> (forall a. a -> a))", ok "(forall a. a -> a) -> (forall a. a -> a)")
    ,("revapp (auto :: (forall a. a -> a) -> (forall a. a -> a)) (\\f -> choose auto f)", ok "(forall a. a -> a) -> (forall a. a -> a)")
    ]

-- this is *not* supported by HML: inference of polymorphic types for arguments that are just passed around..
testsEtaPoly
  = -- in MLF arguments can have an inferred polymorphic type as long as it is not used (or revealed explicitly)
    [("\\x -> auto x", ok "forall a. (forall a. a -> a) -> a -> a")
    ,("\\x -> (auto x, x 1)", Wrong)
    ,("\\x -> (auto x, (x :: forall a. a -> a) 1)", ok "forall a. (forall a. a -> a) -> (a -> a, Int)")
    ,("\\x -> (auto x, (x :: Int -> Int) 1)", Wrong)
    ]

--------------------------------------------------------------------------
-- Test framework
--------------------------------------------------------------------------
type Test = (String,TestResult)
data TestResult  = Ok Type
                 | Wrong

ok :: String -> TestResult
ok stringType 
  = Ok (readType stringType)


test :: [Test] -> IO ()
test ts
  = do xs <- mapM test1 ts
       putStrLn ("\ntested: " ++ show (length ts))
       putStrLn ("failed: " ++ show (sum xs) ++ "\n")

test1 :: Test -> IO Int
test1 (input,Ok resultTp)
  = do tp <- inference input
       if (show tp == show resultTp) 
        then testOk ""
        else testFailed (": test was expected to have type: " ++ show resultTp)
    `Exn.catch` \err ->
      do putStrLn (show err)
         testFailed (": test should be accepted with type: " ++ show resultTp)
       
test1 (input, Wrong)
  = do inference input
       testFailed ": a type error was expected"
    `Exn.catch` \err ->
      do putStrLn (show err)
         testOk " (the input was justly rejected)"

testFailed msg
  = do putStrLn (header ++ "\ntest failed" ++ msg ++ "\n" ++ header ++ "\n")
       return 1
  where
    header = replicate 40 '*'

testOk msg
  = do putStrLn ("ok " ++ msg)
       putStrLn ""
       return 0

*)

#endif