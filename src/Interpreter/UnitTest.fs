(*
 * Lw
 * Test.fs: test modules
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.UnitTest

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

type [< NoComparison; NoEquality >] test_result =
    | Ok of string option
    | Wrong of Type

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

    member this.parse_and_Wk_and_eval_ty_expr s =
        let τ =
            try parse_ty_expr s
            with :? syntax_error as e -> unexpected "syntax error while parsing type expression: %s\n%O" __SOURCE_FILE__ __LINE__ s e
        in
            this.Wk_and_eval_ty_expr_fx τ


[< RequireQualifiedAccess >]
type [< NoEquality; NoComparison >] parsed =
    | Expr of expr
    | Decl of decl
with
    override this.ToString () = this.pretty
    member this.pretty =
        match this with
        | Expr e -> sprintf "expr[%s]" e.pretty
        | Decl d -> sprintf "decl[%s]" d.pretty

let parse_expr_or_decl s =  // TODO: support parsing of type expressions and kinds as well, so everything can be tested
    try parsed.Expr (parse_expr s)
    with :? syntax_error ->
        try parsed.Decl (parse_decl s)
        with :? syntax_error as e -> unexpected "syntax error while parsing expression or declaration: %s\n%O" __SOURCE_FILE__ __LINE__ s e
        

let test_ok msg =
    L.test Low "[OK] %s" msg
    0

let test_failed msg =
    L.fatal_error "[FAIL] %s" msg
    1

let is_test_ok (t : fxty) (et, ek) = et = t && ek = t.kind

let decl_dummy_ty = Fx_F_Ty T_Unit

let handle_exn e = ignore <| Interactive.handle_exn e

let test1 (tc : typechecker) (input, res) =
    let typecheck1 s =
        match parse_expr_or_decl s with
        | parsed.Expr e as p ->
            let ϕ = tc.W_expr e
            L.test Low "%O : %O" e ϕ
            ϕ

        | parsed.Decl d ->
            tc.W_decl d
            decl_dummy_ty
    in
        match res with
        | Ok so ->
            let t, k =
                match so with
                | Some s -> try tc.parse_and_Wk_and_eval_ty_expr s
                            with e ->
                                L.unexpected_error "expected type expression \"%O\" is invalid due to an exception:" s
                                handle_exn e
                                unexpected "%s" __SOURCE_FILE__ __LINE__ s (pretty_exn_and_inners e)
                | None   -> let t = decl_dummy_ty in t, t.kind
            in
                try
                    let ϕ = typecheck1 input
                    if is_test_ok ϕ (t, k) then test_ok "ok"
                    else test_failed <| sprintf "test was expected to have type '%O' but got '%O'" t ϕ
                with :? static_error as e ->
                    let r = test_failed <| sprintf "test should be accepted with type %O but a %s occurred:" t e.header
                    handle_exn e
                    r

        | Wrong T ->
            assert T.IsSubclassOf typeof<static_error>
            try
               let _ = typecheck1 input
               test_failed <| sprintf "a %s was expected from testing input: %s" T.Name input
            with :? static_error as e ->
                if e.GetType().IsSubclassOf T then
                    L.test Min "%s" (pretty_exn_and_inners e)
                    let r = test_ok <| sprintf "input \"%s\" was justly rejected" input
                    L.test Min "static error was: %s" (pretty_exn_and_inners e)
                    r
                else reraise ()

let test ts =
    let tc = new typechecker ()
    let xs, span = cputime (List.map (test1 tc)) ts
    let sum = List.sum xs
    L.test High "tested: %d\nfailed: %d\ncpu time: %s" (List.length ts) sum span.pretty
    sum


module Tests =

    let ok s = Ok (Some s)
    let any = Ok None
    let wrong< 'exn when 'exn :> static_error > = Wrong typeof<'exn>
    let wrong_type = wrong<type_error>
    let wrong_syntax = wrong<syntax_error>
    
    let intrinsics =
      [
        "[]",                                       ok "list 'a"
        "[1; 2]",                                   ok "list int"
        "true :: false :: true",                    ok "list bool"
        "[true; 2]",                                wrong_type
        "(Some 0 :: None) :: [Some 2]",             ok "list (list (option int))"   // TODO: support pipelining operators "|>" and "<|" in expressions AS WELL AS in type expressions
        "[None]",                                   ok "list (option 'a)"
      ]

    let HM =
      [
        "fun x -> x",                               ok "forall 'a. 'a -> 'a"
        "fun f x -> f x",                           ok "forall 'a 'b. ('a -> 'b) -> 'a -> 'b"
        "fun a, b -> a",                            wrong_syntax
        "inc true",                                 wrong_type
        "let i = fun x -> x in i i",                ok "forall 'a. 'a -> 'a"
        "fun i -> i i",                             wrong_type // infinite type
        "fun i -> (i 1, i true)",                   wrong_type // polymorphic use of parameter
//        "single id",                                ok "forall ('a :> forall 'b. 'b -> 'b). list 'a"
//        "choose (fun x y -> x) (fun x y -> y)",     ok "forall 'a. 'a -> 'a -> 'a"
//        "choose id",                                ok "forall ('a :> forall 'b. 'b -> 'b). 'a -> 'a"
      ]
    
    let all = List.concat [ intrinsics; HM ]

    
let main () =
    test Tests.all




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

