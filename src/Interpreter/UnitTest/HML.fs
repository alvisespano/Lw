
module Lw.Interpreter.UnitTest.HML

open Lw.Interpreter.UnitTester
open Lw.Interpreter.UnitTester.Aux

let hml =
    "HML", [KeepBindingsAtEnd; HideHints; Dependencies [Basic.lists; Basic.hindley_milner]],
    [
    "let i x = x in i 1, i true, i",            typed_ok_as "int * bool * (forall 'a. 'a -> 'a)"
    "fun (i : forall 'a. 'a -> 'a) ->
        (i 1, i true)",                         typed_ok_as "(forall 'a. 'a -> 'a) -> int * bool"
    "single id",                                typed_ok_as "forall ('a :> forall 'b. 'b -> 'b). list 'a"
    "[id]",                                     typed_ok_as "forall ('a :> forall 'b. 'b -> 'b). list 'a"
    "let ids = single id",                      typed_ok_as "forall ('a :> forall 'b. 'b -> 'b). list 'a"
    "let const x y = x",                        typed_ok_as "forall 'a 'b. 'a -> 'b -> 'a"
    "let const2 x y = y",                       typed_ok_as "forall 'a 'b. 'a -> 'b -> 'b"
    "let choose x y = if x = y then x else y",  typed_ok_as "forall 'a. 'a -> 'a -> 'a"
    "choose (fun x y -> x) (fun x y -> y)",     typed_ok_as "forall 'a. 'a -> 'a -> 'a"
    "choose id",                                typed_ok_as "forall ('a :> forall 'b. 'b -> 'b). 'a -> 'a"

    "let ids : list ('a -> 'a) = ids",                      typed_ok_as_ "forall 'a. list ('a -> 'a)" [Unbind]     // autogen takes place for top-level lets
    "let ids : forall 'a. list ('a -> 'a) = ids",           typed_ok_as_ "list ('a -> 'a)" [Unbind]                // this must be equivalent to the one above

    "let id : 'a -> 'a = id in id 1, id true",              wrong_type
    "let id : forall 'a. 'a -> 'a = id in id 1, id true",   typed_ok_as_ "int * bool" [Unbind]
    "let id : 'a -> 'a = id in id",                         typed_ok_as_ "'a -> 'a" [NoAutoGen]

    "let ids : list ('a -> 'a) = ids in ids",               typed_ok_as_ "list ('a -> 'a)" [NoAutoGen]
    "let ids : forall 'a. list ('a -> 'a) = ids in ids",    typed_ok_as "forall 'a. list ('a -> 'a)"
    "let ids : list (forall 'a. 'a -> 'a) = ids in ids",    typed_ok_as "list (forall 'a. 'a -> 'a)"
    "let ids : forall 'a. list ('a -> 'a) = ids in ids",    typed_ok_as "forall 'a. list ('a -> 'a)"
    "let ids : list (forall 'a. 'a -> 'a) = ids in ids",    typed_ok_as "list (forall 'a. 'a -> 'a)"

    "let poly (f : forall 'a. 'a -> 'a) =
        f 1, f true",                           typed_ok_as "(forall 'a. 'a -> 'a) -> int * bool"
        
    "app poly",                                 typed_ok_as "(forall 'a. 'a -> 'a) -> int * bool"
    "app poly id",                              typed_ok_as "int * bool"
    "map id [id]",                              typed_ok_as "forall ('a :> forall 'b. 'b -> 'b). list 'a"

    "map poly ids",                             typed_ok_as "list (int * bool)"
    "append (single inc) ids",                  typed_ok_as "list (int -> int)"
    "map poly ids, append (single inc) ids",    typed_ok_as "list (int * bool) * list (int -> int)"

    "let ids : list (forall 'a. 'a -> 'a) = ids
     in
        map poly ids",                          typed_ok_as "list (int * bool)"

    "let ids : forall 'a. list ('a -> 'a) = ids
     in
        map poly ids",                          wrong_type_ [ShowHint 12]
   
    "let ids : list ('a -> 'a) = ids
     in
        map poly ids",                          wrong_type_ [ShowHint 6]

    "let ids : forall ('a :> forall 'b. 'b -> 'b) . list 'a = ids
     in
        map poly ids",                          typed_ok_as "list (int * bool)"

    "let ids : forall 'a. list ('a -> 'a) = ids
     in
        map poly ids, append (single inc) ids",  wrong_type_ [ShowHint 6]

    ]

let higher_rank = 
    "Impredicative Application and Higher Rank Arguments", [],
    [
    "let auto (id : forall 'a. 'a -> 'a) = id",         typed_ok_as "(forall 'a. 'a -> 'a) -> (forall 'a. 'a -> 'a)"
    "let xauto (id : forall 'a. 'a -> 'a) x = id x",    typed_ok_as "forall 'a. (forall 'b. 'b -> 'b) -> 'a -> 'a"
    "let takeAuto (auto : (forall 'a. 'a -> 'a) ->
        (forall 'a. 'a -> 'a)) = auto auto",            typed_ok_as "((forall 'a. 'a -> 'a) -> (forall 'a. 'a -> 'a)) -> (forall 'a. 'a -> 'a)"

    "xauto",                                    typed_ok_as "forall 'a. (forall 'a. 'a -> 'a) -> 'a -> 'a"
    "takeAuto",                                 typed_ok_as "((forall 'a. 'a -> 'a) -> (forall 'a. 'a -> 'a)) -> (forall 'a. 'a -> 'a)"
    "auto",                                     typed_ok_as "(forall 'a. 'a -> 'a) -> (forall 'a. 'a -> 'a)"
    "fun (i : forall 'a. 'a -> 'a) -> i i",     typed_ok_as "forall ('a :> forall 'b. 'b -> 'b). (forall 'b. 'b -> 'b) -> 'a"
                                                // type_ok "forall 'a. (forall 'a. 'a -> 'a) -> 'a -> 'a"
    "auto id",                                  typed_ok_as "forall 'a. 'a -> 'a"
    "apply auto id",                            typed_ok_as "forall 'a. 'a -> 'a"

    "(single : (forall 'a. 'a -> 'a -> list (forall 'a. 'a -> 'a)) id", typed_ok_as "list (forall 'a. 'a -> 'a)"
        
    "runST (returnST 1)",                       typed_ok_as "int"
    "runST (newRef 1)",                         wrong_type
    "apply runST (returnST 1)",                 typed_ok_as "int"
    "map xauto ids",                            typed_ok_as "forall 'a. list ('a -> 'a)"
    "map xauto (map xauto ids)",                wrong_type
    "map auto ids",                             typed_ok_as "list (forall 'a. 'a -> 'a)"
    "map auto (map auto ids)",                  typed_ok_as "list (forall 'a. 'a -> 'a)"
    "head ids",                                 typed_ok_as "forall 'a. 'a -> 'a"
    "tail ids",                                 typed_ok_as "list (forall 'a. 'a -> 'a)"
    "apply tail ids",                           typed_ok_as "list (forall 'a. 'a -> 'a)"
    "map head (single ids)",                    typed_ok_as "list (forall 'a. 'a -> 'a)"
    "apply (map head) (single ids)",            typed_ok_as "list (forall 'a. 'a -> 'a)"

    (*-- check infinite poly types
    "(undefined :: some a. [a -> a] -> Int) (undefined :: some c. [(forall d. d -> c) -> c])", Wrong)
    "(undefined :: some a. [a -> a] -> Int) (undefined :: [(forall d. d -> d) -> (Int -> Int)])", Wrong)
    "(undefined :: some a. [a -> (forall b. b -> b)] -> Int) (undefined :: some c. [(forall d. d -> d) -> c])", ok "Int")

    -- these fail horribly in ghc: (choose auto id) is rejected while ((choose auto) id) is accepted -- so much for parenthesis :-)
    "choose id auto", ok "(forall a. a -> a) -> (forall a. a -> a)")
    "choose auto id", ok "(forall a. a -> a) -> (forall a. a -> a)")
    "choose xauto xauto", ok "forall a. (forall b. b -> b) -> a -> a")
    "choose id xauto", Wrong)
    "choose xauto id", Wrong)

    -- these fail too in ghc: (choose ids []) is accepted while (choose [] ids) is rejected
    "choose [] ids", ok "[forall a. a -> a]")
    "choose ids []", ok "[forall a. a -> a]")
    
    -- check escaping skolems
    "\\x -> auto x", Wrong)                                                                             -- escape in match
    "let poly (xs :: [forall a. a -> a]) = 1 in (\\x -> poly x)", Wrong)                              -- escape in apply
    "\\x -> (x :: [forall a. a -> a])", Wrong)                                                          -- escape in apply
    "\\x -> let polys (xs :: [forall a . a -> a]) = 1; f y = x in polys [f::some a. forall b. b -> a]",Wrong)  -- escape in unify (with rigid annotations, otherwise we get a skolem mismatch)
    "ids :: forall b. [forall a. a -> b]", Wrong)                                                       -- unify different skolems

    -- co/contra variance
    "let g (x::(forall a. a -> a) -> Int) = x id; f (x :: Int -> Int) = x 1 in g f", Wrong)                                      -- HMF is invariant
    "let g (x::(forall a. a -> a) -> Int) = x id; f (x :: Int -> Int) = x 1 in g (\\(x :: forall a. a -> a) -> f x)", ok "Int")  -- but we can always use explicit annotations to type such examples

    -- shared polymorphism
    "let f (x :: [forall a.a -> a]) = x in let g (x :: [Int -> Int]) = x in let ids = [id] in (f ids, g ids)", ok "([forall a. a -> a],[Int -> Int])")*)
    ]

let all : section list =
    [
    hml
    higher_rank
    ]






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

*)