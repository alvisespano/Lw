# Lw

This document will be kept updated as development goes on.
Keep in mind that features may change anytime, since Lw is a work in progress.


## Introduction

Lw is a general purpose, statically typed, strict, impure, functional-first programming language that supports cutting-edge features and advanced forms of polymorphism for writing robust, reusable and succinct code.

Ideal for writing big as well as small programs, as most heavyweight declarative language features has a lightweight inferred counterpart as well, it integrates state-of-the-art advancements in the programming language field together with a number of novel bits invented or reinterpreted by me throughout more than 15 years of research, passion and work.

Among the highlights: type and kind inference, System-F types and first-class polymorphism, open-world overloading with automatic context-dependant resolution, implicit function parameters, union types supporting fully-inferred Generalized Algebraic Datatypes, row types for polymorphic variants and records, overloading of data constructors and record labels, powerful kind system supporting higher-order polymorphism, kind polymorphism, value-to-type & type-to-kind promotion and demotion, first-class modules and much more.

But what makes Lw unique is the way these features are tied together, unleashing some novel ways of writing and reusing code. For example, type constraints resolution is central to most language mechanisms in Lw, leading to a form of static dispatching that can either be automatic or assisted by the programmer; dually, row-type records are subject to dynamic dispatching and enables structural subtyping - a.k.a. fully inferred and sound duck typing. And here lies the magic: users can turn type constraints into records and viceversa anytime by using a special operator, converting non-first-class static type constraints into a first-class record type and the other way round. This makes two worlds communicate: the world of static resolution and the world of dynamic resolution. Languages typically do not define a clear symmetry in this respect, and anyway a lot of boilterplate code is often required for switching between the two worlds - when possible at all. In Lw this symmetry is crucial and explitly designed, encouraging code reuse.


#### &lambda;&omega; = Lw = Lightweight

The language full name is Lightweight, which stands for one of its core principles: almost every feature has little to no impact on code verbosity and size, while retaining robustness and safeness intact. By default everything is statically inferred, automatic or implicit and most features do not require declarations of any sort - hence the name Lightweight. Nonetheless, the so-called declarative approach is an option as well: users can define heavyweight types and enforce a stronger typing discipline when needed or desired.

The `L` and `w` letters also stand for greek &lambda; and &omega;, tributing the theoretical heritage behind Lw: &lambda;-calculus and System-*F*&omega;.


### Comparisons with the **big** languanges

Lw originated from ML and has been influenced by the big languages out there, such as OCaml, Haskell and F#. Its core language constructs are the typical ones you would expect from a modern functional language: let bindings, lambda abstractions, application, currying, pattern matching are all there and work as you would expect. Ideally, a programmer may simply write Lw code that resembles well-known functional code without ever caring about additional features - this makes learning Lw very easy for those already familiar with ML-like languages.

#### Lw vs. OCaml

OCaml is a great language and Lw has learned a number of lessons from it.
All the basic ML constructs are equivalent when not equal, and even some syntactic choices are the same - e.g. the `function` keyword standing for the lambda abstraction with pattern matching.
Lw does not have a module system though, nor an object system. Lw has a very powerful form of row-typed records, though, and that resembles the way object types work in OCaml.
Moreover, Lw has heavyweight GADTs as well as lightweight polymorphic variants, as late OCaml revisions do - but in Lw everything is more tied together and does not feel like a language extension.
Overloading is another story though: OCaml does not support any form of overloading and it does not support the form of constrained polymorphism that Lw offers as central mechanism. This is a major difference.

#### Lw vs. F# #

F# is a great language too. That's the language Lw is currently implemented in, by the way. And most core features of F# are the same of OCaml, therefore the same of Lw. Moveover, Lw supports computation expressions and monads as F# does, although F# uses builder classes and objects for defining custom semantics of *banged* constructs, while Lw uses an system based on constraints and overloading for that purpose. Active patterns are another F# feature that Lw inherited, even though in a slightly more consistent way: in F# active patterns are functions returning `option` while data constructors aren't; in Lw every data constructors, whether a GADT or a polymorphic variant, can be either used as a function returning `option`, rendering them equivalent to active patterns.

#### Lw vs. Haskell

Haskell is arguably the most sophisticate language out there - a comparison with the *king* is therefore necessary. And it's exactly here that Lw can stretch its muscles: Haskell type classes are the feature that best resembles Lw type constraints and overloading. With a difference though: overloading in Lw is more granular, more widespread and less declarative, as there's no need to define top level hierarchies of type classes. Moreover, Lw offers a unique feature: you can easily switch between the static world of type constraints and the dynamic world of records, which is something not even Haskell does. Finally, Lw is strict and impure while Haskell is lazy and pure: this means that writing mixed functional and imperative code is much easier in Lw and you don't need to write complex monadic functors every time you have to print a string. Basically with Lw you can have the same or even more power of Haskell, but lighter mechanisms and strict semantics.


## A tour of Lw

Let's start from the basic constructs that every child of ML usually offers.
The core of the language is exactly as you would expect, thus we won't spend much time showing it off.

```ocaml
let f x = x
```

defines the polymorphic identity function `f : forall 'a. 'a -> 'a`. And of course that's a syntactic sugar for:

```ocaml
let f = fun x -> x
```

where lambdas expressions are obviously first-class citizens.
As usual, function application does not need parentheses, as in `f 23` or `f true`, and obviously enables currying as in:

```ocaml
let g x y = (y, x)
in
    g 11
```

which computes a partially-applied functional value of type `forall 'a. 'a -> int * 'a` that is *missing the second argument*.
Recursion works as usual, as well as conditional expressions:

```ocaml
let rec fib n =
    if n < 2 then 1
    else fib (n - 1) (n -2)
```

where the type inferred is `fib : int -> int`.
And basic pattern matching over disjoint union data types feels familiar as well:

```ocaml
let rec map f = function
  | []      -> []
  | x :: xs -> f x :: map f xs
```

That's the typical definition of `map : forall 'a 'b. ('a -> 'b) -> list 'a -> list 'b` you would write in say OCaml or F#. Just note that in Lw you can tell the interpreter (or the compiler) to pretty print kinds of type variable when universally quantified; by default it does, but there are few other behaviours you may enable in the command line - e.g. hide the universal quantifier and consider ticked type variables as universally quantified unless prefixed by an underscore (like in `'_a` as other MLs do), or annotate kinds only when different from star, or at the first left-to-right occurence.

There will be further detailed sections for new data type definitions, advanced constructs and Lw-specific features.


#### A few notes on the syntax

As already said, Lw shares most of ML's look & feel. With a few notable differences though.

###### Right-handed type applications and ticked type variables

One tiny detail has shown up in the last example: **type variables are ticked**, like typical ML notation, but **type applications are right-handed** instead. In Lw type applications look like ordinary applications in the expression language, which makes sense for advanced features: value-to-type promotions are more consistent, for example, and writing complex type manipulation functions more straightforward.

###### Multiple `let`'s with a single `in`

Another bit that can make life easier in Lw is the sugar for multiple let-bindings with a single final `in` keyword before the body. While the general syntax for `let` is the usual `let patt = expr1 in expr2` (don't forget a variable identifier is actually a special case of pattern), **multiple `let`'s do not need an `in` each, but only the last one does**.
This basically means that `let x = 1 let y = 2 in x, y` is not parsed as an application where the right `let` is the argument and `1` is the applicand as in `let x = 1 (let y = 2 in x, y)` - therefore you must specifiy parentheses in case you are truly willing to do such weird application, which is something rather situational by the way. Naturally, the sugar is meant to deal with what typically a user desires, i.e. defining multiple `let`'s:

```ocaml
let k = 11
let rec R n = if n < 0 then 0 else g n + 1
and g n = R (n - 1)
let k = 23
and swap x y = y, x + k  // the k here is the k bound few lines above, not the one bound just up here
in
    swap x (R 3)
```
    
Each let-binding or series of mutally-recursive let-rec-bindings can omit its own `in` except the last one.
This is different, for example, from F# indentantion-aware lightweight syntax: lexing and parsing in Lw discards whitespaces and end-of-line, totally ignoring indentation.

Beware though: do not confuse multiple `let`'s without the `in` with the `let..and..in` construct. These are two distinct things.
Mulitple let-bindings separated by an `and` are *bound to the same environment* and are syntactically considered as one sigle declaration, thus requiring one single `in` in theory and in practice. Multiple `let`'s, instead, are supposed to have one `in` each, but Lw supports a *syntactic sugar* that allows for multiple `let`'s to be written without each own's `in` except the last one - and that's as if they were declared in cascade, thus each definion may refer to the symbols bound above.
Pay attention to the example above: `R` and `g` are *`and`-bound*, thus not needing an `in` for each binding anyway; while the first `k` and the `R`-and-`g` couple are distinct let-bindings and are supposed to have their own `in`'s (one for the `k` and one for the couple), but in Lw you can omit them. Scoping rules still applies though, as shown by the last couple `k` and `swap`.

###### Identifiers and naming conventions

Variable identifiers in expressions can be lower-case or upper-case; data constructors must be capitalized though. Also ticked, back-ticked and marked identifiers exist and will be explained in dedicated sections: the same casing rule applies to those as well.

**All identifiers are Snake-case, except data constructors which are Pascal-case** (or *capitalized Camel-case*, if you prefer).
Ideally, local identifiers should be short but public identifiers should be meaningful and reasonably long.
Record labels are considered identifiers, thus are Snake-case, and the same applies to type and kind names.
In the type language ticked snake-cased identifiers are free type variables, possibly universally quantified; not to be confused with type-function parameters or locally let-bound type names which are plain identifiers - as they both are in the expression laguange.

Ticking an identifier in general means *do not consider it as unbound*: this applies both to the type language and the expression language. In the former it refers to generalizable type variables, in the former to constrained free variables (a.k.a. implicit parameters).

###### Unicode, greek letters and special symbols

Lw supports Unicode lexing and pretty printing. Use of **greek letters for type variables** in place of ticked identifiers is supported as well as some other special symbols, such as the reveserd-A symbol instead of the *forall* keyword for universally quantifying polymorphic type variables, or the reversed-E symbol in place of the *exists* keyword for explicitly denoting existential types. Virtually all Unicode symbols are usable as identifiers.
One might for instance define the *is_in* (&0220a) function like this - assuming that some `find : ('a -> bool) -> list 'a` function is defined:

```ocaml
let (&0220a) a b = find (fun x -> x = a) b
```

###### Quick lambdas

In Lw, lambda expressions look like ML ones: the general syntax `fun patt -> expr` is clear and well known.
There exist an alternate syntax though, for writing quick short lambda expressions, which supports either the greek ? or the backslash `\` in place of the keyword `fun` and the dot `.` in place of the arrow `->`, as in:

```ocaml
let dont_touch l = map (?x.x) l
let sum l = fold (\z x. x + z) 0 l
```

Mind that this alternate syntax does not support patterns, like `fun` does, or cases, like `function` does. It is simply a short syntax for plain identifier-based lambda expressions possibly having multiple paramters and a brief body.

#### Row types and records

Consider the following function:

```ocaml
let f r = if r.guard then r.x else r.y
```

What type would you expect from parameter `r`? Well, some might even say that no type should be inferred at all since record labels `guard`, `x` and `y` are undefined. In Lw the function parameter `r` does have a type indeed: the type of a record consisting in:
1. a label `guard` of type bool;
2. labels `x` and `y` of the same polymorphic type `'a`, coming from the unification of the `then` and `else` branches;
3. some missing unknown part `'c` that stands for *the rest of the record*.

```ocaml
f : forall 'a :: *, 'c :: row. { guard : bool; x : 'a; y : 'a | 'c } -> 'a
```

This rest of the record thing is called a *row* and is reprensented by a type variable `'c` whose kind is not `*` (star is the kind of types that may have values). Look at the kinds inferred for the type variables universally quantified by the `forall`: `'a` has kind star because clearly record labels contain values; `'c` has a different kind though, because
Why this apparent complicated row thing involing special kinds and stuff? Because row types are a fantastic way for having a form of structural subtying over records without really introducing subtypes, but only by representing the *unknown tail of a record* via parametric polymorphism. Unification rules do all the magic and make programmning with records very lightweight, easy and concise.


#### Overloading and type constraints 

Overloading and type constraints resolution is one of Lw main courses. The two are faces of the same coin.
Overloading lets you simply set up multiple definitions under the same name: you can declare a name you are willing to overload and specify its *principal type*:

```ocaml
overload plus : 'a -> 'a -> 'a
```

As almost everything in Lw, this declaration can either appear at top level or be let-bound within a nested scope.
It does nothing: it just reprensents the intent of overloading and makes the compiler aware of the most generic type any further overloaded instance of the symbol `plus` will have - which basically means that all overloads of `plus` must have a type that is *more specialized* than `'a -> 'a -> 'a`. For example, imagine that `(+) : int -> int -> int` is the native function for integer addition, then

```ocaml
let over plus x y = x + y
```

would be an instance of `plus` whose type is `int -> int -> int` - basically an alias of `(+)` which could have written even more concisely like `let over plus = (+)`.
We may give also another instance of `plus` for booleans (where `|| : bool -> bool -> bool` is the *or* operator):

```ocaml
let over plus a b = a || b
```

whose type obvisouly is `bool -> bool -> bool`.
That's pretty straightforward and apparently not so interesting. Consider though when a function starts mentioning overloaded symbols:

```ocaml
let twice x = plus x x
```

The type inferred will be `twice : forall 'a :: *. { plus : 'a -> 'a -> a } => 'a -> 'a`, which reads like: *for all type variables `'a` of kind star, symbol `twice` has type `'a -> 'a` assuming a symbol `plus` having type `'a -> 'a -> 'a` exists in the environment*. Basically the actual type of function `twice` is at the right hand of the implication arrow `=>`, and what lies between that and the universal quantifier are type constraints. The important lesson here is: **when type constraints are satisfied, a symbol does have a real type as well as a value**. Such value can either be a function or any other form of value supported by the language, therefore also constants can be overloaded.
You may for instance define a *semigroup*-like scenario by adding:

```ocaml
overload zero : 'a

let rec sum = function
   | []      -> zero
   | x :: xs -> plus x (sum xs)
```
Where the type inferred would be `sum : forall 'a. { plus : 'a -> 'a -> 'a; zero : 'a } => list 'a -> 'a`.

The general rule of thumb is: *use of overloaded symbols puts those symbols into the type constraint set of a type scheme at generalization-time, i.e. when the current let-binding occurs*, **even if overloaded instances are not defined**.
This means that you may provide no `let over`'s for your overloaded symbols and still be able to use them anytime within your code, yielding to the very same type results.
That's real **open-world** overloading: **instances are not taken into account until the very end, i.e. until type constraints resolution occurs.**


##### Automatic resolution

Type constraints resolution may take place in 3 ways: automatically, semi-automatically or manually.
In order to make the compiler resolve automatically, proper instances for the types involved must have been provided; in case they haven't, **constraints will simply be kept - totally or partially - until resolution can successfully take place**. And sooner or later it will.
Consider this example:

```ocaml
overload plus : 'a -> 'a -> 'a

let twice x = plus x x  // plus : forall 'a. { plus : 'a -> 'a -> 'a } => 'a -> 'a

let a = twice 3         // a : { plus : int -> int -> int } => int
                        // constraint is unresolved due to lack of instances for int

let b = a + 7           // b : { plus : int -> int -> int } => int
                        // constraint is still unresolved

let c =                 // c : int = 14
    let over plus = (+) // local instance plus for int
    in
        b + 1           // constraint of b is resolved and finally computes the int value (3 + 3) + 7 = 13
                        // and the whole expression computes a ground value

let over plus = (*)     // weird instance of plus for int with the semantics of multiplication

let d = b + c           // d : int = 30
                        // constraint of b is resolved with the multiplicative plus above, hence b = (3 * 3) + 7 = 16
                        // and c was already the ground value 16 with no constraints
```

Type constraints not only allow for a form of *constrained parametric polymorphism*, but in case no appropriate instance exist they can be **kept even if no type variables occur anymore**, which means they stand for a form of *controlled dynamic scoping*. Look at the definition of `b`: that's clearly an integer, there's no polymorphism anymore there; a function `plus : int -> int -> int` still missing though. Now look at the definition of `c`: it basically says *evaluate the integer `b` with this instance of `plus` i'm defining here*. Later on, another instance `plus` is given at top-level, whose semantics apply from there on, hence the evaluation of `d`.


#### Context-dependent overloading 

As opposed to common imperative languages such as C++, Java and C#, where overloading is closed-world and context-independent, i.e. restricted to the number and type of arguments, in Lw overloading is open-world and **context-dependent**, meaning that even constants having non-arrow types or function co-domains can be overloadeed: there's no restriction to the form of an overloaded symbol principal type and its instances.

```ocaml
overload convert : 'a -> 'b            // a very generic principal type

let over convert n = sprintf "%d" n    // convert : int -> string

let over convert = function            // convert : int -> bool
    | 0 -> false
    | _ -> true  

let f x =                              // f : forall 'a. { convert : 'a -> bool; convert : 'a -> string } => 'a -> string
 if convert x then convert x           // constraints are unsolved even if instances exist
 else "nothing" 

let a = f 3                            // a : string
                                       // the instances above fit just perfectly with int
```

First of all, notice that in the type scheme of `f` there occur 2 distinct `convert` constraints: that's because each single occurrence of an overloaded symbol is collected separately within the constraint set, as it may be solved by means of different instances. Secondly, the resolution of both `convert`'s relies on the co-domain for being solved, hence the context-dependentness.


#### Ambiguities and Assisted Resolution

Context-dependent overloading may lead to ambiguities. And we cannot do much about this - consider the following:

```ocaml
overload parse : string -> 'a
overload pretty : 'a -> string

let parse_and_pretty x = pretty (parse x)
```

The type inferred is `parse_and_pretty : forall 'a. { pretty : 'a -> string; parse : string -> 'a } => string -> string`.
Now, look at the type part: no type variable occurs in `string -> string` even if `'a` is universally quantified; actually, `'a` appears only in the constraints part. This is a situation where further unification of the type part would be useless for resolving the constraints: no matter how you will use `parse_and_pretty` in your code, there's no way the type checker can deduce a type for `'a`. This basically means that **any combination of `pretty` and `parse` candidates would do** - and that's what, technically speaking, is considered **ambiguious**.

```ocaml
let over parse s = sscanf "%d" s    // parse : string -> int
let over pretty n = sprintf "%d" n  // pretty : int -> string

let x = parse_and_pretty "3"        // x : forall 'a. { pretty : 'a -> string; parse : string -> 'a } => string
```

Despite the instances introduces above, the resolution of `x` is still ambiguous. The compiler knows it is a string, but no clue indicates that the two instances involving given for `int` are proper candidates.
A special language construct comes in help here:

```ocaml
let x = parse_and_pretty "3" where { parse : _ -> int }   // x : string
```

By specifying at least some part of the type of one of the constraints, the resolution algorithm can narrow the possible set of candidates: that `int` appearing as co-domain of constrained function `parse` is enough in this case. It basically gives a clue for type variable `'a`, which was responsible for the whole ambiguity issue. The rest is done by unification by the compiler, which decides that instance `parse : string -> int` is the best fit, and eventually `pretty : int -> string` comes automatically.

In other words, **the user should provide a tiny bit of type information in order to help the type checker solving all the rest**. That's a least-impact solution for solving ambiguitites.
Moreover, the general syntax for this *assisted* resolution allows for any type expression to appear after the `where` keyword following an expression: therefore any arbitrarily-complex type computation or alias may come in hand.






