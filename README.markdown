# Lw

Lw is a general-purpose statically-typed functional language with advanced features.
It is currently in development and some of its features are yet to come or still unstable, nonetheless it has reached a stage at which people who enjoy experimenting with new programming languages may start to play with it.

I will update this README file in the near future and document the most interesting among its constructs and features. Consider, however, that any feature may change in the future or may get broken at some point until a stable version is released ;)

## Installation

Lw and the Lw Interpreter are written in F#, therefore you probably want to import the solution into Visual Studio in order to compile it and play with its interactive console.
Assuming you are using at least VS2013 - though VS2015 Community edition is the one I'm developing with at the moment - you should encounter no troubles in making NuGet package manager automatically download dependencies and get the solution compile.

#### VS Solution and Dependencies

Lw.sln consists of 3 projects:

* Core. The core of the language: lexer, parser and type checker plus all that is related to them. This is a library project and cannot be run.
* Interpreter: the real Lw interpreter. This is a startup*-able* project generating an executable.
* FSharp.Common: this is another library project which both Core and Interpreter projects rely on. It is distributed separately as a stand-alone GitHub project of mine.

#### Usage

The Lw interpreter can be used in a few ways:

1. passing a source file name as argument to the executable: this makes the interpreter evaluate the whole program and return an interger exit code.
2. launching the executable with the `--interactive` command line argument: this runs the interpreter in interactive mode, pretty much like other functional languages interactive console. You can write declarations and expressions and see the type inferred as well as the result of the evaluation.
3. mixing the two ways above: this makes the interpreter evaluate the source input file and eventually open the interactive console with an environment populated with all the stuff defined at top level in the input file.
 
(2) from VS: activate the Interactive solution configuration on the left of the *play* button and
as an interactive console.


## Overview

Lw is a general purpose, statically typed, strict, functional-first programming language that supports advanced features and forms of polymorphism for writing robust, extremely reusable, maintenable and succinct code in a lightweight fashion.

It integrates state-of-the-art advancements in the programming language field together with a number of novel bits invented or reinterpreted by myself throughout more than 15 years of study, research and work. Among the most advanced features, Lw supports open-world context-dependent overloading, constrained polymorphism, implicit parameters, fully-inferred GADTs with overloadable data constructors, first-class polymorphism and modules, row types with overloadable labels, higher-order polymorphism with kind inference and much more.

But what makes Lw unique is the way these features are related together, giving birth to a pretty novel way of writing and reusing code: type constraints resolution is central to many language mechanisms, leading to a form of static dispatching which can either be automatic or controlled by the user in case of ambiguities. On the other hand, row-typed records offer a form of dynamic dispatching - and here is the magic: users can switch type constraints into records and viceversa, making type constraints become first-class row types and values and the other way round. This makes two worlds communicate: the world of static dispatching and the world of dynamic dispatching, maximizing code reuse.


#### &lambda;&omega; = Lw = Lightweight

Lw full name is Lightweight, which stands for one of its core principles: almost every feature has little to no impact on code verbosity and size, while of course retaining robustness and safeness intact. Almost everything is statically inferred, from record types to data constructor types, to overloaded symbols principal types.

The `L` and `w` letters also stand for greek &lambda; and &omega;, resembling its theoretical heritage: &lambda;-calculus and System-*F*&omega;.


### Comparisons with the **big** languanges

Lw originated from ML and has been influenced by the big languages out there, such as OCaml, Haskell and F#. Its core language constructs are the typical ones you would expect from a modern functional language: let bindings, lambda abstractions, application, currying, pattern matching are all there and work as you would expect. Ideally, a programmer may simply write Lw code that resembles well-known functional code without ever caring about additional features - this makes learning Lw very easy for those already familiar with ML-like languages.

#### Lw vs. OCaml

OCaml is a great language and Lw has learned a number of lessons from it.
All the basic ML subset of constructs are equivalent when not equal, and even some syntactic choices are the same - e.g. the `function` keyword standing for the lambda abstraction with pattern matching.
Lw does not have a module system though, nor an object system. Lw has a very powerful form of row-typed records, though, and that resembles the way object types work in OCaml.
Moreover, Lw has heavyweight GADTs as well as lightweight polymorphic variants, as late OCaml revisions do - but in Lw everything is more tied together and does not feel like a language extension.
Overloading is another story though: OCaml does not support any form of overloading and it does not support the form of constrained polymorphism that Lw offers as central mechanism. This is a major difference.

#### Lw vs. F#

F# is a great language too. That's the language Lw is currently implemented in. And most core features of F# are the same of OCaml, therefore the same of Lw. Moveover, Lw supports computation expressions and monads as F# does, although F# uses builder classes and objects for defining custom semantics of *banged* constructs, while Lw uses an elegant system based on overloading for that purpose. Active patterns are another F# feature that Lw inherited, even though in a slightly cleaner way.

#### Lw vs. Haskell

Haskell is arguably the most sophisticate language out there - a comparison with the *king* is necessary, albeit a little scary ;) But it's exactly here that Lw can stretch its muscles: Haskell type classes are the feature that mostly resembles Lw type constraints and overloading. With a difference: Lw is more granular and lightweight, since there's no need to define heavyweight hierarchies of type classes; and also Lw allows for easy switching between the static world of type constraints and the dynamic world of records, which is something not even Haskell does. Not to mention that Lw allows overloading and static resolution even of GADT data constructors.
Moreover, Lw is strict and non purely functional: this means that writing mixed functional and imperative code is much easier in Lw. Basically with Lw you can have the same or even more power of the Haskell, with less heavyweight mechanisms.


## A tour of Lw highlights

Let's start from the basic constructs that every child of ML has.
The core of the language is exactly as you would expect, so we won't spend too much time introducing it.

```ocaml
let f x = x
```

defines the polymorphic identity function `f : forall 'a. 'a -> 'a`. And of course that's a syntactic sugar for:

```ocaml
let f = fun x -> x
```

where lambdas expressions are actually first-class citizens.
As usual, function application does not need parentheses, as in `f 23` or `f true` and obviously enables currying as in:

```ocaml
let g x y = (y, x)
in
    g 11
```

which computes a partially-applied functional value that is *missing* the last argument.
Recursion works as usual, as well as conditional expressions:

```ocaml
let rec fib n =
    if n < 2 then 1
    else fib (n - 1) (n -2)
```

where the type inferred is `fib : int -> int`. And basic pattern matching over common data feels familiar:

```ocaml
let rec map f = function
  | []      -> []
  | x :: xs -> f x :: map f xs
```

That's the typical definition of `map : forall 'a :: *, 'b :: *. ('a -> 'b) -> list 'a -> list 'b` where kinds of type variable are annotated when universally quantified.

#### A few notes on the syntax

One tiny detail showed up in the last example: **type applications are right-handed**, unlike ML notation. In Lw type applications look like ordinary applications in the expression language, which makes sense for advanced features: value-to-type promotions are more consistent, for example, and writing complex type manipulation functions more straightforward.

Another bit that makes life easier in Lw - compared to many MLs - is the sugar for multiple let-bindings and the `in` keyword. While the plain syntax is as usual `let patt = expr1 in expr2` (remember that a variable identifier is actually a special case of pattern), **multiple `let`s do not need an `in` each, but only the last one does**.
This allows for the following coding style:

```ocaml
let x = 3
let rec R n = if n < 0 then 0 else g n + 1
and g n = R (n - 1)
let swap x y = y, x
in
    swap x (R 3)
```
    
Each let-binding or series of mutally-recursive let-rec-bbindings can omit its own `in` except the last one.
This is different, for example, from F# indentantion-aware lightweight syntax: lexing and parsing in Lw discards whitespaces and end-of-line, totally ignoring indentation.

Mind that variable identifiers can both be lower-case and upper-case; heavyweight data constructors (see GADTs section) must be capitalized though.


#### Row types and Records

Consider the following function:

```ocaml
let f r = if r.guard then r.x else r.y
```

What type would you expect from f? Well, some might even say that no type should be inferred since the record label `guard` and `a` are undefined. In Lw the function parameter `r` does have a type indeed: the type of a record consisting in:
1. a label `guard` of type bool;
2. labels `x` and `y` of the same polymorphic type `'a`, coming from the unification of the `then` and `else` branches;
3. some missing unknown part `'c` that stands for *the rest of the record*.

```ocaml
f : forall 'a :: *, 'c :: row. { guard : bool; a : 'a; b : 'a | 'c } -> 'a
```

This rest of the record thing is called a *row* and is reprensented by a type variable `'c` whose kind is not `*` (star is the kind of types that may have values). Look at the kinds inferred for the type variables universally quantified by the `forall`: `'a` has kind star because clearly record labels contain values; `'c` has a different kind though, because
Why this apparent complicated row thing involing special kinds and stuff? Because row types are a fantastic way for having a form of structural subtying over records without really introducing subtypes, but only by representing the *unknown tail of a record* via parametric polymorphism. Unification rules do all the magic and make programmning with records very lightweight, easy and concise.


#### Overloading and type constraints resolution

This is the main dish. Consider the following:

```ocaml
overload plus : 'a -> 'a -> 'a
```

This declaration can either appear at top level or be let-bound within a nested scope and introduces a principal type for an overloadable symbol. Later on, symbol `plus` can be mentioned as an ordinary variable and won't be unbound:

```ocaml
let twice x = plus x x
```

The type inferred will be `twice : forall 'a :: *. { plus : 'a -> 'a -> a } => 'a -> 'a`, where the actual type of function `twice` is at the right hand of the implication arrow `=>`, and what lies on the left is a type constraint. The overall type scheme means *assuming a symbol plus of type `'a -> 'a -> a` exists in the environment, the type of `twice` is `'a -> 'a` for any type `'a`*. That's actually an implication asserting the need for a given symbol in order to make a type effective.

## to be continued..


