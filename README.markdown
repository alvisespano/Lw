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

Lw is a general purpose, statically typed, strict, functional-first programming language that supports advanced constructs and forms of polymorphism for writing robust, extremely reusable, maintenable and succinct code in a lightweight fashion.

It integrates the state-of-the-art of advancements in the programming language field together with a few novel bits invented by myself throughout more than 15 years of study, research and work. Among the most advanced features, Lw supports open-world context-dependent overloading, constrained polymorphism, implicit parameters, fully-inferred GADTs with overloadable data constructors, first-class modules and polymorphism, row types with overloadable labels, higher-order polymorphism with kind inference and much more.

But what makes Lw unique is the way these features are related together, giving birth to a novel way of writing and reusing code: type constraints resolution is central to many mechanisms, from overloading resolution to implicit parameter application, and it leads to a form of static dispatching, automatic, semi-automatic or manual, that permeates deep within many aspects of the language.
Lw originated from ML and has been influenced by OCaml, Haskell and F#.


#### &lambda;&omega; = Lw = Lightweight

Lw full name is Lightweight, which stands for one of its core principles: almost every feature has little to no impact on code verbosity and size, while of course retaining robustness and safeness intact. Almost everything is statically inferred, from record types to data constructor types, to overloaded symbols principal types.

The `L' and `w` letters also stand for greek &lambda; and &omega;, resembling its theoretical heritage: &lambda;-calculus and *System-F&omega;*.

#### Comparisons with the **big** languanges

#### Lw vs. Haskell

How does Lw compare to the biggest languages out there?

#### Highlights

#### Brief History of the Project


## Examples


