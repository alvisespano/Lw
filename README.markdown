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
* Interpreter: the real Lw interpreter. This is an *startup-able* project generating an executable.
* FSharp.Common: this is another library project which both Core and Interpreter projects rely on. It is distributed separately as a stand-alone GitHub project of mine.

#### Usage

The Lw interpreter can be used in a few ways:

1. passing a source file name as argument to the executable: this makes the interpreter evaluate the whole program and return an interger exit code.
2. launching the executable with the `--interactive` command line argument: this runs the interpreter in interactive mode, pretty much like other functional languages interactive console. You can write declarations and expressions and see the type inferred as well as the result of the evaluation.
3. mixing the two ways above: this makes the interpreter evaluate the source input file and eventually open the interactive console with an environment populated with all the stuff defined at top level in the input file.
 
(2) from VS: activate the Interactive solution configuration on the left of the *play* button and
as an interactive console.

## Overview

#### &lambda;&omega; = Lw = Lightweight

#### Highlights

#### Brief History of the Project


## Examples


