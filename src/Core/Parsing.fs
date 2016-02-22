(*
 * Lw
 * Parsing.fs: parsing facilities
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Parsing

open System
open FSharp.Common.Prelude
open FSharp.Common.Log
open FSharp.Common.Parsing
open Lw.Core.Globals

let load_and_parse_program filename =
    use fstr = new IO.FileStream (filename, IO.FileMode.Open)
    use rd = new IO.StreamReader (fstr)
    L.msg Normal "parsing source file '%s'..." filename
    parse_from_TextReader rd filename Parser.program Lexer.tokenize Parser.tokenTagToTokenId

let parse_line rd name =
    parse_from_TextReader rd name Parser.interactive_line Lexer.tokenize Parser.tokenTagToTokenId

let parse_from_string what p s = parse_from_string s what p Lexer.tokenize Parser.tokenTagToTokenId
let parse_decl = parse_from_string "DECL" Parser.top_decl
let parse_ty_expr = parse_from_string "TYPE-EXPR" Parser.ty_expr
let parse_expr = parse_from_string "EXPR" Parser.expr
