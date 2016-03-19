(*
 * Lw
 * Parsing.fs: parsing facilities
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Parsing

open System
open FSharp.Common.Log
open FSharp.Common.Parsing
open Lw.Core.Globals
open Microsoft.FSharp.Text

let private __syntax_error (msg, lexbuf : Lexing.LexBuffer<char>) = new syntax_error (msg, lexbuf)
let parse_from_TextReader args = parse_from_TextReader __syntax_error args

let load_and_parse_program filename =
    use fstr = new IO.FileStream (filename, IO.FileMode.Open)
    use rd = new IO.StreamReader (fstr)
    L.msg Normal "parsing source file '%s'..." filename
    parse_from_TextReader rd filename (1, 1) Parser.program Lexer.tokenize Parser.tokenTagToTokenId

let parse_line rd name =
    parse_from_TextReader rd name (0, 0) Parser.interactive_line Lexer.tokenize Parser.tokenTagToTokenId

let parse_from_string what p s = parse_from_string __syntax_error s what (0, 0) p Lexer.tokenize Parser.tokenTagToTokenId
let parse_decl = parse_from_string "DECL" Parser.top_decl 
let parse_ty_expr = parse_from_string "TY-EXPR" Parser.ty_expr
let parse_fxty_expr = parse_from_string "FXTY-EXPR" Parser.fxty_expr
let parse_expr = parse_from_string "EXPR" Parser.expr
