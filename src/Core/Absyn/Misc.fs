(*
 * Lw
 * Absyn/Defs.fs: definitions for AST
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Absyn.Misc

open System
open System.Collections.Generic
open FSharp.Common
open FSharp.Common.Log
open FSharp.Common.Parsing
open Lw.Core.Globals
open Lw.Core


// misc stuff
//

let parse_float s = Double.Parse (s, Globalization.NumberStyles.Float, Globalization.CultureInfo.InvariantCulture)
let fresh_reserved_id () = Config.reserved_id <| sprintf Config.Printing.fresh_reserved_id (fresh_int ())
let tuple_index_label = sprintf Config.Printing.row_based_tuple_label_fmt

type id = string

let (|SymString|_|) =
    let rex = new System.Text.RegularExpressions.Regex("([a-zA-Z_][a-zA-Z0-9_]*)|(__\\$[0-9]+)")
    in function
    | x when not (rex.IsMatch x) -> Some x
    | _ -> None

let (|Sym|_|) (|Id|_|) = function
    | Id (SymString _, r) -> Some r
    | _ -> None


// nodes, params and located stuff
//

type 'a translated = Translated of 'a
with
    override this.ToString () = match this with Translated x -> x.ToString ()

type [< NoEquality; NoComparison >] node<'a, 't> (value : 'a, ?loc : location) =
    let mutable _typed : 't option = None
    let mutable _translated : 'a translated option = None

    member this.translated
        with get () = either (Translated this.value) _translated
        and set x = _translated <- Some x
    
    member this.typed
        with get () = match _typed with Some x -> x | None -> unexpected "node %O has not been typed" __SOURCE_FILE__ __LINE__ this
        and set t = _typed <- Some t

    member val value = value with get //, set
    member val loc = defaultArg loc (new location ())
    abstract pretty : string
    default this.pretty = sprintf "%O" this.value
    override this.ToString () = this.pretty
    static member op_Implicit (this : node<'a, 't>) = this.value


let Lo loc (x : 'a) = new node<_, _> (x, loc)
let ULo x = new node<_, _> (x)
let (|Lo|) (l : node<'a, _>) = l.value, l.loc
let (|ULo|) = function Lo (x, _) -> x


type annotable =
    abstract annot_sep : string

type param<'id, 'n>  = 'id * 'n option

type 'n id_param = param<id, 'n>

let pretty_param sep (id, tyo) =
    match tyo with
        | None   -> sprintf "%O" id
        | Some a -> sprintf "(%O %s %O)" id sep a
