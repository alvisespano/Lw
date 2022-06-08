(*
 * Lw
 * Absyn/Misc.fs: misc definitions for AST
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

let parse_float (s : string) = Double.Parse (s, Globalization.NumberStyles.Float, Globalization.CultureInfo.InvariantCulture)
let fresh_reserved_id () = Config.reserved_id <| sprintf Config.Printing.fresh_reserved_id (fresh_int ())
let tuple_index_label = sprintf Config.Printing.row_based_tuple_label_fmt

type ident = string

let (|SymString|_|) =
    let rex = new System.Text.RegularExpressions.Regex("([a-zA-Z_][a-zA-Z0-9_]*)|(__\\$[0-9]+)")
    in function
    | x when not (rex.IsMatch x) -> Some x
    | _ -> None

let (|Sym|_|) (|Id|_|) = function
    | Id (SymString _, r) -> Some r
    | _ -> None


// nodes and located stuff
//

type annotation =
    abstract annotation_sep : string

type 'a translated = Translated of 'a
with
    override this.ToString () = match this with Translated x -> x.ToString ()

type [< NoEquality; NoComparison >] node<'a> (value : 'a, ?loc : location) =
    let mutable _typed : obj option = None
    let mutable _translated : 'a translated option = None

    member this.translated
        with get () = either (Translated this.value) _translated
        and set x = _translated <- Some x
    
    member this.typed
        with get () = match _typed with Some x -> x | None -> unexpected "node %O has not been typed" __SOURCE_FILE__ __LINE__ this
        and set t = _typed <- Some t

    member val value = value with get
    member val loc = defaultArg loc (new location ())
    abstract pretty : string
    default this.pretty = sprintf "%O" this.value
    override this.ToString () = this.pretty
//    static member op_Implicit (this : node<'a>) = this.value
//    interface annotation with
//        member this.annotation_sep = this.value.annotation_sep 


let Lo loc (x : 'a) = new node<_> (x, loc)
let ULo x = new node<_> (x)
let (|Lo|) (l : #node<'a>) = l.value, l.loc
let (|ULo|) = function Lo (x, _) -> x


// annotations
//

//type annotation_node<'a when 'a :> annotation> (value : 'a, ?loc : location) =
//    inherit node<'a> (value, ?loc = loc)
//    interface annotation with
//        member this.annotation_sep = this.value.annotation_sep 

//type annotated<'id, 'n when 'n :> annotation>  = 'id * option<'n>
//
//type annotated_ident<'n when 'n :> annotation> = annotated<ident, 'n>
//
//let pretty_annotated (id, tyo) =
//    match tyo with
//    | None   -> sprintf "%O" id
//    | Some t -> sprintf "(%O %s %O)" id (t :> annotation).annotation_sep t


type annotated<'id, 'n>  = 'id * option<'n>

type annotated_ident<'n> = annotated<ident, 'n>

let pretty_annotated sep (id, tyo) =
    match tyo with
    | None   -> sprintf "%O" id
    | Some t -> sprintf "(%O %s %O)" id sep t
