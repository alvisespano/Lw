(*
 * Lw
 * Absyn.fs: Abstract Syntax
 * (C) 2000-2014 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Absyn

#nowarn "60"

open System
open System.Collections.Generic
open FSharp.Common
open FSharp.Common.Prelude
open FSharp.Common.Log
open FSharp.Common.Parsing


// misc stuff
//

let parse_float s = Double.Parse (s, Globalization.NumberStyles.Float, Globalization.CultureInfo.InvariantCulture)
let fresh_reserved_id () = sprintf Config.Printing.fresh_reserved_id_fmt (fresh_int ())
let wildcard_reserved_id () = sprintf Config.Printing.wildcard_reserved_fmt (fresh_int ())
let tuple_index_label = sprintf Config.Printing.tuple_index_label_fmt

type id = string

let (|SymString|_|) =
    let rex = new System.Text.RegularExpressions.Regex("([a-zA-Z_][a-zA-Z0-9_]*)|(__\\$[0-9]+)")
    in function
    | x when not (rex.IsMatch x) -> Some x
    | _ -> None

let (|Sym|_|) (|Id|_|) = function
    | Id (SymString _, r) -> Some r
    | _ -> None

type location =
    inherit Parsing.location
    new (filename : string, line : int, col : int, ?end_line : int, ?end_col : int, ?line_bias : int, ?col_bias : int) =
        { inherit Parsing.location (filename, line, col, ?end_line = end_line, ?end_col = end_col, ?line_bias = line_bias, ?col_bias = col_bias) }

    new (p1, ?p2, ?line_bias, ?col_bias) =
        { inherit Parsing.location (p1, ?p2 = p2, ?line_bias = line_bias, ?col_bias = col_bias) }

    new () = { inherit Parsing.location () }

type [< NoEquality; NoComparison >] node<'a, 't> (value : 'a, ?loc : location) =
    let mutable _typed : 't option = None
    member val value = value with get, set
    member val loc = defaultArg loc (new location ())
    abstract pretty : string
    default this.pretty = sprintf "%O" this.value
    override this.ToString () = this.pretty
    member this.typed
        with get () = match _typed with Some x -> x | None -> unexpected "node %O has not been typed" __SOURCE_FILE__ __LINE__ this
        and set t = _typed <- Some t

let Lo loc (x : 'a) = new node<_, _> (x, loc)
let ULo x = new node<_, _> (x)
let (|Lo|) (l : node<'a, _>) = l.value, l.loc
let (|ULo|) = function Lo (x, _) -> x

let (|Application|) (|App|_|) (|R|_|) =
    let (|L|_|) = function
        | App _ | R _ as x -> Some x
        | _ -> None
    in function
    | (L e1, R e2)  -> sprintf "%O %O" e1 e2
    | (e1, R e2)    -> sprintf "(%O) %O" e1 e2
    | (L e1, e2)    -> sprintf "%O (%O)" e1 e2
    | (e1, e2)      -> sprintf "(%O) (%O)" e1 e2

let Row_Tuple tup ps = tup (List.mapi (fun i p -> tuple_index_label (i + 1), p) ps, None)
let (|Row_Tuple|_|) (|Tup|_|) = function
    | Tup ((x1, _) :: _ as bs, None) when x1 = tuple_index_label 1 -> Some (List.map snd bs)
    | _ -> None

let Arrows arrow =
    let rec R = function
        | []      -> unexpected "empty arrow atom list" __SOURCE_FILE__ __LINE__
        | [x]     -> x
        | x :: xs -> arrow (x, R xs)
    in
        R

let rec (|Arrows|_|) (|Arrow|_|) = function
    | Arrow (x1, Arrows (|Arrow|_|) l) -> Some (x1 :: l)
    | Arrow (x1, x2)                   -> Some [x1; x2]
    | _                                -> None

let Apps app =
    let rec R = function
        | []        -> unexpected "empty app atom list" __SOURCE_FILE__ __LINE__
        | [x]       -> x
        | x :: xs   -> app (R xs, x)
    in
        fun xs -> R (List.rev xs)

let rec (|Apps|_|) (|App|_|) = function
    | App (Apps (|App|_|) l, x2) -> Some (l @ [x2])
    | App (x1, x2)               -> Some [x1; x2]
    | _                          -> None

type annotable =
    abstract annot_sep : string

type 'n param = id * 'n option

let pretty_param sep (id, tyo) =
    match tyo with
        | None   -> id
        | Some a -> sprintf "%s %s %O" id sep a


// variables
//

// TODO: reimplement variables by means of pointers; reimplement substitution accordingly as well
type var = Va of int * string option
with
    member this.uid =
        match this with
        | Va (n, _) -> n

    static member private auto_name fmt n =
        let start, endd = Config.Printing.dynamic.tyvar_range
        let start, endd = Convert.ToInt32 start, Convert.ToInt32 endd
        let bas = endd - start + 1
        let chr n = n + start |> Convert.ToChar |> Convert.ToString
        let rec div n = let n' = n / bas in (if n' = 0 then "" else div n') + (chr (n % bas))
        in
            sprintf fmt (div n)

    member private this.pretty_fmt fmt =
        match this with
        | Va (n, Some s) ->
            let r = sprintf fmt s
            #if DEBUG_TYVARS
            sprintf "%s_%d" r n
            #else
            r
            #endif

        | Va (n, None) ->
            let r = var.auto_name fmt n
            #if DEBUG_TYVARS
            sprintf "%s?%d" r n
            #else
            r
            #endif

    member this.pretty_quantified = this.pretty_fmt Config.Printing.dynamic.tyvar_quantified_fmt
    member this.pretty_unquantified = this.pretty_fmt Config.Printing.dynamic.tyvar_unquantified_fmt

    static member fresh = Va (fresh_int (), None)
    static member fresh_named s = Va (fresh_int (), Some s)

    member this.refresh =
        match this with
        | Va (_, so) -> Va (fresh_int (), so)

    static member private cnt = ref 0
    static member private env : Env.t<int, var> option ref = ref None
    static member private forall : Set<int> ref = ref Set.empty

    static member reset_normalization ?quantified_vars =
        let quantified_vars = defaultArg quantified_vars Set.empty
        var.cnt := 0
        var.env := Some Env.empty
        var.forall := Set.map (fun (α : var) -> α.uid) quantified_vars
        { new IDisposable with
            member __.Dispose () =
                var.env := None
                var.forall := Set.empty
        }

    override this.ToString () = this.pretty

    member this.pretty =
        let env = var.env
        match !env with
        | None     -> this.pretty_quantified
        | Some env ->
            let α =
                match env.search this.uid with
                | None   -> let n = !var.cnt
                            var.cnt := n + 1
                            let α = Va (n, match this with Va (_, so) -> so)
                            var.env := Some (env.bind this.uid α)
                            α
                | Some α -> α
            in
                if Set.contains this.uid !var.forall then α.pretty_quantified else α.pretty_unquantified


// kinds
//

type kind =
    | K_Var of var
    | K_Cons of id * kind list
with
    interface annotable with
        member __.annot_sep = "::"

let K_Arrow (k1, k2) = K_Cons ("->", [k1; k2])
let (|K_Arrow|_|) = function
    | K_Cons ("->", [k1; k2]) -> Some (k1, k2)
    | _ -> None

let K_Arrows = Arrows K_Arrow
let (|K_Arrows|_|) = (|Arrows|_|) (function K_Arrow (k1, k2) -> Some (k1, k2) | _ -> None)

let K_Id x = K_Cons (x, [])
let (|K_Id|_|) = function
    | K_Cons (x, []) -> Some x
    | _ -> None

let K_Star = K_Id "*"
let (|K_Star|_|) = function
    | K_Id "*" -> Some ()
    | _ -> None

let K_Row = K_Cons (Config.Typing.KindCons.row, [])
let (|K_Row|_|) = function
    | K_Cons (name, []) when name = Config.Typing.KindCons.row -> Some ()
    | _ -> None

let K_HTuple ks = K_Cons (Config.Typing.KindCons.htuple, ks)
let (|K_HTuple|_|) = function
    | K_Cons (name, ks) when name = Config.Typing.KindCons.htuple -> Some ks
    | _ -> None

type kind with
    member this.pretty =
        let (|A|_|) = function
            | K_Var _ 
            | K_Cons (_, []) as k -> Some k
            | _ ->  None
        let rec R = function
            | K_Var α                       -> sprintf "%O" α
            | K_Arrow (K_Arrow _ as k1, k2) -> sprintf "(%s) -> %s" (R k1) (R k2)
            | K_Arrow (k1, k2)              -> sprintf "%s -> %s" (R k1) (R k2)
            | K_HTuple ([] | [_])           -> unexpected "empty or unary tuple kind" __SOURCE_FILE__ __LINE__
            | K_HTuple ks                   -> sprintf "(%s)" (mappen_strings R ", " ks)
            | K_Cons (x, [])                -> x
            | K_Cons (x, [A k])             -> sprintf "%s %s" x (R k)
            | K_Cons (x, ks)                -> sprintf "%s (%s)" x (mappen_strings R ", " ks)
        in
            R this

    override this.ToString () = this.pretty

    static member fresh_var = K_Var var.fresh

type kinded_param = kind param


// bindings and cases
//

let pretty_and_bindings bs = flatten_stringables "\nand " bs

type [< NoEquality; NoComparison >] qbinding<'q, 'p, 'e, 'a> = { qual : 'q; patt : node<'p, 'a>; expr : node<'e, 'a> }
with
    override this.ToString () = this.pretty
    member this.pretty = sprintf "%O%O = %O" this.qual this.patt this.expr

type [< NoComparison; NoEquality >] rec_qbinding<'q, 'par, 'e, 'a when 'e :> annotable> = { qual : 'q; par : 'par param; expr : node<'e, 'a> }
with
    override this.ToString () = this.pretty
    member this.pretty = sprintf "%O%O = %O" this.qual (pretty_param this.expr.value.annot_sep this.par) this.expr

type [< NoComparison; NoEquality >] kind_binding = { id : id; pars : var list; kind : kind }
with
    override this.ToString () = this.pretty
    member this.pretty = sprintf "%s%s = %O" this.id (soprintf " (%s)" (match this.pars with [] -> None | αs -> Some (flatten_stringables ", " αs))) this.kind

type [< NoComparison; NoEquality >] signature_binding<'e, 'a when 'e :> annotable> = { id : id; signature : node<'e, 'a> }
with
    override this.ToString () = this.pretty
    member this.pretty = sprintf "%O %s %O" this.id this.signature.value.annot_sep this.signature

type [< NoComparison; NoEquality >] case<'p, 'e, 't > = node<'p, 't> * node<'e, 't> option * node<'e, 't>

let pretty_case = function
    | p, None, e    -> sprintf "%O -> %O" p e
    | p, Some we, e -> sprintf "%O when %O -> %O" p we e

let pretty_cases cases = mappen_strings pretty_case "\n  | " cases


// rows
//

let make_rows rowed ((|Rowed|_|) : id -> _ -> _) =
    let Record = rowed Config.Typing.TyCons.Rows.record
    let (|Record|_|) = (|Rowed|_|) Config.Typing.TyCons.Rows.record
    let Variant = rowed Config.Typing.TyCons.Rows.variant
    let (|Variant|_|) = (|Rowed|_|) Config.Typing.TyCons.Rows.variant
    let Tuple = Row_Tuple Record
    let (|Tuple|_|) = (|Row_Tuple|_|) (|Record|_|)
    in
        Record, Variant, Tuple, (|Record|_|), (|Variant|_|), (|Tuple|_|)

let pretty_row sep binder = function
    | [], Some x -> sprintf "%O :: %O" x K_Row
    | xes, xo ->
        let s = mappen_strings (fun (x, e) -> sprintf "%s %s %O" x binder e) sep xes
        in
            match xo with
                | None   -> s
                | Some x -> sprintf "%s | %O" s x



// type patterns & expressions
//

type [< NoComparison; NoEquality >] ty_decl_qual = Dummy_ty_decl_qual
with
    override this.ToString () = this.pretty

    member q.pretty = ""

    static member none = Dummy_ty_decl_qual

type [< NoComparison; NoEquality >] ty_upatt =
    | Tp_Var of id
    | Tp_Cons of id
    | Tp_Annot of ty_patt * kind
    | Tp_App of (ty_patt * ty_patt)
    | Tp_HTuple of ty_patt list
    | Tp_Or of ty_patt * ty_patt
    | Tp_And of ty_patt * ty_patt
    | Tp_As of ty_patt * id
    | Tp_Wildcard
    | Tp_Row of (id * ty_patt) list * ty_patt option
with
    interface annotable with
        member __.annot_sep = "::"

and [< NoComparison; NoEquality >] ty_uexpr =
    | Te_PolyVar of id
//    | Te_Var of id
    | Te_Id of id
    | Te_Lambda of kinded_param * ty_expr
    | Te_HTuple of ty_expr list
    | Te_App of (ty_expr * ty_expr)
    | Te_Let of ty_decl * ty_expr
    | Te_Match of ty_expr * ty_case list
    | Te_Annot of ty_expr * kind
    | Te_Row of (id * ty_expr) list * ty_expr option
with
    interface annotable with
        member __.annot_sep = "::"

and [< NoComparison; NoEquality >] ty_udecl =
    | Td_Bind of ty_binding list
    | Td_Rec of ty_rec_binding list
    | Td_Kind of kind_binding list

and ty_binding = qbinding<ty_decl_qual, ty_upatt, ty_uexpr, kind>
and ty_rec_binding = rec_qbinding<ty_decl_qual, kind, ty_uexpr, kind>

and ty_expr = node<ty_uexpr, kind>
and ty_patt = node<ty_upatt, kind>
and ty_decl = node<ty_udecl, unit>
and ty_case = case<ty_upatt, ty_uexpr, kind>

and typed_param = ty_expr param

let private Te_Primitive name = Te_Id name
let Te_Unit = Te_Primitive "unit"

// special patterns for type expressions

let Te_Apps τs = (Apps (fun (τ1, τ2) -> Lo τ1.loc <| Te_App (τ1, τ2)) τs).value
let (|Te_Apps|_|) = (|Apps|_|) (function Te_App (ULo τ1, ULo τ2) -> Some (τ1, τ2) | _ -> None)

let Te_Arrow_Cons = Te_Id "->"
let (|Te_Arrow_Cons|_|) = function
    | Te_Id "->" -> Some ()
    | _ -> None

let Te_Arrow (t1 : ty_expr, t2 : ty_expr) = Te_Apps [Lo t1.loc Te_Arrow_Cons; t1; t2]
let (|Te_Arrow|_|) = function
    | Te_Apps [Te_Arrow_Cons; t1; t2] -> Some (t1, t2)
    | _ -> None

let Te_Arrows τs = (Arrows (fun (e1 : ty_expr, e2) -> Lo e1.loc <| Te_Arrow (e1, e2)) τs).value

let private Te_Rowed name r = Te_App (ULo <| Te_Id name, ULo <| Te_Row r)
let private (|Te_Rowed|_|) name = function
    | Te_App (ULo (Te_Id name'), ULo (Te_Row (xes, xo))) when name = name' -> Some (xes, xo)
    | _ -> None

let Te_Record, Te_Variant, Te_Tuple, (|Te_Record|_|), (|Te_Variant|_|), (|Te_Tuple|_|) = make_rows Te_Rowed (|Te_Rowed|_|)

// special patterns for type patterns

let Tp_Arrow_Cons = Tp_Cons "->"
let (|Tp_Arrow_Cons|_|) = function
    | Tp_Cons "->" -> Some ()
    | _ -> None

let Tp_Apps ps = (Apps (fun (τ1, τ2) -> Lo τ1.loc <| Tp_App (τ1, τ2)) ps).value
let (|Tp_Apps|_|) = (|Apps|_|) (function Tp_App (ULo τ1, ULo τ2) -> Some (τ1, τ2) | _ -> None)

let Tp_Arrow (t1 : ty_patt, t2) = Tp_Apps [Lo t1.loc Tp_Arrow_Cons; t1; t2]
let (|Tp_Arrow|_|) = function
    | Tp_Apps [Tp_Arrow_Cons; t1; t2] -> Some (t1, t2)
    | _ -> None

let private Tp_Rowed name r = Tp_App (ULo <| Tp_Var name, ULo <| Tp_Row r)
let private (|Tp_Rowed|_|) name = function
    | Tp_App (ULo (Tp_Var name'), ULo (Tp_Row (xes, xo))) when name = name' -> Some (xes, xo)
    | _ -> None

let Tp_Record, Tp_Variant, Tp_Tuple, (|Tp_Record|_|), (|Tp_Variant|_|), (|Tp_Tuple|_|) = make_rows Tp_Rowed (|Tp_Rowed|_|)

type ty_upatt with
    override this.ToString () = this.pretty

    member this.pretty =
        let (|App|) =
            let (|R|_|) = function
                | ULo (Tp_Cons _ | Tp_Var _) as e -> Some e
                | _ -> None
            in
                (|Application|) (function ULo (Tp_App (p1, p2)) -> Some (p1, p2) | _ -> None) (|R|_|)
        let (|Tp_Sym|_|) = (|Sym|_|) (function Tp_Var x | Tp_Cons x -> Some (x, x) | _ -> None)
        match this with
            | Tp_Sym x              -> sprintf "(%O)" x
            | Tp_Var x
            | Tp_Cons x             -> x
            | Tp_Tuple ([] | [_])   -> unexpected "empty or unary tuple type pattern" __SOURCE_FILE__ __LINE__
            | Tp_Tuple ps           -> sprintf "(%s)" (flatten_stringables " * " ps)
            | Tp_Record row         -> sprintf "{ %s }" (pretty_row "; " ":" row)
            | Tp_Variant row        -> sprintf "< %s >" (pretty_row " | " ":" row)
            | Tp_HTuple ([] | [_])  -> unexpected "empty or unary tupled type pattern" __SOURCE_FILE__ __LINE__
            | Tp_HTuple ps          -> sprintf "(%s)" (flatten_stringables ", " ps)
            | Tp_App (App s)        -> s
            | Tp_Annot (p, t)       -> sprintf "(%O : %O)" p t
            | Tp_As (p, x)          -> sprintf "(%O as %s)" p x
            | Tp_Or (p1, p2)        -> sprintf "(%O | %O)" p1 p2
            | Tp_And (p1, p2)       -> sprintf "(%O & %O)" p1 p2
            | Tp_Wildcard           -> "_"
            | Tp_Row (bs, o)        -> sprintf "(| %s |)" (pretty_row " | " ":" (bs, o))

type ty_uexpr with
    override this.ToString () = this.pretty

    member this.pretty =
        let (|App|) =
            let (|R|_|) = function
                | ULo (Te_PolyVar _ | Te_Record _ | Te_Variant _ | Te_Id _) as e -> Some e
                | _ -> None
            in
                (|Application|) (function ULo (Te_App (e1, e2)) -> Some (e1, e2) | _ -> None) (|R|_|)
        let (|Te_Sym|_|) = (|Sym|_|) (function Te_Id x -> Some (x, x) | _ -> None)
        match this with
            | Te_Sym x                 -> sprintf "(%O)" x
            | Te_PolyVar x             -> sprintf Config.Printing.dynamic.tyvar_quantified_fmt x
//            | Te_Var x
            | Te_Id x                  -> x
            | Te_Tuple ([] | [_])      -> unexpected "empty or unary tuple type expression" __SOURCE_FILE__ __LINE__
            | Te_Tuple es              -> sprintf "(%s)" (flatten_stringables " * " es)
            | Te_Record row            -> sprintf "{ %s }" (pretty_row "; " ":" row)
            | Te_Variant row           -> sprintf "< %s >" (pretty_row " | " ":" row)
            | Te_HTuple ([] | [_])     -> unexpected "empty or unary tupled type expression" __SOURCE_FILE__ __LINE__
            | Te_HTuple es             -> sprintf "(%s)" (flatten_stringables ", " es)

            // NOTE: arrow must be matched BEFORE app 
            | Te_Arrow (Te_Arrow _ as t1, t2) -> sprintf "(%O) -> %Os" t1 t2
            | Te_Arrow (t1, t2)               -> sprintf "%O -> %O" t1 t2

            | Te_App (App s)           -> s
            | Te_Lambda (ka, e)        -> sprintf "fun %s -> %O" (pretty_param "::" ka) e
            | Te_Annot (e, ty)         -> sprintf "(%O : %O)" e ty
            | Te_Let (d, e)            -> sprintf "let %O in %O" d e
            | Te_Match (e, cases)      -> sprintf "match %O with\n| %s" e (pretty_cases cases)
            | Te_Row (bs, o)           -> sprintf "(| %s |)" (pretty_row " | " ":" (bs, o))

type ty_udecl with       
    override this.ToString () = this.pretty

    member this.pretty =
        match this with
            | Td_Rec []
            | Td_Kind []
            | Td_Bind []    -> unexpected "empty declaration list" __SOURCE_FILE__ __LINE__
            | Td_Rec bs     -> sprintf "type %s" (pretty_and_bindings bs)
            | Td_Kind bs    -> sprintf "kind %s" (pretty_and_bindings bs)
            | Td_Bind bs    -> sprintf "let %s" (pretty_and_bindings bs)


// literals
//

type [< NoComparison >] lit =
    | Int of int
    | Float of float
    | Bool of bool
    | Char of char
    | String of string
    | Unit
with
    override this.ToString () = this.pretty

    member this.pretty =
        match this with
            | Int n      -> sprintf "%d" n
            | Float x    -> sprintf "%g" x
            | Bool b     -> sprintf "%b" b
            | String s   -> sprintf "\"%s\"" s
            | Char c     -> sprintf "'%c'" c
            | Unit       -> "()"


// patterns
//

type [< NoComparison; NoEquality >] upatt =
    | P_Var of id
    | P_Cons of id  // internal use only
    | P_PolyCons of id
    | P_App of (patt * patt)
    | P_Lit of lit
    | P_Annot of patt * ty_expr
    | P_As of patt * id
    | P_Wildcard
    | P_Or of patt * patt
    | P_And of patt * patt
    | P_Record of (id * patt) list

and [< NoComparison; NoEquality >] patt = node<upatt, unit>

let P_Tuple = Row_Tuple (fun (bs, _) -> P_Record bs)
let (|P_Tuple|_|) = (|Row_Tuple|_|) (function P_Record bs -> Some (bs, None) | _ -> None)

let P_Apps ps = (Apps (fun (p1, p2) -> Lo p1.loc <| P_App (p1, p2)) ps).value
let (|P_Apps|_|) = (|Apps|_|) (function P_App (ULo p1, ULo p2) -> Some (p1, p2) | _ -> None)

type upatt with
    override this.ToString () = this.pretty

    member this.pretty =
        let (|A|) =
            let (|R|_|) = function
                | (ULo (P_PolyCons _ | P_Cons _ | P_Var _)) as p -> Some p
                | _ -> None
            let (|L|_|) = function
                | ULo (P_App _) | R _ as p -> Some p
                | _ -> None
            in
                (|Application|) (|L|_|) (|R|_|)
        let (|P_Sym|_|) = (|Sym|_|) (function P_Var x | P_PolyCons x -> Some (x, x) | _ -> None)
        match this with
            | P_Sym x                                 -> sprintf "(%O)" x
            | P_Var x
            | P_Cons x                                -> x
            | P_PolyCons x                            -> sprintf Config.Printing.polycons_fmt x
            | P_Lit lit                               -> lit.pretty
            | P_Tuple ([] | [_])                      -> unexpected "empty or unary tuple pattern" __SOURCE_FILE__ __LINE__
            | P_Tuple ps                              -> sprintf "(%s)" (flatten_stringables ", " ps)
            | P_App (A s)                             -> s
            | P_Annot (p, t)                          -> sprintf "(%O : %O)" p t
            | P_As (p, x)                             -> sprintf "(%O as %s)" p x
            | P_Or (p1, p2)                           -> sprintf "(%O | %O)" p1 p2
            | P_And (p1, p2)                          -> sprintf "(%O & %O)" p1 p2
            | P_Wildcard                              -> "_"
            | P_Record bs                             -> sprintf "{ %s }" (mappen_strings (fun (x, e) -> sprintf "%s = %O" x e) "; " bs)



// expressions and declarations
//

type [< NoComparison; NoEquality >] decl_qual =
    {
        over : bool
    }
with
    override this.ToString () = this.pretty

    member q.pretty =
        match q with
            | { over = false } -> ""
            | { over = true }  -> "over"

    static member none = { over = false }

    member this.as_tokens = [this.pretty]

//type [< NoComparison; NoEquality >] var_qual =
//    | VaQ_Strict
//    | VaQ_Flex
//with
//    member this.is_strict =
//        match this with
//            | VaQ_Strict -> true
//            | VaQ_Flex   -> false
//
//    member this.pretty_id id =
//        match this with
//            | VaQ_Strict  -> id
//            | VaQ_Flex    -> sprintf "%s#" id

type [< NoComparison; NoEquality >] uexpr =
    | Lit of lit
    | Var of id
    | Reserved_Cons of id    // internal only
    | FreeVar of id
    | PolyCons of id
    | Loosen of expr
    | Record of (id * expr) list * expr option
    | Lambda of typed_param * expr
    | If of expr * expr * expr
    | App of (expr * expr)
    | Let of decl * expr
    | Match of expr * expr_case list
    | Select of expr * id
    | Restrict of expr * id
    | Annot of expr * ty_expr
    | Combine of expr list
    | Val of expr
    | Solve of expr * ty_expr
    | Inject of expr
    | Eject of expr
with
    interface annotable with
        member __.annot_sep = ":"
 
and binding = qbinding<decl_qual, upatt, uexpr, unit>
and rec_binding = rec_qbinding<decl_qual, ty_expr, uexpr, unit>
and overload_binding = signature_binding<ty_uexpr, kind>
and [< NoComparison; NoEquality >] datatype_binding = { id : id; kind : kind; datacons : signature_binding<ty_uexpr, kind> list }

and [< NoComparison; NoEquality >] udecl =
    | D_Bind of binding list
    | D_Rec of rec_binding list
    | D_Type of ty_rec_binding list
    | D_Kind of kind_binding list
    | D_Overload of overload_binding list
    | D_Open of decl_qual * expr
    | D_Datatype of datatype_binding
    | D_Reserved_Multi of decl list

and expr = node<uexpr, unit>
and decl = node<udecl, unit>
and expr_case = case<upatt, uexpr, unit>

let Id x = Var x
let (|Id|_|) = function
    | Var x -> Some x
    | _ -> None

let Tuple = Row_Tuple Record
let (|Tuple|_|) = (|Row_Tuple|_|) (function Record (bs, o) -> Some (bs, o) | _ -> None)

type uexpr with
    override this.ToString () = this.pretty

    member this.pretty =
        let (|A|) =
            let (|R|_|) = function
                | (ULo (Lit _ | Var _ | FreeVar _ | Reserved_Cons _ | Record _ | Select _)) as e -> Some e
                | _ -> None
            let (|L|_|) = function
                | ULo (App _) | R _ as e -> Some e
                | _ -> None
            in
                (|Application|) (|L|_|) (|R|_|)
        let (|Sym|_|) = (|Sym|_|) (function Var x | FreeVar x -> Some (x, x) | _ -> None)
        match this with
            | Lit l                 -> l.pretty
            | Sym x                 -> sprintf "(%s)" x
            | Var x                 -> sprintf "%s" x
            | Reserved_Cons x       -> x
            | FreeVar x             -> sprintf Config.Printing.freevar_fmt x
            | PolyCons x            -> sprintf Config.Printing.polycons_fmt x
            | App (A s)             -> s
            | Lambda (ta, e)        -> sprintf "fun %s -> %O" (pretty_param ":" ta) e
            | Select (e, id)        -> sprintf "%O.%s" e id
            | Restrict (e, id)      -> sprintf "%O \ %s" e id
            | If (e1, e2, e3)       -> sprintf "if %O then %O else %O" e1 e2 e3
            | Annot (e, τ)          -> sprintf "(%O : %O)" e τ
            | Let (d, e)            -> sprintf "%O in %O" d e
            | Match (e, cases)      -> sprintf "match %O with\n| %s" e (pretty_cases cases)
            | Tuple ([] | [_])      -> unexpected "empty or unary tuple expression" __SOURCE_FILE__ __LINE__ this
            | Tuple es              -> sprintf "(%s)" (flatten_stringables ", " es)
            | Combine es            -> flatten_stringables "; " es
            | Val e                 -> sprintf "val %O" e
            | Solve (e, τ)          -> sprintf "%O where %O" e τ
            | Record (bs, None)     -> sprintf "{ %s }" (mappen_strings (fun (x, e) -> sprintf "%s = %O" x e) "; " bs)
            | Record (bs, Some e)   -> sprintf "{ %s | %O }" (mappen_strings (fun (x, e) -> sprintf "%s = %O" x e) "; " bs) e
            | Inject e              -> sprintf "\_ %O" e
            | Eject e               -> sprintf "%O _/" e
            | Loosen e              -> sprintf "(%O)#" e


type udecl with       
    override this.ToString () = this.pretty

    member this.pretty =
        match this with
            | D_Type []
            | D_Kind []
            | D_Bind []
            | D_Rec []
            | D_Overload []
            | D_Reserved_Multi [] -> unexpected "empty declaration list" __SOURCE_FILE__ __LINE__
            | D_Type bs           -> sprintf "type %s" (pretty_and_bindings bs)
            | D_Kind bs           -> sprintf "kind %s" (pretty_and_bindings bs)
            | D_Bind bs           -> sprintf "let %s" (pretty_and_bindings bs)
            | D_Rec bs            -> sprintf "let rec %s" (pretty_and_bindings bs)
            | D_Overload bs       -> sprintf "overload %s" (pretty_and_bindings bs)
            | D_Open (q, e)       -> sprintf "open %O%O" q e
            | D_Datatype dt       -> sprintf "datatype %s :: %O with %s" dt.id dt.kind (flatten_stringables " | " dt.datacons)
            | D_Reserved_Multi ds -> flatten_stringables ";; " ds


type [< NoComparison; NoEquality >] program =
  { namespacee : id option
    decls      : decl list
    main       : expr option
  }
with
    override this.ToString () = this.pretty

    member this.pretty =
        sprintf "%s%s%s\n" (soprintf "namespace %s\n\n" this.namespacee) (flatten_stringables "\n" this.decls) (soprintf "\n\n;;\n\n%O" this.main)

type [< NoComparison; NoEquality >] interactive_line =
    | Line_Expr of expr
    | Line_Decl of decl
with
    override this.ToString () = this.pretty
    member this.pretty =
        match this with
            | Line_Expr e -> e.pretty
            | Line_Decl d -> d.pretty
    
    
// misc parsing sugars
//

let lambda_function lambda matchh id (cases : case<_, _, _> list) =
    let loc = let p, _, _ = cases.[0] in p.loc
    let L = Lo loc
    let x = fresh_reserved_id ()
    in
        L <| lambda ((x, None), (L <| matchh (L <| id x, cases)))

let LambdaFunction = lambda_function Lambda Match Id
let Te_LambdaFunction = lambda_function Te_Lambda Te_Match Te_Id

let lambda_fun (|P_Annot|_|) (|P_Tuple|_|) (|P_Var|_|) (|P_Wildcard|_|) (|P_Custom|_|) lambda lambda_function = function
    | [], _ -> unexpected "empty lambda parameter list" __SOURCE_FILE__ __LINE__
    | ps, e ->
        List.foldBack (fun (p : node<_, _>) (e : node<_, _>) ->
                let loc = p.loc
                let rec f = function
                    | P_Annot (ULo (P_Var x), t) -> Lo loc <| lambda ((x, Some t), e)
                    | P_Tuple ([_] | [])         -> unexpected "empty or unary tuple pattern" __SOURCE_FILE__ __LINE__
                    | P_Var x                    -> Lo loc <| lambda ((x, None), e)
                    | P_Wildcard                 -> Lo loc <| lambda ((wildcard_reserved_id (), None), e)
                    | P_Custom p e e'            -> Lo loc e'
                    | _                          -> lambda_function [p, None, e]
                in
                    f p.value)
            ps e

let LambdaFun =
    let (|P_Annot|_|) = function
        | P_Annot (a, b) -> Some (a, b)
        | _ -> None
    let (|P_Var|_|) = function
        | P_Var r -> Some r
        | _ -> None
    let (|P_Wildcard|_|) = function
        | P_Wildcard -> Some ()
        | _ -> None
    let (|P_Custom|_|) (p : node<_, _>) (e : node<_, _>) = function
        | P_Lit Unit -> Some (Lambda ((wildcard_reserved_id (), Some (Lo p.loc Te_Unit)), e))
        | _ -> None
    in
        lambda_fun (|P_Annot|_|) (|P_Tuple|_|) (|P_Var|_|) (|P_Wildcard|_|) (|P_Custom|_|) Lambda LambdaFunction

let Te_LambdaFun =
    let (|P_Annot|_|) = function
        | Tp_Annot (a, b) -> Some (a, b)
        | _ -> None
    let (|P_Var|_|) = function
        | Tp_Var r -> Some r
        | _ -> None
    let (|P_Wildcard|_|) = function
        | Tp_Wildcard -> Some ()
        | _ -> None
    let (|P_Custom|_|) _ _ _ = None
    in
        lambda_fun (|P_Annot|_|) (|Tp_Tuple|_|) (|P_Var|_|) (|P_Wildcard|_|) (|P_Custom|_|) Te_Lambda Te_LambdaFunction
        
let lambda_cases lambdafun p_var var matchh tuple p_tuple =
    let tuple = function
        | [e : node<_, _>] -> e.value
        | es  -> tuple es
    let p_tuple = function
        | [p : node<_, _>] -> p.value
        | ps  -> p_tuple ps
    function
    | [ps, None, e] -> lambdafun (ps, e)
    | (p0 : node<_, _> :: _ as ps0, _, _) :: cases' as cases ->
        let len0 = List.length ps0
        let L0 x = Lo p0.loc x
        for ps, _, _ in cases' do
            if List.length ps <> len0 then
                raise (Parsing.syntax_error (sprintf "number of function parameters expected to be %d across all cases" len0, p0.loc))
        let ids = List.init len0 (fun _ -> fresh_reserved_id ())
        let pars f = List.mapi (fun i (p : node<_, _>) -> Lo p.loc <| f ids.[i]) ps0
        let cases = List.map (fun (ps, weo, e) -> L0 <| p_tuple ps, weo, e) cases
        in
            lambdafun (pars p_var, L0 <| matchh (L0 <| tuple (pars var), cases))

    | l -> unexpected "ill-formed lambda case list: %O" __SOURCE_FILE__ __LINE__ l
    
let LambdaCases x = lambda_cases LambdaFun P_Var Id Match Tuple P_Tuple x
let Te_LambdaCases x = lambda_cases Te_LambdaFun Tp_Var Te_Id Te_Match Te_Tuple Tp_Tuple  x
            
let RecLambda ((x, t), cases) =
    let e = LambdaCases cases
    let L x = Lo (let _, _, e = cases.[0] in e.loc) x
    in
        L <| Let (L <| D_Rec [{ qual = decl_qual.none; par = (x, t); expr = e }], L <| Id x)

let lets lett (ds, e) = List.foldBack (fun d e -> Lo e.loc <| lett (d, e)) ds e

let Lets x = lets Let x
let Te_Lets x = lets Te_Let x

let UnApp (op, e : expr) = App (Lo e.loc <| Id op, e)
let BinApp (e1 : expr, op, e2 : expr) = App (Lo e1.loc <| App (Lo e2.loc <| Id op, e1), e2)

let EApps es = (Apps (fun (e1, e2) -> Lo e1.loc <| App (e1, e2)) es).value
let List_Nil = Var Config.Typing.list_nil
let List_Cons (e1, e2) = EApps [ULo (Var Config.Typing.list_cons); e1; e2]
let List_Seq (es : expr list) = List.foldBack (fun e z -> List_Cons (e, Lo e.loc z)) es List_Nil

let P_List_Nil = P_Cons Config.Typing.list_nil
let P_List_Cons (p1, p2) = P_Apps [ULo (P_Cons Config.Typing.list_cons); p1; p2]
let P_List_Seq (ps : patt list) = List.foldBack (fun p z -> P_List_Cons (p, Lo p.loc z)) ps P_List_Nil



// parser auxiliary tools
//

module Aux =
    
    let pos (parseState : Microsoft.FSharp.Text.Parsing.IParseState) n x =
        let p1 = parseState.InputStartPosition n
        let p2 = parseState.InputEndPosition n
        let loc = new location (p1, p2, Config.Parsing.line_bias, Config.Parsing.col_bias)
        in
            Lo loc x

    let sugar_with_reserved_id (parseState : Microsoft.FSharp.Text.Parsing.IParseState) f =
        let x = fresh_reserved_id ()
        let p1, p2 = parseState.ResultRange
        let loc = new location (p1, p2, Config.Parsing.line_bias, Config.Parsing.col_bias)
        in
            f x (Lo loc)
