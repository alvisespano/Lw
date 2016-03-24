(*
 * Lw
 * Absyn/AST.fs: main AST
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Absyn.Ast

#nowarn "60"

open System
open System.Collections.Generic
open FSharp.Common
open FSharp.Common.Log
open FSharp.Common.Parsing
open Lw.Core
open Lw.Core.Globals
open Lw.Core.Absyn.Misc
open Lw.Core.Absyn.Var
open Lw.Core.Absyn.Kind
open Lw.Core.Absyn.Factory


// bindings and cases
//

let pretty_and_bindings bs = flatten_stringables "\nand " bs

type [< NoEquality; NoComparison >] qbinding<'q, 'p, 'e, 'a> = { qual : 'q; patt : node<'p, 'a>; expr : node<'e, 'a> }
with
    override this.ToString () = this.pretty
    member this.pretty = sprintf "%O%O = %O" this.qual this.patt this.expr

type [< NoComparison; NoEquality >] rec_qbinding<'q, 'par, 'e, 'a when 'e :> annotable> = { qual : 'q; par : 'par id_param; expr : node<'e, 'a> }
with
    override this.ToString () = this.pretty
    member this.pretty = sprintf "%O%O = %O" this.qual (pretty_param this.expr.value.annot_sep this.par) this.expr

type [< NoComparison; NoEquality >] kind_binding = { id : ident; pars : var list; kind : kind }
with
    override this.ToString () = this.pretty
    member this.pretty = sprintf "%s%s = %O" this.id (soprintf " (%s)" (match this.pars with [] -> None | αs -> Some (flatten_stringables ", " αs))) this.kind

type [< NoComparison; NoEquality >] signature_binding<'e, 'a when 'e :> annotable> = { id : ident; signature : node<'e, 'a> }
with
    override this.ToString () = this.pretty
    member this.pretty = sprintf "%O %s %O" this.id this.signature.value.annot_sep this.signature

type [< NoComparison; NoEquality >] case<'p, 'e, 't > = node<'p, 't> * node<'e, 't> option * node<'e, 't>

let pretty_case = function
    | p, None, e    -> sprintf "%O -> %O" p e
    | p, Some we, e -> sprintf "%O when %O -> %O" p we e

let pretty_cases cases = mappen_strings pretty_case "\n  | " cases



// type patterns & expressions
//

type [< NoComparison; NoEquality >] ty_decl_qual = Dummy_ty_decl_qual
with
    override this.ToString () = this.pretty

    member q.pretty = ""

    static member none = Dummy_ty_decl_qual

type [< NoComparison; NoEquality >] ty_upatt =
    | Tp_Var of ident
    | Tp_Cons of ident
    | Tp_Annot of ty_patt * kind
    | Tp_App of (ty_patt * ty_patt)
    | Tp_HTuple of ty_patt list
    | Tp_Or of ty_patt * ty_patt
    | Tp_And of ty_patt * ty_patt
    | Tp_As of ty_patt * ident
    | Tp_Wildcard
    | Tp_Row of (ident * ty_patt) list * ty_patt option
with
    interface annotable with
        member __.annot_sep = Config.Printing.kind_annotation_sep

and [< NoComparison; NoEquality >] ty_uexpr =
    | Te_Var of ident
    | Te_Cons of ident
    | Te_Lambda of kinded_param * ty_expr
    | Te_HTuple of ty_expr list
    | Te_App of (ty_expr * ty_expr)
    | Te_Let of ty_decl * ty_expr
    | Te_Match of ty_expr * ty_case list
    | Te_Annot of ty_expr * kind
    | Te_Row of (ident * ty_expr) list * ty_expr option
    | Te_Forall of kinded_param * ty_expr
with
    interface annotable with
        member __.annot_sep = Config.Printing.kind_annotation_sep

and [< NoComparison; NoEquality >] fxty_uexpr =
    | Fxe_Bottom
    | Fxe_Forall of (kinded_param * fxty_expr option) * fxty_expr
    | Fxe_F_Ty of ty_expr
with
    interface annotable with
        member __.annot_sep = Config.Printing.kind_annotation_sep

and [< NoComparison; NoEquality >] ty_udecl =
    | Td_Bind of ty_binding list
    | Td_Rec of ty_rec_binding list
    | Td_Kind of kind_binding list

and ty_binding = qbinding<ty_decl_qual, ty_upatt, ty_uexpr, kind>
and ty_rec_binding = rec_qbinding<ty_decl_qual, kind, ty_uexpr, kind>

and ty_expr = node<ty_uexpr, kind>
and fxty_expr = node<fxty_uexpr, kind>
and ty_patt = node<ty_upatt, kind>
and ty_decl = node<ty_udecl, kind>
and ty_case = case<ty_upatt, ty_uexpr, kind>

and typed_param = ty_expr id_param

let private Te_Primitive name = Te_Cons name
let Te_Unit = Te_Primitive Config.Typing.Names.Type.unit

// special patterns for type expressions and type patterns

/// This magic function transforms a pattern factory into the same factory supporting nodes.
let nodify make app (|App|_|) =
    let f (loc, x) = Lo loc x
    let (|F|) (n : node<_, _>) = n.loc, n.value
    let app (x1 : node<_, _>, x2 : node<_, _>) = x1.loc + x2.loc, app (x1, x2)
    let (|App|_|) (_, u) = match u with App (τ1, τ2) -> Some (τ1, τ2) | _ -> None
    let Apps, (|Apps1|), (|Apps|_|) = make f (|F|) app (|App|_|)
    let l f x = f (new location (), x)
    in
        Apps >> snd, l (|Apps1|), l (|Apps|_|) 

let Te_Apps, (|Te_Apps1|), (|Te_Apps|_|) = nodify make_apps_by Te_App (function Te_App (τ1, τ2) -> Some (τ1, τ2) | _ -> None)
let Te_Arrow, (|Te_Arrow|_|) = let A = Config.Typing.Names.Type.arrow in make_arrow_by_apps (ULo (Te_Cons A)) Te_Apps (function ULo (Te_Cons x) when x = A -> Some () | _ -> None) (|Te_Apps|_|)
let Te_Arrows, (|Te_Arrows1|), (|Te_Arrows|_|) = nodify make_arrows_by Te_Arrow (|Te_Arrow|_|)
let Te_Foralls, (|Te_Foralls0|), (|Te_Foralls|_|) = make_foralls (fun (α, τ) -> Lo τ.loc <| Te_Forall (α, τ)) (function ULo (Te_Forall (α, τ)) -> Some (α, τ) | _ -> None)
let Fxe_Foralls, (|Fxe_Foralls0|), (|Fxe_Foralls|_|) = make_foralls (fun (α, τ) -> Lo τ.loc <| Fxe_Forall (α, τ)) (function ULo (Fxe_Forall (α, τ)) -> Some (α, τ) | _ -> None)

let Te_Record, Te_Variant, Te_Tuple, (|Te_Record|_|), (|Te_Variant|_|), (|Te_Tuple|_|) =
    let Te_Rowed name r = Te_App (ULo <| Te_Cons name, ULo <| Te_Row r)
    let (|Te_Rowed|_|) name = function
        | Te_App (ULo (Te_Cons name'), ULo (Te_Row (xes, xo))) when name = name' -> Some (xes, xo)
        | _ -> None
    in
        make_rows Te_Rowed (|Te_Rowed|_|)

let Tp_Apps, (|Tp_Apps1|), (|Tp_Apps|_|) = nodify make_apps_by Tp_App (function Tp_App (τ1, τ2) -> Some (τ1, τ2) | _ -> None)
let Tp_Arrow, (|Tp_Arrow|_|) = let A = Config.Typing.Names.Type.arrow in make_arrow_by_apps (ULo (Tp_Cons A)) Tp_Apps (function ULo (Tp_Cons x) when x = A -> Some () | _ -> None) (|Tp_Apps|_|)
let Tp_Arrows, (|Tp_Arrows1|), (|Tp_Arrows|_|) = nodify make_arrows_by Tp_Arrow (|Tp_Arrow|_|)
// TODO: type patterns do not have the forall case yet
//let Tp_Foralls, (|Tp_Foralls0|), (|Tp_Foralls|_|) = make_foralls (fun (α, τ) -> Lo τ.loc <| Tp_Forall (α, τ)) (function ULo (Tp_Forall (α, τ)) -> Some (α, τ) | _ -> None)

let Tp_Record, Tp_Variant, Tp_Tuple, (|Tp_Record|_|), (|Tp_Variant|_|), (|Tp_Tuple|_|) =
    let Tp_Rowed name r = Tp_App (ULo <| Tp_Var name, ULo <| Tp_Row r)
    let (|Tp_Rowed|_|) name = function
        | Tp_App (ULo (Tp_Var name'), ULo (Tp_Row (xes, xo))) when name = name' -> Some (xes, xo)
        | _ -> None
    in
        make_rows Tp_Rowed (|Tp_Rowed|_|)

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
            | Tp_Record row         -> sprintf "{ %s }" (pretty_row "; " Config.Printing.type_annotation_sep row)
            | Tp_Variant row        -> sprintf "< %s >" (pretty_row " | " Config.Printing.type_annotation_sep row)
            | Tp_HTuple ([] | [_])  -> unexpected "empty or unary tupled type pattern" __SOURCE_FILE__ __LINE__
            | Tp_HTuple ps          -> sprintf "(%s)" (flatten_stringables ", " ps)
            | Tp_App (App s)        -> s
            | Tp_Annot (p, t)       -> sprintf "(%O : %O)" p t
            | Tp_As (p, x)          -> sprintf "(%O as %s)" p x
            | Tp_Or (p1, p2)        -> sprintf "(%O | %O)" p1 p2
            | Tp_And (p1, p2)       -> sprintf "(%O & %O)" p1 p2
            | Tp_Wildcard           -> "_"
            | Tp_Row (bs, o)        -> sprintf "(| %s |)" (pretty_row " | " Config.Printing.type_annotation_sep (bs, o))

type ty_uexpr with
    override this.ToString () = this.pretty

    member this.pretty =
        let (|App|) =
            let (|R|_|) = function
                | ULo (Te_Var _ | Te_Record _ | Te_Variant _ | Te_Cons _) as e -> Some e
                | _ -> None
            in
                (|Application|) (function ULo (Te_App (e1, e2)) -> Some (e1, e2) | _ -> None) (|R|_|)
        let (|Te_Sym|_|) = (|Sym|_|) (function Te_Cons x -> Some (x, x) | _ -> None)
        match this with
            | Te_Sym x                 -> sprintf "(%O)" x
            | Te_Var x             -> sprintf Config.Printing.dynamic.tyvar_quantified_fmt x
            | Te_Cons x                  -> x
            | Te_Tuple ([] | [_])      -> unexpected "empty or unary tuple type expression" __SOURCE_FILE__ __LINE__
            | Te_Tuple es              -> sprintf "(%s)" (flatten_stringables " * " es)
            | Te_Record row            -> sprintf "{ %s }" (pretty_row "; " Config.Printing.type_annotation_sep row)
            | Te_Variant row           -> sprintf "< %s >" (pretty_row " | " Config.Printing.type_annotation_sep row)
            | Te_HTuple ([] | [_])     -> unexpected "empty or unary tupled type expression" __SOURCE_FILE__ __LINE__
            | Te_HTuple es             -> sprintf "(%s)" (flatten_stringables ", " es)

            // arrow must be matched BEFORE app 
            | Te_Arrow (ULo (Te_Arrow _ as t1), t2) -> sprintf "(%O) -> %Os" t1 t2
            | Te_Arrow (t1, t2)               -> sprintf "%O -> %O" t1 t2

            | Te_App (App s)           -> s
            | Te_Lambda (kpar, τ)      -> sprintf "fun %s -> %O" (pretty_param Config.Printing.kind_annotation_sep kpar) τ
            | Te_Annot (e, ty)         -> sprintf "(%O : %O)" e ty
            | Te_Let (d, e)            -> sprintf "let %O in %O" d e
            | Te_Match (e, cases)      -> sprintf "match %O with\n| %s" e (pretty_cases cases)
            | Te_Row (bs, o)           -> sprintf "(| %s |)" (pretty_row " | " Config.Printing.type_annotation_sep (bs, o))
            | Te_Forall ((x, ko), τ2)  -> sprintf "forall %s. %O" (pretty_param Config.Printing.kind_annotation_sep (var.fresh_named x, ko)) τ2

type fxty_uexpr with
    override this.ToString () = this.pretty

    member this.pretty =
        match this with
            | Fxe_Bottom -> Config.Printing.dynamic.bottom
            | Fxe_F_Ty τ -> τ.pretty
            | Fxe_Forall (((x, ko), None), τ2)    -> sprintf "forall %s. %O" (pretty_param Config.Printing.kind_annotation_sep (var.fresh_named x, ko)) τ2
            | Fxe_Forall (((x, ko), Some τ1), τ2) -> sprintf "forall (%s >= %O). %O" (pretty_param Config.Printing.kind_annotation_sep (var.fresh_named x, ko)) τ1 τ2

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

type [< NoComparison; RequireQualifiedAccess >] lit =
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
    | P_Var of ident
    | P_Cons of ident
    | P_PolyCons of ident
    | P_App of (patt * patt)
    | P_Lit of lit
    | P_Annot of patt * ty_expr
    | P_As of patt * ident
    | P_Wildcard
    | P_Or of patt * patt
    | P_And of patt * patt
    | P_Record of (ident * patt) list

and [< NoComparison; NoEquality >] patt = node<upatt, unit>

let P_Apps, (|P_Apps1|), (|P_Apps|_|) = nodify make_apps_by P_App (function P_App (τ1, τ2) -> Some (τ1, τ2) | _ -> None)

let P_Tuple = Row_based_Tuple (fun (bs, _) -> P_Record bs)
let (|P_Tuple|_|) = (|Row_based_Tuple|_|) (function P_Record bs -> Some (bs, None) | _ -> None)

let P_ConsApps (x, ps) = P_Apps (ULo (P_Cons x) :: ps)
let (|P_ConsApps1|_|) = function
    | P_Apps1 (ULo (P_Cons x) :: ts) -> Some (x, ts)
    | _ -> None

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
    | Var of ident
//    | Reserved_Cons of id    // internal only
    | FreeVar of ident
    | PolyCons of ident
    | Loosen of expr
    | Record of (ident * expr) list * expr option
    | Lambda of typed_param * expr
    | If of expr * expr * expr
    | App of (expr * expr)
    | Let of decl * expr
    | Match of expr * expr_case list
    | Select of expr * ident
    | Restrict of expr * ident
    | Annot of expr * ty_expr
    | Combine of expr list
    | Val of expr
    | Solve of expr * ty_expr
    | Inject of expr
    | Eject of expr
with
    interface annotable with
        member __.annot_sep = Config.Printing.type_annotation_sep
 
and binding = qbinding<decl_qual, upatt, uexpr, unit>
and rec_binding = rec_qbinding<decl_qual, ty_expr, uexpr, unit>
and overload_binding = signature_binding<ty_uexpr, kind>
and [< NoComparison; NoEquality >] datatype_binding = { id : ident; kind : kind; datacons : signature_binding<ty_uexpr, kind> list }

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

let Tuple = Row_based_Tuple Record
let (|Tuple|_|) = (|Row_based_Tuple|_|) (function Record (bs, o) -> Some (bs, o) | _ -> None)

let UnApp (op, e : expr) = App (Lo e.loc <| Id op, e)
let BinApp (e1 : expr, op, e2 : expr) = App (Lo e1.loc <| App (Lo e2.loc <| Id op, e1), e2)

//let EApps es = (Apps (fun (e1, e2) -> Lo e1.loc <| App (e1, e2)) es).value
let Apps, (|Apps1|), (|Apps|_|) = nodify make_apps_by App (function App (τ1, τ2) -> Some (τ1, τ2) | _ -> None)

module N = Config.Typing.Names

let List_Nil = Var N.Data.list_nil
let List_Cons (e1, e2) = Apps [ULo (Var N.Data.list_cons); e1; e2]
let List_Seq (es : expr list) = List.foldBack (fun e z -> List_Cons (e, Lo e.loc z)) es List_Nil

let (|List_Cons|_|) = function
    | Apps [ULo (Var s); e1; e2] when s = N.Data.list_cons -> Some (e1, e2)
    | _ -> None
let (|List_Nil|_|) = function
    | Var s when s = N.Data.list_nil -> Some ()
    | _ -> None

let P_List_Nil = P_Cons N.Data.list_nil
let P_List_Cons (p1, p2) = P_Apps [ULo (P_Cons N.Data.list_cons); p1; p2]
let P_List_Seq (ps : patt list) = List.foldBack (fun p z -> P_List_Cons (p, Lo p.loc z)) ps P_List_Nil


type uexpr with
    override this.ToString () = this.pretty

    member this.pretty =
        let (|A|) =
            let (|R|_|) = function
                | (ULo (Lit _ | Var _ | FreeVar _ | (*Reserved_Cons _ |*) Record _ | Select _)) as e -> Some e
                | _ -> None
            let (|L|_|) = function
                | ULo (App _) | R _ as e -> Some e
                | _ -> None
            in
                (|Application|) (|L|_|) (|R|_|)
        let (|Sym|_|) = (|Sym|_|) (function Var x | FreeVar x -> Some (x, x) | _ -> None)
        let rec (|List|_|) = function
            | List_Nil -> Some []
            | List_Cons (e1, ULo (List e2)) -> Some (e1 :: e2)
            | _ -> None
        match this with
            | Lit l                 -> l.pretty
            | List es               -> sprintf "[%s]" (flatten_stringables "; " es)
            | List_Cons (e1, e2)    -> sprintf "%O :: %O" e1 e2
            | Sym x                 -> sprintf "(%s)" x
            | Var x                 -> sprintf "%s" x
//            | Reserved_Cons x       -> x
            | FreeVar x             -> sprintf Config.Printing.freevar_fmt x
            | PolyCons x            -> sprintf Config.Printing.polycons_fmt x
            | App (A s)             -> s
            | Lambda (tpar, e)      -> sprintf "fun %s -> %O" (pretty_param Config.Printing.type_annotation_sep tpar) e
            | Select (e, id)        -> sprintf "%O.%s" e id
            | Restrict (e, id)      -> sprintf "%O \\ %s" e id
            | If (e1, e2, e3)       -> sprintf "if %O then %O else %O" e1 e2 e3
            | Annot (e, τ)          -> sprintf "%O : %O" e τ
            | Let (d, e)            -> sprintf "%O in %O" d e
            | Match (e, cases)      -> sprintf "match %O with\n| %s" e (pretty_cases cases)
            | Tuple ([] | [_])      -> unexpected "empty or unary tuple expression" __SOURCE_FILE__ __LINE__ this
            | Tuple es              -> sprintf "(%s)" (flatten_stringables ", " es)
            | Combine es            -> flatten_stringables "; " es
            | Val e                 -> sprintf "val %O" e
            | Solve (e, τ)          -> sprintf "%O where %O" e τ
            | Record (bs, None)     -> sprintf "{ %s }" (mappen_strings (fun (x, e) -> sprintf "%s = %O" x e) "; " bs)
            | Record (bs, Some e)   -> sprintf "{ %s | %O }" (mappen_strings (fun (x, e) -> sprintf "%s = %O" x e) "; " bs) e
            | Inject e              -> sprintf "\\_ %O" e
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
  { namespacee : ident option
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
    
    
// additional sugars
//

// TODOL: polish these functions in such a way that they return always a uexpr and always arguments pick exprs
let lambda_function lambda matchh id (cases : case<_, _, _> list) =
    let loc = let p, _, _ = cases.[0] in p.loc
    let L = Lo loc
    let x = fresh_reserved_id ()
    in
        L <| lambda ((x, None), (L <| matchh (L <| id x, cases)))

let LambdaFunction = lambda_function Lambda Match Id
let Te_LambdaFunction = lambda_function Te_Lambda Te_Match Te_Cons

let lambda_fun (|P_Annot|_|) (|P_Tuple|_|) (|P_Var|_|) (|P_Wildcard|_|) (|P_Custom|_|) lambda lambda_function = function
    | [], _ -> unexpected "empty lambda parameter list" __SOURCE_FILE__ __LINE__
    | ps, e ->
        List.foldBack (fun (p : node<_, _>) (e : node<_, _>) ->
                let loc = p.loc
                let rec f = function
                    | P_Annot (ULo (P_Var x), t) -> Lo loc <| lambda ((x, Some t), e)
                    | P_Tuple ([_] | [])         -> unexpected "empty or unary tuple pattern" __SOURCE_FILE__ __LINE__
                    | P_Var x                    -> Lo loc <| lambda ((x, None), e)
                    | P_Wildcard                 -> Lo loc <| lambda ((fresh_reserved_id (), None), e)
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
        | P_Lit lit.Unit -> Some (Lambda ((fresh_reserved_id (), Some (Lo p.loc Te_Unit)), e))
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
                raise (syntax_error (sprintf "number of function parameters expected to be %d across all cases" len0, p0.loc))
        let ids = List.init len0 (fun _ -> fresh_reserved_id ())
        let pars f = List.mapi (fun i (p : node<_, _>) -> Lo p.loc <| f ids.[i]) ps0
        let cases = List.map (fun (ps, weo, e) -> L0 <| p_tuple ps, weo, e) cases
        in
            lambdafun (pars p_var, L0 <| matchh (L0 <| tuple (pars var), cases))

    | l -> unexpected "ill-formed lambda case list: %O" __SOURCE_FILE__ __LINE__ l
    
let LambdaCases x = lambda_cases LambdaFun P_Var Id Match Tuple P_Tuple x
let Te_LambdaCases x = lambda_cases Te_LambdaFun Tp_Var Te_Cons Te_Match Te_Tuple Tp_Tuple  x
            
let RecLambda ((x, t), cases) =
    let e = LambdaCases cases
    let L x = Lo (let _, _, e = cases.[0] in e.loc) x
    in
        L <| Let (L <| D_Rec [{ qual = decl_qual.none; par = (x, t); expr = e }], L <| Id x)

let lets lett (ds, e) = List.foldBack (fun d e -> Lo e.loc <| lett (d, e)) ds e

let Lets x = lets Let x
let Te_Lets x = lets Te_Let x




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
