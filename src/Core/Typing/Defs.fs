(*
 * Lw
 * Typing/Defs.fs: type system definition
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Defs

#nowarn "60"

open System
open System.Collections.Generic
open System.Diagnostics
open FSharp.Common
open FSharp.Common.Log
open Lw.Core
open Lw.Core.Globals
open Lw.Core.Absyn
open Lw.Core.Absyn.Misc
open Lw.Core.Absyn.Var
open Lw.Core.Absyn.Kind
open Lw.Core.Absyn.Sugar
open Lw.Core.Absyn.Ast


// kinding environments, types and related stuff
//

type [< NoComparison; NoEquality >] kscheme = { forall : Set<var>; kind : kind }
with
    static member binding_separator = "::"

// kind judice environment for type constructors
type kjenv = Env.t<ident, kscheme>

// kind judice environment for type variables
type vakjenv = Env.t<ident, kind>

type kinded =
    abstract kind : kind


// System-F types

type [< NoComparison; NoEquality; DebuggerDisplay("{ToString()}") >] ty =
    | T_Cons of ident * kind
    | T_Var of var * kind    
    | T_HTuple of ty list   // TODOL: try to design a more general Rowed type which does not expect star on fields, and encode htuples with it
    | T_App of (ty * ty)
    | T_Forall of var * ty
    | T_Closure of ident * tenv ref * ty_expr * kind
with
    static member binding_separator = Config.Printing.type_annotation_sep

    member this.kind = (this :> kinded).kind

    interface kinded with
        member this.kind =
            match this with
            | T_Cons (_, k)
            | T_Var (_, k)
            | T_Closure (_, _, _, k) -> k
            | T_HTuple ts            -> K_HTuple [for t in ts do yield t.kind]
            | T_Forall (_, t)        -> t.kind
            | T_App (t1, _)          -> match t1.kind with
                                        | K_Arrow (_, k) -> k
                                        | k              -> unexpected "non-arrow kind %O in left hand of type application: %O" __SOURCE_FILE__ __LINE__ k this


// evaluated types environment (namely δ, analogous to the value environment Δ)
and tenv = Env.t<ident, ty>


// flexible types

type [< NoComparison; NoEquality; DebuggerDisplay("{ToString()}") >] fxty =
    | Fx_Forall of (var * fxty) * fxty
    | Fx_Bottom of kind
    | Fx_F_Ty of ty
with
    static member binding_separator = Config.Printing.type_annotation_sep
    static member reduction_separator = Config.Printing.ftype_instance_of_fxty_sep

    member this.kind = (this :> kinded).kind

    interface kinded with
        member this.kind =
            match this with
            | Fx_Bottom k             -> k
            | Fx_Forall (_, ϕ)        -> ϕ.kind
            | Fx_F_Ty t               -> t.kind


// constraints for overloading
//

type constraint_mode = Cm_FreeVar | Cm_OpenWorldOverload | Cm_ClosedWorldOverload
with
    member this.pretty_as_constraint_id x =
        match this with
        | Cm_OpenWorldOverload      -> sprintf Config.Printing.openworld_overload_constraint_fmt x
        | Cm_ClosedWorldOverload    -> sprintf Config.Printing.closedworld_overload_constraint_fmt x
        | Cm_FreeVar                -> sprintf Config.Printing.freevar_constraint_fmt x

type [< CustomEquality; CustomComparison; DebuggerDisplay("{ToString()}") >] constraintt =
    {
        name    : ident
        num     : int
        mode    : constraint_mode
        strict  : bool
        ty      : ty
    }
with
    override x.Equals yobj =
        match yobj with
        | :? constraintt as y -> x.num = y.num
        | _ -> false
 
    override x.GetHashCode () = hash x.num
 
    interface System.IComparable with
      member x.CompareTo yobj =
          match yobj with
          | :? constraintt as y -> compare x.num y.num
          | _                   -> invalidArg "yobj" "cannot compare values of different types"

    static member fresh_strict cm name t = { name = name; num = fresh_int (); mode = cm; strict = true; ty = t }
    
    override this.ToString () = this.pretty

    member this.pretty_as_translated_id = sprintf Config.Printing.constraint_id_fmt this.name this.num

    member this.pretty =
        let sep = if this.strict then Config.Printing.type_annotation_sep else ":>"
        let id =
            let id = this.mode.pretty_as_constraint_id this.name
            in
                #if DEBUG_CONSTRAINTS
                sprintf Config.Printing.cid_fmt id this.num
                #else
                id
                #endif
        in
            sprintf "%s %s %O" id sep this.ty


type constraints (set : Set<constraintt>) =

    interface IEnumerable<constraintt> with
        member __.GetEnumerator () = (set :> IEnumerable<_>).GetEnumerator ()

    interface Collections.IEnumerable with
        member this.GetEnumerator () = (this :> IEnumerable<_>).GetEnumerator () :> Collections.IEnumerator

    member __.is_empty = set.IsEmpty
    member __.map f = new constraints (Set.map f set)
    member __.fold f z = Set.fold f z set
    member __.exists p = Set.exists p set
    member __.forall p = Set.forall p set

    member private __.set = set

    member __.add c = new constraints (Set.add c set)
    member __.remove c = new constraints (Set.remove c set)

    member __.toList = Set.toList set

    static member (+) (cs1 : constraints, cs2 : constraints) = new constraints (cs1.set + cs2.set)
    static member (-) (cs1 : constraints, cs2 : constraints) = new constraints (cs1.set - cs2.set)

    member __.pretty = if set.IsEmpty then "{}" else sprintf "{ %s }" (flatten_stringables "; " set)
    override this.ToString () = this.pretty

    static member empty = new constraints (Set.empty)

[< CompilationRepresentationAttribute(CompilationRepresentationFlags.ModuleSuffix) >]
module constraints =
    let B = new Computation.Builder.itemized_collection<_, _> (empty = constraints.empty, plus1 = (fun c (cs : constraints) -> cs.add c), plus = (+))



// type schemes, prefix and typing environments
//
    
type [< NoComparison; NoEquality; DebuggerDisplay("{ToString()}") >] tscheme =
    {
//        type_constraints : type_constraints
        constraints      : constraints
        fxty             : fxty
    }

[< RequireQualifiedAccess >]
type jenv_key =
        | Data of ident
        | Inst of ident * int
        | Var of ident
with
    override this.ToString () = this.pretty

    member this.pretty =
        match this with
            | jenv_key.Var x       -> x
            | jenv_key.Data x      -> sprintf "data %s" x
            | jenv_key.Inst (x, n) -> sprintf Config.Printing.jk_inst_fmt x n 

    member this.pretty_as_translated_id =
        match this with
            | jenv_key.Var x       
            | jenv_key.Data x      -> x
            | jenv_key.Inst (x, n) -> sprintf Config.Printing.jk_inst_fmt x n 

[< RequireQualifiedAccess >]
type [< NoComparison; NoEquality >] jenv_mode =
    | Overload
    | Normal

type [< NoComparison; NoEquality >] jenv_value =
    {
        mode    : jenv_mode
        scheme  : tscheme
    }
with
    override this.ToString () = this.pretty
            
    member this.pretty =        
        match this.mode with
        | jenv_mode.Overload -> sprintf "<overload> %O" this.scheme
        | jenv_mode.Normal   -> sprintf "%O" this.scheme

type jenv = Env.t<jenv_key, jenv_value>

type [< NoComparison; NoEquality; DebuggerDisplay("{ToString()}") >] prefix =
    | Q_Nil
    | Q_Cons of prefix * (var * fxty)

    interface IEnumerable<var * fxty> with
        member this.GetEnumerator () = this.toSeq.GetEnumerator ()

    interface Collections.IEnumerable with
        member this.GetEnumerator () = (this :> IEnumerable<_>).GetEnumerator () :> Collections.IEnumerator   

    member this.toSeq =
        let rec R Q =
          seq {
            match Q with
            | Q_Nil         -> ()
            | Q_Cons (Q, i) -> yield! R Q; yield i }
        in
            R this

    member Q.is_empty = match Q with Q_Nil -> true | _ -> false

    member Q.dom = Computation.B.set { for α, _ in Q do yield α }

    member Q.is_disjoint (Q' : prefix) = (Set.intersect Q.dom Q'.dom).IsEmpty

    static member pretty_item = function
        | α, Fx_Bottom K_Star        -> sprintf "%O" α
        | α, Fx_Bottom k             -> sprintf "(%O :: %O)" α k
        | α, t when t.kind.is_star   -> sprintf "(%O %s %O)" α Config.Printing.var_bound_sep t
        | α, t                       -> sprintf "((%O :: %O) %s %O)" α t.kind Config.Printing.var_bound_sep t

    static member pretty_as_prefix Q = mappen_strings_or_nothing prefix.pretty_item Config.Printing.empty_prefix Config.Printing.forall_prefix_sep Q
    member Q.pretty = prefix.pretty_as_prefix Q
    override this.ToString () = this.pretty

    member this.fold f z =
        match this with
        | Q_Nil         -> z
        | Q_Cons (Q, i) -> f (Q.fold f z) i
    
    member Q.insert i =
        let rec R = function
            | Q_Nil          -> Q_Cons (Q_Nil, i)
            | Q_Cons (Q, i') -> Q_Cons (R Q, i')
        in
            R Q

    static member (+) (Q : prefix, (α, t : fxty)) = Q_Cons (Q, (α, t))
    static member (+) (Q1 : prefix, Q2 : prefix) = Q2.fold (fun (Q : prefix) (α, t) -> Q + (α, t)) Q1


[< CompilationRepresentationAttribute(CompilationRepresentationFlags.ModuleSuffix) >]
module prefix =
    let B = new Computation.Builder.itemized_collection<_, _> (empty = Q_Nil, plus1 = (fun i Q -> Q + i), plus = fun Q1 Q2 -> Q1 + Q2)
    let ofSeq sq = B { for α, t in sq do yield α, t }
    let of_bottoms αks = B { for α, k in αks do yield α, Fx_Bottom k }



// contexts for off-monad data
//

type resolution = Res_Strict | Res_Loose | Res_No

type [< NoComparison; NoEquality >] context =
    { 
        nesting   : int
        resolution      : resolution
    }
with
    static member as_top_level_decl = {
        nesting   = 0
        resolution      = Res_Strict
    }

    member this.nest = { this with nesting = this.nesting + 1 } // HACK: re-enable this and fix what's wrong with top level generalization

    member this.is_top_level = this.nesting < 1

type scoped_var = {
    var     : var
    nesting : int
}
with
    override this.ToString () = this.pretty

    member this.pretty = sprintf "%O (nesting level %d)" this.var this.nesting

    member this.name =
        match this.var with
        | Va (_, Some s) -> s
        | _ -> unexpected_case __SOURCE_FILE__ __LINE__ this

type scoped_vars = Env.t<ident, scoped_var>

type [< NoComparison; NoEquality >] uni_context =
    { 
        loc            : location
        γ              : kjenv
        Γ              : jenv
        scoped_vars    : scoped_vars
    }



// type shortcuts and augmentations
//

let private T_Primitive name = T_Cons (name, K_Star)
let private (|T_Primitive|_|) name = function
    | T_Cons (s, K_Star) when name = s -> Some ()
    | _                                -> None

module N = Config.Typing.Names
    
let (|T_Bool|_|) = (|T_Primitive|_|) N.Type.bool
let (|T_Unit|_|) = (|T_Primitive|_|) N.Type.unit
let (|T_Int|_|) = (|T_Primitive|_|) N.Type.int
let (|T_Float|_|) = (|T_Primitive|_|) N.Type.float
let (|T_String|_|) = (|T_Primitive|_|) N.Type.string
let (|T_Char|_|) = (|T_Primitive|_|) N.Type.char

let T_Bool = T_Primitive N.Type.bool
let T_Unit = T_Primitive N.Type.unit
let T_Int = T_Primitive N.Type.int
let T_Float = T_Primitive N.Type.float
let T_String = T_Primitive N.Type.string
let T_Char = T_Primitive N.Type.char

let T_Star_Var α = T_Var (α, K_Star)
let (|T_Star_Var|_|) = function
    | T_Var (α, K_Star) -> Some α
    | _ -> None

let (|T_NamedVar|_|) = function
    | T_Var (Va (_, Some _) as α, k) -> Some (α, k)
    | _ -> None

let T_Apps, (|T_Apps1|), (|T_Apps|_|) = make_apps (fun (τ1, τ2) -> T_App (τ1, τ2)) (function T_App (τ1, τ2) -> Some (τ1, τ2) | _ -> None)
let T_Arrow, (|T_Arrow|_|) = make_arrow_by_apps (T_Cons (N.Type.arrow, K_Arrows [K_Star; K_Star; K_Star])) T_Apps (function T_Cons (x, _) when x = N.Type.arrow -> Some () | _ -> None) (|T_Apps|_|)
let T_Arrows, (|T_Arrows1|), (|T_Arrows|_|) = make_arrows T_Arrow (|T_Arrow|_|)
let T_Foralls, (|T_Foralls0|), (|T_Foralls|_|) = make_foralls T_Forall (function T_Forall (α, t) -> Some (α, t) | _ -> None)
let Fx_Foralls, (|Fx_Foralls0|), (|Fx_Foralls|_|) = make_foralls Fx_Forall (function Fx_Forall (αt, t) -> Some (αt, t) | _ -> None)

let T_ConsApps ((x, k), ts) = T_Apps (T_Cons (x, k) :: ts)
let (|T_ConsApps1|_|) t =
    match t with
    | T_Apps1 (T_Cons (x, k) :: ts) -> Some ((x, k), ts)
    | _ -> None

let T_Row_Var ρ = T_Var (ρ, K_Row)

let K_Row_Ext = K_Arrows [K_Star; K_Row; K_Row]
let (|K_Row_Ext|_|) = function
    | K_Arrows [K_Star; K_Row; K_Row] -> Some ()
    | _ -> None

let T_Row_Empty = T_Cons (string N.Type.Row.special_prefix, K_Row)
let T_Row_Ext (l, t, ρ) = T_Apps [T_Cons (sprintf "%c%s" N.Type.Row.special_prefix l, K_Row_Ext); t; ρ]

let (|T_Row_Empty|T_Row_Ext|T_Row_Var|T_NoRow|) = function
    | T_Var (ρ, K_Row) -> T_Row_Var ρ

    | T_Cons (s, K_Row) when s = string N.Type.Row.special_prefix ->
        T_Row_Empty

    | T_Apps [T_Cons (s, K_Row_Ext); t; ρ] when s.Length > 1 && s.[0] = N.Type.Row.special_prefix ->
        T_Row_Ext (s.TrimStart [|N.Type.Row.special_prefix|], t, ρ)

    | t -> T_NoRow t

let T_Row (r, ρo) = List.foldBack (fun (l, t) ρ -> T_Row_Ext (l, t, ρ)) r (match ρo with Some ρ -> T_Row_Var ρ | None -> T_Row_Empty)
let (|T_Row|_|) = function
    | T_NoRow _ -> None
    | t ->
        let rec R = function
            | T_Row_Ext (l, t, r) -> let bs, o = R r in (l, t) :: bs, o
            | T_Row_Empty         -> [], None
            | T_Row_Var ρ         -> [], Some ρ
            | T_NoRow t'          -> unexpected "ill-formed row type %A having nested non-row type %A" __SOURCE_FILE__ __LINE__ t t'
        in
            Some (R t)

let T_Record, T_Variant, T_Tuple, (|T_Record|_|), (|T_Variant|_|), (|T_Tuple|_|) =
    let T_Rowed name r = T_App (T_Cons (name, K_Arrow (K_Row, K_Star)), T_Row r)
    let (|T_Rowed|_|) name = function
        | T_App (T_Cons (name', K_Arrow (K_Row, K_Star)), T_Row r) when name = name' -> Some r
        | _ -> None
    in
        make_rows T_Rowed (|T_Rowed|_|)

let T_Open_Record xts = T_Record (xts, Some var.fresh)
let T_Closed_Record xts = T_Record (xts, None)
let T_Open_Variant xts = T_Variant (xts, Some var.fresh)
let T_Closed_Variant xts = T_Variant (xts, None)


// augmentations for kinds and kind schemes
//

type kind with
    member this.fv =     
        match this with
            | K_Var α          -> Set.singleton α
            | K_Cons (_, ks)   -> List.fold (fun set (k : kind) -> set + k.fv) Set.empty ks

type kscheme with
    override this.ToString () = this.pretty

    member kσ.pretty =
        match kσ with
            | { forall = αs; kind = k } ->
                use A = var.add_quantifieds αs
                let αspart = if αs.IsEmpty then "" else sprintf "%s %s. " Config.Printing.dynamic.forall (flatten_stringables Config.Printing.forall_prefix_sep αs)
                in
                    sprintf "%s%O" αspart k

    member this.fv =
        match this with
            | { forall = αs; kind = k } -> k.fv - αs
       


// augmentations for types and schemes
//

type ty with
    // TODO: these should be forbidden and turned into methods of the main monad
    [< Obsolete >]
    static member fresh_var k = T_Var (var.fresh, k)
    [< Obsolete >]
    static member fresh_var_and_ty k = let α = var.fresh in α, T_Var (α, k)
    [< Obsolete >]
    static member fresh_star_var = ty.fresh_var K_Star
    [< Obsolete >]
    static member fresh_star_var_and_ty = ty.fresh_var_and_ty K_Star

    member this.ftv =
        Env.t.B {
            match this with
            | T_Var (α, k)              -> yield (α, k) 
            | T_Closure (_, _, _, k)   
            | T_Cons (_, k)             -> ()
            | T_HTuple ts               -> for t in ts do yield! t.ftv
            | T_App (t1, t2)            -> yield! t1.ftv; yield! t2.ftv
            | T_Forall (α, t)           -> yield! t.ftv.remove α
        }

    member this.fv = Computation.B.set { for α, k in this.ftv do yield α; yield! k.fv }    


let T_Bottom k =
    let α, tα = ty.fresh_var_and_ty k
    in
        T_Forall (α, tα)

let T_ForallK ((α, _), t) = T_Forall (α, t)
let (|T_ForallK|_|) t =
    match t with
    | T_Forall (α, t) ->
        let k =
            match Seq.tryFind (fst >> (=) α) t.ftv with
            | Some (_, k) -> k
            | None        -> kind.fresh_var
        in
            Some ((α, k), t)

    | _ -> None

let T_ForallsK, (|T_ForallsK0|), (|T_ForallsK|_|) = make_foralls T_ForallK (|T_ForallK|_|)
   
let pretty_kinded_wrapper R' t =
    let R t =
        let k = (t :> kinded).kind
        in
            match k with
            | K_Arrows1 ks when List.forall (fun (k : kind) -> k.is_star) ks -> R' t
            | _                                                              -> sprintf "(%s :: %O)" (R' t) k
    in
        R t

let pretty_forall pretty_item forall (qs, t) =
    use A = var.add_quantifieds (Seq.map fst qs)
    let t = sprintf "%O" t  // pretty the body first, so var names will appear normalized in order from left to right; then prefix is sorted
    let ts =
        qs
        #if !DEBUG_VAR_NAMES
        |> Seq.sortBy (fst >> sprintf "%O")
        #endif
        |> mappen_strings pretty_item Config.Printing.forall_prefix_sep
    in
        sprintf "%s %s. %s" forall ts t

type ty with
    override this.ToString () = this.pretty    
    member this.pretty =
        let (|T_Sym_Cons|_|) = (|Sym|_|) (function T_Cons (x, k) -> Some (x, (x, k)) | _ -> None)
        let (|A|_|) = function
            | T_Tuple _ -> None // tuples are encoded using row types with integer labels, so they must be matched before generic row types
            | T_Var _ | T_Record _ | T_Variant _ | T_Cons _ | T_Closure _ | T_Row _ as e -> Some e
            | _ -> None
        let (|App|) = (|Application|) (function T_App (t1, t2) -> Some (t1, t2) | _ -> None) (|A|_|)
        let rec (|LArrow|_|) = function
            | T_Forall (_, LArrow _)
            | T_Arrow _ as e -> Some e
            | _ -> None
        let rec R' = function
            | T_Var (α, _)            -> sprintf "%O" α
            | T_Tuple ([] | [_]) as t -> unexpected "empty or unary tuple: %O" __SOURCE_FILE__ __LINE__ t
            | T_Tuple ts              -> mappen_strings (fun t -> (match t with A _ -> sprintf "%s" | _ -> sprintf "(%s)") (R t))  " * " ts
            | T_Record row            -> sprintf "{ %s }" (pretty_row "; " Config.Printing.type_annotation_sep row)
            | T_Variant row           -> sprintf "< %s >" (pretty_row " | " Config.Printing.type_annotation_sep row)
            | T_Row row               -> sprintf "(| %s |)" (pretty_row " | " Config.Printing.type_annotation_sep row)

            | T_HTuple ([] | [_]) as t -> unexpected "empty or unary htuple: %O" __SOURCE_FILE__ __LINE__ t
            | T_HTuple ts              -> mappen_strings (fun t -> (match t with A _ -> sprintf "%s" | _ -> sprintf "(%s)") (R t))  ", " ts

            | T_Sym_Cons (x, __)      -> sprintf "(%s)" x
            | T_Cons (x, _)           -> x

            | T_Arrow (LArrow _ as t1, t2) -> sprintf "(%s) -> %s" (R t1) (R t2)
            | T_Arrow (t1, t2)             -> sprintf "%s -> %s" (R t1) (R t2)

            | T_App (App s)           -> s
            | T_Closure (x, _, τ, _)  -> sprintf "<[%O]>" (Te_Lambda ((x, None), τ))

            | T_ForallsK arg          -> pretty_forall (sprintf "%O" << T_Var) Config.Printing.dynamic.forall arg
            | T_Forall _ as t         -> unexpected_case __SOURCE_FILE__ __LINE__ t
        and R = pretty_kinded_wrapper R'
        in
            R this

    // an F-type is monomorphic when no quantification occurs at any level
    member this.is_monomorphic =
        match this with
        | T_Forall _        -> false
        | T_Var _
        | T_Cons _             
        | T_Closure _       -> true
        | T_App (t1, t2)    -> t1.is_monomorphic && t2.is_monomorphic
        | T_HTuple ts       -> List.fold (fun r (t : ty) -> r && t.is_monomorphic) true ts

    member private t.search p =
        let l ts = List.tryPick (fun (t : ty) -> t.search p) ts
        match t with
        | (T_Cons _
        | T_Var _ as t)
        | T_Forall (_, t)   -> l [t]
        | T_App (t1, t2)    -> l [t1; t2]
        | T_HTuple ts       -> l ts
        | T_Closure _       -> None

    member t.return_ty =
        match t with
        | T_Forall (_, t) -> t.return_ty
        | T_Arrows ts     -> List.last ts
        | _               -> t

    // an F-type is unquantified when no forall occurs at top-level
    member t.is_unquantified =
        match t with
        | T_Forall _ -> false
        | _          -> true


// active patterns for dealing with quantification, instantiation etc. 

let Fx_ForallsQ (Q : prefix, ϕ : fxty) = Fx_Foralls (Seq.toList Q, ϕ)
let FxU_ForallsQ (Q, t : ty) = Fx_ForallsQ (Q, Fx_F_Ty t)

// all outer quantified vars are taken, both from the flex type and from possible F-type quantifiers, hence right hand is granted unquantified
let (|FxU_ForallsQ|FxU_Unquantified|FxU_Bottom|) = function
    | Fx_Foralls (qs, Fx_F_Ty (T_ForallsK (αks, t))) -> assert t.is_unquantified; FxU_ForallsQ (prefix.ofSeq qs + prefix.of_bottoms αks, t)
    | Fx_Foralls (qs, Fx_F_Ty t)                     -> assert t.is_unquantified; FxU_ForallsQ (prefix.ofSeq qs, t)
    | Fx_F_Ty (T_ForallsK (αks, t))                  -> assert t.is_unquantified; FxU_ForallsQ (prefix.of_bottoms αks, t)
    | Fx_F_Ty t                                      -> assert t.is_unquantified; FxU_Unquantified t
    | Fx_Bottom k                                    -> FxU_Bottom k
    | Fx_Forall _ as ϕ                               -> unexpected_case __SOURCE_FILE__ __LINE__ ϕ

// reduced form of the active pattern above where the ForallsQ case supports also empty prefixes
let (|FxU0_ForallsQ|FxU0_Bottom|) = function
    | FxU_ForallsQ (Q, t) -> FxU0_ForallsQ (Q, t)
    | FxU_Unquantified t  -> FxU0_ForallsQ (Q_Nil, t)
    | FxU_Bottom k        -> FxU0_Bottom k

type fxty with
    override this.ToString () = this.pretty    
    member this.pretty =
        let rec R' = function
            | Fx_Bottom _      -> Config.Printing.dynamic.bottom
            | Fx_F_Ty t        -> t.pretty
            | Fx_Foralls arg   -> pretty_forall prefix.pretty_item Config.Printing.dynamic.flex_forall arg
            | Fx_Forall _ as ϕ -> unexpected_case __SOURCE_FILE__ __LINE__ ϕ
        and R = function
            | Fx_F_Ty _ as ϕ -> R' ϕ    // prevents double wrapping of an F-type
            | ϕ              -> pretty_kinded_wrapper R' ϕ
        in
            R this

    member this.ftv =
        match this with
        | Fx_F_Ty t               -> t.ftv
        | Fx_Bottom _             -> Env.empty
        | Fx_Forall ((α, ϕ1), ϕ2) -> let r2 = ϕ2.ftv in if r2.contains_key α then ϕ1.ftv + r2.remove α else r2

    member this.fv =
        match this with
        | Fx_Bottom k             -> k.fv
        | Fx_Forall ((α, ϕ1), ϕ2) -> let r2 = ϕ2.fv in if Set.contains α r2 then ϕ1.fv + (Set.remove α r2) else r2
        | Fx_F_Ty t               -> t.fv

    [< Obsolete >]
    member this.is_monomorphic =
        match this with
        | Fx_Bottom _
        | Fx_Forall _ -> false
        | Fx_F_Ty t   -> t.is_monomorphic



type tscheme with    
    override this.ToString () = this.pretty

    member σ.pretty =
        let { constraints = cs; fxty = Fx_Foralls0 (qs, ϕ1) } = σ
        // TODO: deal with variables in the constraints and choose how to show them, either detecting the outer-most foralls or something like that
        let αs = Computation.B.set { for α, _ in qs do yield α }
        let αspart = if αs.IsEmpty then "" else sprintf "%s %s. " Config.Printing.dynamic.forall (flatten_stringables Config.Printing.forall_prefix_sep αs)
        let cspart = if cs.is_empty then "" else sprintf "{ %O } => " cs
        in
            sprintf "%s%s%O" αspart cspart ϕ1
                        
    static member binding_separator = ty.binding_separator
