(*
 * Lw
 * Typing/Defs.fs: type system definition
 * (C) 2000-2014 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Defs

#nowarn "60"

open System
open System.Collections.Generic
open System.Diagnostics
open FSharp.Common
open FSharp.Common.Prelude
open FSharp.Common.Log
open Lw.Core
open Lw.Core.Globals
open Lw.Core.Absyn


// types, schemes, constraints, environments, etc.
//

type kscheme = { forall : Set<var>; kind : kind }
with
    static member binding_separator = "::"

type kjenv = Env.t<id, kscheme>

type kconsenv = Env.t<id, var list * kind>

type tenv = Env.t<id, ty>


// System-F types
//

and [< NoComparison; CustomEquality; DebuggerDisplay("{ToString()}") >] ty =
    | T_Cons of id * kind
    | T_Var of var * kind    
    | T_HTuple of ty list   // TODO: try to design a more general Rowed type which does not expect star on fields, and encode htuples with it
    | T_App of (ty * ty)
    | T_Forall of var * ty
    | T_Closure of id * tenv ref * ty_expr * kind
with
    static member binding_separator = Config.Printing.type_annotation_sep

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

    override x.Equals y = CustomCompare.equals_with (fun x y -> (x :> IEquatable<ty>).Equals y) x y

    override this.GetHashCode () =
        match this with
        | T_Cons (x, k)             -> (x, k).GetHashCode ()
        | T_Var (α, k)              -> (α, k).GetHashCode ()
        | T_HTuple ts               -> ts.GetHashCode ()
        | T_App (t1, t2)            -> (t1, t2).GetHashCode ()
        | T_Forall (α, t)           -> (α, t).GetHashCode ()
        | T_Closure (_, _, _, _)    -> unexpected "hashing type closure: %O" __SOURCE_FILE__ __LINE__ this

    interface IEquatable<ty> with
        member x.Equals y =
            x.kind = y.kind
                 && match x, y with
                    | T_Cons (x, _), T_Cons (y, _)          -> x = y
                    | T_Var (α, _), T_Var (β, _)            -> α = β
                    | T_App (t1, t2), T_App (t1', t2')      -> t1 = t1' && t2 = t2'
                    | T_Forall (α, t1), T_Forall (β, t2)    -> α = β && t1 = t2
                    | T_HTuple ts, T_HTuple ts'
                        when ts.Length = ts'.Length         -> List.fold2 (fun b t t' -> b && t = t') true ts ts'
                    | T_Closure _, _
                    | _, T_Closure _                        -> L.unexpected_error "comparing type closures: %O = %O" x y; false
                    | _                                     -> false


// flexible types

type [< NoComparison; CustomEquality; DebuggerDisplay("{ToString()}") >] fxty =
    | Fx_Forall of (var * fxty) * fxty
    | Fx_Bottom of kind
    | Fx_F_Ty of ty
with
    static member binding_separator = Config.Printing.type_annotation_sep
    static member reduction_separator = Config.Printing.ftype_instance_sep

    member this.kind =
        match this with
        | Fx_Bottom k             -> k
        | Fx_Forall (_, ϕ)        -> ϕ.kind
        | Fx_F_Ty t               -> t.kind

    override x.Equals y = CustomCompare.equals_with (fun x y -> (x :> IEquatable<fxty>).Equals y) x y

    override this.GetHashCode () =
        match this with
        | Fx_Bottom k                -> k.GetHashCode ()
        | Fx_Forall ((α, ϕ1), ϕ2)    -> (α, ϕ1, ϕ2).GetHashCode ()
        | Fx_F_Ty t                  -> t.GetHashCode ()

    interface IEquatable<fxty> with
        member x.Equals y =
            x.kind = y.kind
                 && match x, y with
                    | Fx_Forall ((α, t1), t2),
                        Fx_Forall ((α', t1'), t2')  -> α = α' && t1 = t1' && t2 = t2'
                    | Fx_Bottom k1, Fx_Bottom k2    -> k1 = k2
                    | Fx_F_Ty t1, Fx_F_Ty t2        -> t1 = t2
                    | _                             -> false


// pure contexts
//

type resolution = Res_Strict | Res_Loose | Res_No

type [< NoComparison; NoEquality >] context =
    { 
        top_level_decl  : bool
        resolution      : resolution
//        strict          : bool
    }
with
    static member top_level = {
        top_level_decl  = true
        resolution      = Res_Strict
//        strict          = true
    }

type [< NoComparison; NoEquality >] mgu_context =
    { 
        loc            : location
        γ              : kjenv
    }


// overloaded symbol constraints
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
        name    : id
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

    member this.pretty_as_translated_id = sprintf Config.Printing.cid_fmt this.name this.num

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



// GADTs definitions
//

//type uvar = Uv of var
//with
//    override this.ToString () = this.pretty
//
//    member this.pretty =
//        match this with
//            | Uv va -> va.pretty
//
//type [< NoComparison; NoEquality >] type_constraints = 
//    | C_Empty
//    | C_Eq of ty * ty
//    | C_And of type_constraints * type_constraints
//with
//    override this.ToString () = this.pretty
//
//    member this.pretty =
//        match this with
//            | C_Empty        -> ""
//            | C_Eq (t1, t2)  -> sprintf "%O ~ %O" t1 t2
//            | C_And (c1, c2) -> sprintf "%O & %O" c1 c2
//
//    member this.is_empty = match this with C_Empty -> true | _ -> false
//
//type [< NoComparison; NoEquality >] type_impl_constraints =
//    | Ic_Constraint of type_constraints
//    | Ic_Impl of Set<var> * Set<uvar> * type_constraints * type_impl_constraints
//    | Ic_And of type_impl_constraints * type_impl_constraints
//with
//    override this.ToString () = this.pretty
//
//    member this.pretty =
//        match this with
//            | Ic_Constraint c           -> c.pretty
//            | Ic_Impl (αs, bs, c, ic)   -> sprintf "[%s] forall %O. %O => %O" (flatten_stringables " " αs) (flatten_stringables " " bs) c ic
//            | Ic_And (ic1, ic2)         -> sprintf "%O & %O" ic1 ic2
//


// schemes and predicates
//

    
type [< NoComparison; NoEquality; DebuggerDisplay("{ToString()}") >] scheme =
    {
//        type_constraints : type_constraints
        constraints      : constraints
        fxty               : fxty
    }

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

    member Q.dom = Computation.B.set { for α, _ in Q do yield α }

    member Q.is_disjoint (Q' : prefix) = (Set.intersect Q.dom Q'.dom).IsEmpty

    static member pretty_item = function
        | α, Fx_Bottom K_Star        -> sprintf "%O" α
        | α, Fx_Bottom k             -> sprintf "(%O :: %O)" α k
        | α, t when t.kind = K_Star  -> sprintf "(%O %s %O)" α Config.Printing.var_bound_sep t
        | α, t                       -> sprintf "(%O :: %O >= %O)" α t.kind t

    static member pretty_as_prefix Q = mappen_strings_or_nothing prefix.pretty_item Config.Printing.empty_prefix Config.Printing.forall_prefix_sep Q
    member Q.pretty = prefix.pretty_as_prefix Q
    override this.ToString () = this.pretty

    member this.fold f z =
        match this with
        | Q_Nil         -> z
        | Q_Cons (Q, i) -> f (Q.fold f z) i

    static member (+) (Q : prefix, (α, t : fxty)) = Q_Cons (Q, (α, t))
    static member (+) (Q1 : prefix, Q2 : prefix) = Q2.fold (fun (Q : prefix) (α, t) -> Q + (α, t)) Q1


[< CompilationRepresentationAttribute(CompilationRepresentationFlags.ModuleSuffix) >]
module prefix =
    let B = new Computation.Builder.itemized_collection<_, _> (empty = Q_Nil, plus1 = (fun i Q -> Q_Cons (Q, i)), plus = fun Q1 Q2 -> Q1 + Q2)
    let ofSeq sq = B { for α, t in sq do yield α, t }
    let of_bottoms αks = B { for α, k in αks do yield α, Fx_Bottom k }



// type judice environment
//

type jenv_key =
        | Jk_Data of id
        | Jk_Inst of id * int
        | Jk_Var of id
with
    override this.ToString () = this.pretty

    member this.pretty =
        match this with
            | Jk_Var x       -> x
            | Jk_Data x      -> sprintf "data %s" x
            | Jk_Inst (x, n) -> sprintf Config.Printing.jk_inst_fmt x n 

    member this.pretty_as_translated_id =
        match this with
            | Jk_Var x       
            | Jk_Data x      -> x
            | Jk_Inst (x, n) -> sprintf Config.Printing.jk_inst_fmt x n 

type [< NoComparison; NoEquality >] jenv_mode =
    | Jm_Overloadable
    | Jm_Normal
with
    override this.ToString () = this.pretty
            
    member this.pretty =
        match this with
            | Jm_Overloadable -> "(overloadable) "  // TODO: this trailing space is ugly
            | Jm_Normal       -> ""

type [< NoComparison; NoEquality >] jenv_value =
    {
        mode    : jenv_mode
        scheme  : scheme
    }
with
    override this.ToString () = this.pretty
            
    member this.pretty =        
        match this.mode with
        | Jm_Overloadable -> sprintf "(overloadable) %O" this.scheme
        | Jm_Normal       -> sprintf "%O" this.scheme

type jenv = Env.t<jenv_key, jenv_value>


// type shortcuts and augmentations
//

let private T_Primitive name = T_Cons (name, K_Star)
let private (|T_Primitive|_|) name = function
    | T_Cons (s, K_Star) when name = s -> Some ()
    | _                                -> None
    
let (|T_Bool|_|) = (|T_Primitive|_|) "bool"
let (|T_Unit|_|) = (|T_Primitive|_|) "unit"
let (|T_Int|_|) = (|T_Primitive|_|) "int"
let (|T_Float|_|) = (|T_Primitive|_|) "float"
let (|T_String|_|) = (|T_Primitive|_|) "string"
let (|T_Char|_|) = (|T_Primitive|_|) "char"

let T_Bool = T_Primitive "bool"
let T_Unit = T_Primitive "unit"
let T_Int = T_Primitive "int"
let T_Float = T_Primitive "float"
let T_String = T_Primitive "string"
let T_Char = T_Primitive "char"

let T_Star_Var α = T_Var (α, K_Star)
let (|T_Star_Var|_|) = function
    | T_Var (α, K_Star) -> Some α
    | _ -> None

let (|T_NamedVar|_|) = function
    | T_Var (Va (_, Some _) as α, k) -> Some (α, k)
    | _ -> None

let T_Apps = Apps T_App
let (|T_Apps|_|) = (|Apps|_|) (function T_App (t1, t2) -> Some (t1, t2) | _ -> None)

let T_Foralls, (|T_Foralls0|), (|T_Foralls|_|) = make_foralls T_Forall (function T_Forall (α, t) -> Some (α, t) | _ -> None)
let Fx_Foralls, (|Fx_Foralls0|), (|Fx_Foralls|_|) = make_foralls Fx_Forall (function Fx_Forall (αt, t) -> Some (αt, t) | _ -> None)

let T_ConsApps ((x, k), ts) = T_Apps (T_Cons (x, k) :: ts)
let (|T_ConsApps|_|) = function
    | T_Apps (T_Cons (x, k) :: ts) -> Some ((x, k), ts)
    | _ -> None

let T_Arrow_Cons = T_Cons ("->", K_Arrows [K_Star; K_Star; K_Star])
let (|T_Arrow_Cons|_|) = function
    | T_Cons ("->", K_Arrows [K_Star; K_Star; K_Star]) -> Some ()
    | _ -> None

let T_Arrow (t1, t2) = T_Apps [T_Arrow_Cons; t1; t2]
let (|T_Arrow|_|) = function
    | T_Apps [T_Arrow_Cons; t1; t2] -> Some (t1, t2)
    | _ -> None

let T_Arrows = Arrows T_Arrow
let (|T_Arrows|_|) = (|Arrows|_|) (|T_Arrow|_|)

let T_Row_Var ρ = T_Var (ρ, K_Row)

let K_Row_Ext = K_Arrows [K_Star; K_Row; K_Row]
let (|K_Row_Ext|_|) = function
    | K_Arrows [K_Star; K_Row; K_Row] -> Some ()
    | _ -> None

let T_Row_Empty = T_Cons (string Config.Typing.TyCons.row_special_char, K_Row)
let T_Row_Ext (l, t, ρ) = T_Apps [T_Cons (sprintf "%c%s" Config.Typing.TyCons.row_special_char l, K_Row_Ext); t; ρ]

let (|T_Row_Empty|T_Row_Ext|T_Row_Var|T_NoRow|) = function
    | T_Var (ρ, K_Row)              -> T_Row_Var ρ
    | T_Cons (s, K_Row) when s.Length = 1 && s.[0] = Config.Typing.TyCons.row_special_char ->
        T_Row_Empty

    | T_Apps [T_Cons (s, K_Row_Ext); t; ρ] when s.Length > 1 && s.[0] = Config.Typing.TyCons.row_special_char ->
        T_Row_Ext (s.TrimStart [|Config.Typing.TyCons.row_special_char|], t, ρ)
    | t                                                           -> T_NoRow t

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

let private T_Rowed name r = T_App (T_Cons (name, K_Arrow (K_Row, K_Star)), T_Row r)
let private (|T_Rowed|_|) name = function
    | T_App (T_Cons (name', K_Arrow (K_Row, K_Star)), T_Row r) when name = name' -> Some r
    | _ -> None

let T_Record, T_Variant, T_Tuple, (|T_Record|_|), (|T_Variant|_|), (|T_Tuple|_|) = make_rows T_Rowed (|T_Rowed|_|)
let T_Open_Record xts = T_Record (xts, Some var.fresh)
let T_Closed_Record xts = T_Record (xts, None)
let T_Open_Variant xts = T_Variant (xts, Some var.fresh)
let T_Closed_Variant xts = T_Variant (xts, None)


// substitution types
//

type [< NoComparison; NoEquality >] subst<'t> (env : Env.t<var, 't>) =
    interface IEnumerable<var * 't> with
        member __.GetEnumerator () = (env :> IEnumerable<_>).GetEnumerator ()

    interface Collections.IEnumerable with
        member this.GetEnumerator () = (this :> IEnumerable<_>).GetEnumerator () :> Collections.IEnumerator

    new () = new subst<'t> (Env.empty)
    new (α, t) = new subst<'t> (Env.empty.bind α t)

    member internal __.env = env

    member __.is_empty = env.is_empty
    member __.search = env.search
    member __.dom = env.dom
    member __.restrict αs = new subst<'t> (env.filter (fun α _ -> Set.contains α αs))
    member __.remove αs = new subst<'t> (Seq.fold (fun env α -> env.remove α) env αs)
    member __.map f = new subst<'t> (env.map f)
    member __.search_by f = env.search_by f

    static member pretty_item (bra, ket, α : var, t : 't) = sprintf "%s%O %s %O%s" bra α Config.Printing.substitution_sep t ket
    static member pretty_item (α, t) = subst<'t>.pretty_item ("[", "]", α, t)
    member __.pretty (bra, ket) = if env.is_empty then sprintf "%s%s" bra ket else env.pretty_by_binding (fun α t -> subst<'t>.pretty_item (bra, ket, α, t)) ""
    override this.ToString () = this.pretty ("[", "]")
      
    member private θ1.append (θ2 : subst<'t>) = new subst<'t> (θ1.env + θ2.env)
    static member empty = new subst<'t> ()

    member θ1.compose apply_subst (θ2 : subst<'t>) = (θ2.map (fun _ t2 -> apply_subst θ1 t2)).append (θ1.restrict (θ1.dom - θ2.dom))

type ksubst = subst<kind>
type tsubst = subst<ty>

type [< NoComparison; NoEquality >] tksubst = { t : tsubst; k : ksubst }
with
    static member op_Implicit tθ = { t = tθ; k = ksubst.empty }
    static member op_Implicit kθ = { t = tsubst.empty; k = kθ }
    static member empty = { t = tsubst.empty; k = ksubst.empty }
    member θ.dom = θ.t.dom + θ.k.dom
    override this.ToString () = this.pretty
    member this.pretty = this.t.pretty ("[", "]") + if this.k.is_empty then "" else this.k.pretty ("{", "}") 
       

// augmentations for kinds
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
                use A = var.add_quantified αs
                let αspart = if αs.IsEmpty then "" else sprintf "%s%s. " Config.Printing.dynamic.forall (flatten_stringables Config.Printing.forall_prefix_sep αs)
                in
                    sprintf "%s%O" αspart k

    member this.fv =
        match this with
            | { forall = αs; kind = k } -> k.fv - αs
       


// augmentations for types
//
    
type var with
    static member add_quantified (Q : prefix) = var.add_quantified (Seq.map fst Q)

let inline wrap_pretty_with_kind R' t =
    let R t =
        let k = (^t : (member kind : kind) t)
        in
            if k = K_Star then R' t
            else sprintf "(%s :: %O)" (R' t) k
    in
        R t

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
            | T_App (App s)          -> s
            | T_Closure (x, _, τ, _) -> sprintf "<[%O]>" (Te_Lambda ((x, None), τ))
            | T_Foralls0 (αs, t)     -> use A = var.add_quantified αs in sprintf "forall %s. %O" (flatten_stringables Config.Printing.forall_prefix_sep αs) t
        and R = wrap_pretty_with_kind R'
        in
            R this

//    static member alpha_and_ty k = let α = var.alpha in α, T_Var (α, k)
    static member fresh_var k = T_Var (var.fresh, k)
    static member fresh_var_and_ty k = let α = var.fresh in α, T_Var (α, k)
    static member fresh_star_var = ty.fresh_var K_Star
    static member fresh_star_var_and_ty = ty.fresh_var_and_ty K_Star

    member this.fv =
        match this with
        | T_Var (α, k)              -> Set.singleton α + k.fv
        | T_Cons (_, k)             -> k.fv
        | T_HTuple ts               -> List.fold (fun r (t : ty) -> Set.union r t.fv) Set.empty ts
        | T_App (t1, t2)            -> Set.union t1.fv t2.fv
        | T_Forall (α, t)           -> t.fv - Set.singleton α
        | T_Closure (_, _, _, k)    -> k.fv

    member this.is_monomorphic =
        match this with
        | T_Forall _        -> false
        | T_Var _
        | T_Cons _             
        | T_Closure _       -> true
        | T_App (t1, t2)    -> t1.is_monomorphic && t2.is_monomorphic
        | T_HTuple ts       -> List.fold (fun r (t : ty) -> r && t.is_monomorphic) true ts

    member t.search p =
        let l ts = List.tryFind p ts
        match t with
        | (T_Cons _
        | T_Var _ as t)
        | T_Forall (_, t)   -> l [t]
        | T_App (t1, t2)    -> l [t1; t2]
        | T_HTuple ts       -> l ts
        | T_Closure _       -> None

    member t.search_var α =
        match t.search (function T_Var (β, _) -> α = β | _ -> false) with
        | Some (T_Var (_, k)) -> Some k
        | _ -> None


type fxty with
    override this.ToString () = this.pretty    
    member this.pretty =
        let rec R' = function
            | Fx_Bottom _           -> Config.Printing.dynamic.bottom
            | Fx_F_Ty t             -> t.pretty
            | Fx_Foralls0 (qs, t)   ->
                let Q = prefix.ofSeq qs
                use N = var.add_quantified Q
                in
                    sprintf "Forall %O. %O" Q t
        and R = wrap_pretty_with_kind R'
        in
            R this

    member this.fv =
        match this with
        | Fx_Bottom k             -> k.fv
        | Fx_Forall ((α, ϕ1), ϕ2) -> let r2 = ϕ2.fv in if Set.contains α r2 then ϕ1.fv + (Set.remove α r2) else r2
        | Fx_F_Ty t               -> t.fv

    member this.is_monomorphic =
        match this with
        | Fx_Bottom _
        | Fx_Forall _ -> false
        | Fx_F_Ty t   -> t.is_monomorphic


type scheme with    
    override this.ToString () = this.pretty

    member σ.pretty =
        let { constraints = cs; fxty = Fx_Foralls0 (qs, ϕ1) } = σ
        // TODO: deal with variables in the constraints and choose how to show them, either detecting the outer-most foralls or something like that
        let αs = Computation.B.set { for α, _ in qs do yield α }
        let αspart = if αs.IsEmpty then "" else sprintf "%s%s. " Config.Printing.dynamic.forall (flatten_stringables Config.Printing.forall_prefix_sep αs)
        let cspart = if cs.is_empty then "" else sprintf "{ %O } => " cs
        in
            sprintf "%s%s%O" αspart cspart ϕ1
                        
    static member binding_separator = ty.binding_separator
