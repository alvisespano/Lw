(*
 * Lw
 * Typing/Defs.fs: type system definition
 * (C) 2000-2014 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Defs

#nowarn "60"

open System
open System.Collections.Generic
open FSharp.Common
open FSharp.Common.Prelude
open FSharp.Common.Log
open Lw.Core
open Lw.Core.Globals
open Lw.Core.Absyn

// types, schemes, predicates, constraints, environments, etc.
//

type kscheme = { forall : Set<var>; kind : kind }
with
    static member binding_separator = "::"

type kjenv = Env.t<id, kscheme>

type kconsenv = Env.t<id, var list * kind>

type tenv = Env.t<id, ty>

and [< NoComparison; CustomEquality >] ty =
    | T_Cons of id * kind
    | T_Var of var * kind
    // TODO: T_Huple stands for higher-order tuples (i.e. tuples of types, not to be confused with the type of tuples in the value language), and it's not encoded
    // using rows because rows elements must have kind star, at the moment. Try to design a more general Rowed type which does not need stars on labels, and which would
    // allow for a non-native definition of HTuple
    | T_HTuple of ty list
    | T_App of (ty * ty)
    | T_Forall of (var * ty) * ty
    | T_Closure of id * tenv ref * ty_expr * kind
    | T_Bottom
with
    static member binding_separator = Config.Printing.type_annotation_sep

    member this.kind =
        match this with
        | T_Cons (_, k)
        | T_Var (_, k)
        | T_Closure (_, _, _, k) -> k
        | T_Bottom               -> kind.fresh_var
        | T_HTuple ts            -> K_HTuple [for t in ts do yield t.kind]
        | T_Forall (_, t)        -> t.kind
        | T_App (t1, _)          -> match t1.kind with
                                    | K_Arrow (_, k) -> k
                                    | k              -> unexpected "non-arrow kind %O in left hand of type application: %O" __SOURCE_FILE__ __LINE__ k this

    override x.Equals y = CustomCompare.equals_with (fun x y -> (x :> IEquatable<ty>).Equals y) x y

    override this.GetHashCode () =
        match this with
        | T_Bottom                  -> 0
        | T_Cons (x, k)             -> 1 + (x, k).GetHashCode ()
        | T_Var (α, k)              -> 1 + (α, k).GetHashCode ()
        | T_HTuple ts               -> 1 + ts.GetHashCode ()
        | T_App (t1, t2)            -> 1 + (t1, t2).GetHashCode ()
        | T_Forall ((α, t1), t2)    -> 1 + (α, t1, t2).GetHashCode ()
        | T_Closure (_, _, _, _)    -> unexpected "hashing type closure: %O" __SOURCE_FILE__ __LINE__ this

    interface IEquatable<ty> with
        member x.Equals y =
            x.kind = y.kind
                 && match x, y with
                    | T_Cons (x, _), T_Cons (y, _)      -> x = y
                    | T_Var (α, _), T_Var (β, _)        -> α = β
                    | T_App (t1, t2), T_App (t1', t2')  -> t1 = t1' && t2 = t2'
                    | T_Closure _, _
                    | _, T_Closure _                    -> L.unexpected_error "comparing type closures: %O = %O" x y; false
                    | _                                 -> false


// overloaded symbol constraints
//

type constraint_mode = Cm_FreeVar | Cm_OpenWorldOverload | Cm_ClosedWorldOverload
with
    member this.pretty_as_constraint_id x =
        match this with
        | Cm_OpenWorldOverload      -> sprintf Config.Printing.openworld_overload_constraint_fmt x
        | Cm_ClosedWorldOverload    -> sprintf Config.Printing.closedworld_overload_constraint_fmt x
        | Cm_FreeVar                -> sprintf Config.Printing.freevar_constraint_fmt x

type [< CustomEquality; CustomComparison >] constraintt =
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
    
    member this.refresh = { this with num = fresh_int () }

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

    member __.pretty = sprintf "{ %s }" (flatten_stringables "; " set)
    override this.ToString () = this.pretty

    static member empty = new constraints (Set.empty)

let constr = new Computation.Builder.itemized_collection<_, _> (empty = constraints.empty, plus1 = (fun c (cs : constraints) -> cs.add c), plus = (+))



// GADTs definitions
//

type uvar = Uv of var
with
    override this.ToString () = this.pretty

    member this.pretty =
        match this with
            | Uv va -> va.pretty

type [< NoComparison; NoEquality >] type_constraints = 
    | C_Empty
    | C_Eq of ty * ty
    | C_And of type_constraints * type_constraints
with
    override this.ToString () = this.pretty

    member this.pretty =
        match this with
            | C_Empty        -> ""
            | C_Eq (t1, t2)  -> sprintf "%O ~ %O" t1 t2
            | C_And (c1, c2) -> sprintf "%O & %O" c1 c2

    member this.is_empty = match this with C_Empty -> true | _ -> false

type [< NoComparison; NoEquality >] type_impl_constraints =
    | Ic_Constraint of type_constraints
    | Ic_Impl of Set<var> * Set<uvar> * type_constraints * type_impl_constraints
    | Ic_And of type_impl_constraints * type_impl_constraints
with
    override this.ToString () = this.pretty

    member this.pretty =
        match this with
            | Ic_Constraint c           -> c.pretty
            | Ic_Impl (αs, bs, c, ic)   -> sprintf "[%s] forall %O. %O => %O" (flatten_stringables " " αs) (flatten_stringables " " bs) c ic
            | Ic_And (ic1, ic2)         -> sprintf "%O & %O" ic1 ic2



// schemes and predicates
//

//type [< NoComparison; NoEquality >] predicate =
//    {
//        constraints      : constraints
//        type_constraints : type_constraints
//    }
//with
//    static member empty = { constraints = constraints.empty; type_constraints = C_Empty }
    
type [< NoComparison; NoEquality >] scheme =
    {
        constraints      : constraints
//        type_constraints : type_constraints
        ty               : ty
    }

type prefix = (var * ty) list

let prefix_dom Q = Computation.set { for α, _ in Q do yield α }

let pretty_prefix_item (α, t) = sprintf "(%O >= %O)" α t
let pretty_prefix Q = mappen_strings pretty_prefix_item Config.Printing.sep_in_forall Q



// judice environment
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

let T_Apps = Apps T_App
let (|T_Apps|_|) = (|Apps|_|) (function T_App (t1, t2) -> Some (t1, t2) | _ -> None)

let T_Foralls = Foralls T_Forall
let (|T_Foralls|) = (|Foralls|) (function T_Forall ((α, t1), t2) -> Some ((α, t1), t2) | _ -> None)

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
let T_Tailed_Record xts = T_Record (xts, Some var.fresh)


// substitutions
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
    member __.restrict αks = new subst<'t> (env.filter (fun α _ -> Set.exists (fun (α', _) -> α = α') αks))
    member __.remove αs = new subst<'t> (Seq.fold (fun env α -> env.remove α) env αs)
    member __.map f = new subst<'t> (env.map f)

    member __.pretty_sep sep = env.pretty_by_binding (fun α t -> sprintf "%O = %O" α t) sep
    member this.pretty = this.pretty_sep "; "
    override this.ToString () = this.pretty
      
    static member (-) (θ1 : subst<'a>, θ2 : subst<'a>) = new subst<'a> (θ1.env - θ2.env)
    static member (+) (θ1 : subst<'a>, θ2 : subst<'a>) = new subst<'a> (θ1.env + θ2.env)

    static member empty = new subst<'t> ()

    member θ1.compose apply_subst (θ2 : subst<'t>) = θ1.map (fun _ t -> apply_subst θ2 t) + θ2.restrict (θ2.dom - θ1.dom)


type ksubst = subst<kind>
type tsubst = subst<ty>
type vasubst = subst<var>
type tksubst = tsubst * ksubst


type kind with
    member internal k.apply_to_vars f R =
        match k with
        | K_Var α          -> f α
        | K_Cons (x, ks)   -> K_Cons (x, List.map R ks)

    member k.subst_vars (θ : vasubst) =
        let R (k : kind) = k.subst_vars θ
        in
            k.apply_to_vars (fun α -> match θ.search α with Some β -> K_Var β | None -> k) R

type ty with
    member internal t.apply_to_vars f (θ : subst<_>) S Sk =
        match t with
        | T_Bottom -> T_Bottom
        | T_Var (α, k) ->
            match θ.search α with
            | Some x -> f x k
            | None   -> T_Var (α, Sk k)

        | T_Cons (x, k)             -> T_Cons (x, Sk k)
        | T_App (t1, t2)            -> T_App (S t1, S t2)
        | T_HTuple ts               -> T_HTuple (List.map S ts)
        | T_Forall ((α, t1), t2)    -> if Set.contains α θ.dom then unexpected "some quantified variables in polymorphic type %O appear in domain of substituion %O" __SOURCE_FILE__ __LINE__ t θ // TODO: can this check be removed?
                                       else T_Forall ((α, S t1), S t2)
        | T_Closure (x, Δ, τ, k)    -> T_Closure (x, Δ, τ, Sk k)

    member t.subst_vars (θ : vasubst) =
        let S (t : ty) = t.subst_vars θ
        let Sk (k : kind) = k.subst_vars θ
        in
            t.apply_to_vars (fun β k -> T_Var (β, Sk k)) θ S Sk

       

// augmentations for kinds
//

type kind with
    member this.fv =     
        match this with
            | K_Var α          -> Set.singleton α
            | K_Cons (_, ks)   -> List.fold (fun set (k : kind) -> set + k.fv) Set.empty ks

type kscheme with
    override this.ToString () = this.pretty

    member ς.pretty =
        match ς with
            | { forall = αs; kind = k } ->
                use N = var.reset_normalization αs
                let αspart = if αs.IsEmpty then "" else sprintf "%s%s. " Config.Printing.dynamic.forall (flatten_stringables Config.Printing.sep_in_forall αs)
                in
                    sprintf "%s%O" αspart k

    member this.fv =
        match this with
            | { forall = αs; kind = k } -> k.fv - αs
       


// augmentations for types
//

type ty with
    member this.pretty =
        let (|T_Sym_Cons|_|) = (|Sym|_|) (function T_Cons (x, k) -> Some (x, (x, k)) | _ -> None)
        let (|A|_|) = function
            | T_Tuple _ -> None // NOTE: tuples are encoded using row types with integer labels, so they must be matched before
            | T_Var _ | T_Record _ | T_Variant _ | T_Cons _ | T_Closure _ | T_Row _ as e -> Some e
            | _ -> None
        let (|App|) = (|Application|) (function T_App (t1, t2) -> Some (t1, t2) | _ -> None) (|A|_|)
        let rec R = function
            | T_Star_Var α -> sprintf "%O" α
            | T_Var (α, k) -> sprintf "(%O :: %O)" α k

            | T_Tuple ([] | [_]) as t -> unexpected "empty or unary tuple: %O" __SOURCE_FILE__ __LINE__ t
            | T_Tuple ts              -> mappen_strings (fun t -> (match t with A _ -> sprintf "%s" | _ -> sprintf "(%s)") (R t))  " * " ts

            | T_Record row  -> sprintf "{ %s }" (pretty_row "; " Config.Printing.type_annotation_sep row)
            | T_Variant row -> sprintf "< %s >" (pretty_row " | " Config.Printing.type_annotation_sep row)
            | T_Row row     -> sprintf "(| %s |)" (pretty_row " | " Config.Printing.type_annotation_sep row)

            | T_HTuple ([] | [_]) as t -> unexpected "empty or unary htuple: %O" __SOURCE_FILE__ __LINE__ t
            | T_HTuple ts              -> mappen_strings (fun t -> (match t with A _ -> sprintf "%s" | _ -> sprintf "(%s)") (R t))  ", " ts

            | T_Sym_Cons (x, K_Star) -> sprintf "(%s)" x
            | T_Sym_Cons (x, k)      -> sprintf "((%s) :: %O)" x k
            | T_Cons (x, K_Star)     -> x
            | T_Cons (x, k)          -> sprintf "(%s :: %O)" x k

            | T_Arrow (T_Arrow _ as t1, t2) -> sprintf "(%s) -> %s" (R t1) (R t2)
            | T_Arrow (t1, t2)              -> sprintf "%s -> %s" (R t1) (R t2)

            | T_App (App s)          -> s
            | T_Foralls (Q, t)       -> sprintf "forall %s. %O" (pretty_prefix Q) t
            | T_Closure (x, _, τ, k) -> sprintf "<[%O] :: %O>" (Te_Lambda ((x, None), τ)) k

            // these are not supposed to be matched because active patterns should stand in place of them above
            | T_Forall _ as t -> unexpected "term %O in type" __SOURCE_FILE__ __LINE__ t
        in
            R this

    override this.ToString () = this.pretty
    
    static member fresh_var = T_Star_Var var.fresh

    // free type variables
    member this.fv =
        match this with
        | T_Bottom                  -> Set.empty
        | T_Var (α, k)              -> Set.singleton α + k.fv
        | T_Cons (_, k)             -> k.fv
        | T_HTuple ts               -> List.fold (fun r (t : ty) -> Set.union r t.fv) Set.empty ts
        | T_App (t1, t2)            -> Set.union t1.fv t2.fv
        | T_Forall ((α, t1), t2)    -> let r2 = t2.fv in if Set.contains α r2 then t1.fv + (Set.remove α r2) else r2
        | T_Closure (_, _, _, k)    -> k.fv

    member this.is_monomorphic =
        match this with
        | T_Bottom          
        | T_Forall _        -> false
        | T_Var _
        | T_Cons _             
        | T_Closure _       -> true
        | T_App (t1, t2)    -> t1.is_monomorphic && t2.is_monomorphic
        | T_HTuple ts       -> List.fold (fun r (t : ty) -> r && t.is_monomorphic) true ts

    member this.is_unquantified =
        match this with
        | T_Bottom          
        | T_Forall _        -> false
        | _                 -> true


// TODO: refactor this predicate thingie and put constraints and whatever else directly inside the scheme
//type predicate with
//    override π.ToString () = π.pretty
//
//    member π.pretty =
//        let cs = π.constraints
//        let tcs = π.type_constraints
//        let cspart = if cs.is_empty then "" else predicate.pretty_constraints cs
//        let tcspart = if tcs.is_empty then "" else predicate.pretty_type_constraints tcs
//        in
//            if not cs.is_empty && not tcs.is_empty then sprintf "%s /\\ %s" tcspart cspart
//            else tcspart + cspart
//
//    static member pretty_constraints cs = sprintf "{ %O }" cs
//
//    static member pretty_type_constraints tcs = sprintf "(%O)" tcs

type constraints with

    member this.fv = Computation.set { for c in this do yield! c.ty.fv }


type scheme with    
    override this.ToString () = this.pretty

    member σ.pretty =
        let { constraints = cs; ty = T_Foralls (Q, t) } = σ
        let αs = prefix_dom Q
        use N = var.reset_normalization αs
        let αspart = if αs.IsEmpty then "" else sprintf "%s%s. " Config.Printing.dynamic.forall (flatten_stringables Config.Printing.sep_in_forall αs)
        let cspart = if cs.is_empty then "" else sprintf "{ %O } => " cs
        in
            sprintf "%s%s%O" αspart cspart t
                        
    member this.fv =
        let { constraints = cs; ty = t } = this
        in
            cs.fv + t.fv

    static member binding_separator = ty.binding_separator


// substitution applications
//

let rec subst_kind (Θ : ksubst) (k : kind) = 
    let Sk = subst_kind Θ
    in
        k.apply_to_vars (fun α -> match Θ.search α with Some k -> k | None -> K_Var α) Sk


let rec subst_ty (θ : tsubst, Θ : ksubst) (t :ty) =
    let S = subst_ty (θ, Θ)
    let Sk = subst_kind Θ
    in
        t.apply_to_vars (fun t _ -> t) θ S Sk

//// first argument is the NEW subst, second argument is the OLD one
let compose_ksubst (θ' : ksubst) θ = θ'.compose subst_kind θ

let compose_tksubst (θ' : tsubst, Θ') (θ, Θ) =
    let Θ = compose_ksubst Θ' Θ
    let θ = θ'.compose (fun θ -> subst_ty (θ, Θ)) θ
    in
        θ, Θ

let subst_prefix Σ Q = [ for α, t in Q do yield α, subst_ty Σ t ]

// TODO: implement actual substitution of type constraints for GADTs
let subst_type_constraints _ tcs = tcs

let subst_constraints Σ (cs : constraints) = cs.map (fun c -> { c with ty = subst_ty Σ c.ty })

let subst_scheme Σ σ =
    let { constraints = cs; ty = t } = σ
    in
        { constraints = subst_constraints Σ cs; ty = subst_ty Σ t }
        
let subst_kscheme (Θ : ksubst) σκ =
    let { forall = αs; kind = k } = σκ
    let Θ = Θ.remove αs
    in
        { forall = αs; kind = subst_kind Θ k }

let subst_jenv Σ (env : jenv) = env.map (fun _ ({ scheme = σ } as jv) -> { jv with scheme = subst_scheme Σ σ })
let subst_kjenv Θ (env : kjenv) = env.map (fun _ -> subst_kscheme Θ)
let subst_tenv Σ (env : tenv) = env.map (fun _ -> subst_ty Σ)

// operations over types, schemes and prefixes

let internal fv_env fv (env : Env.t<_, _>) = env.fold (fun αs _ v -> Set.union αs (fv v)) Set.empty

let fv_Γ (Γ : jenv) = fv_env (fun { scheme = σ } -> σ.fv) Γ

let private var_refresher αs = new vasubst (Set.fold (fun (env : Env.t<_, _>) (α : var) -> env.bind α α.refresh) Env.empty αs)

let instantiate { constraints = cs; ty = T_Foralls (Q, t) } =
    let αs = prefix_dom Q
    let θ = var_refresher αs
    let cs = constr { for c in cs do yield { c.refresh with ty = c.ty.subst_vars θ } }
    in
        cs, Q, t.subst_vars θ
          
let generalize (cs : constraints, Q, t : ty) Γ restricted_vars =
    let αs = (t.fv + cs.fv) - (fv_Γ Γ) - restricted_vars
    let Q = [ for α, t in Q do if Set.contains α αs then yield α, t ]
    in
        { constraints = cs; ty = T_Foralls (Q, t) }

// TODO: refresh_ty and Ungeneralized may not be of use anymore in HML
let refresh_ty (t : ty) =
    let _, _, t = instantiate { constraints = constraints.empty; ty = t }
    in
        t

let Ungeneralized t = { constraints = constraints.empty; ty = t }

let (|Ungeneralized|) = function
    | { constraints = _; ty = T_Foralls ([], t) } -> t
    | σ -> unexpected "expected an ungeneralized type scheme but got: %O" __SOURCE_FILE__ __LINE__ σ


// operations over kinds

let fv_γ (γ : kjenv) = fv_env (fun (ς : kscheme) -> ς.fv) γ

let kinstantiate { forall = αs; kind = k } =
    let θ = var_refresher αs
    in
        k.subst_vars θ

// TODO: restricted named vars should be taken into account also for kind generalization?
let kgeneralize (k : kind) γ =
    let αs = k.fv - (fv_γ γ)
    in
        { forall = αs; kind = k }

let (|KUngeneralized|) = function
    | { forall = αs; kind = k } when αs.Count = 0 -> k
    | ς -> unexpected "expected an ungeneralized kind scheme but got: %O" __SOURCE_FILE__ __LINE__ ς

let KUngeneralized k = { forall = Set.empty; kind = k }