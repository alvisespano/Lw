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
    | T_HTuple of ty list * kind
    | T_App of (ty * ty)
    | T_Closure of id * tenv ref * ty_expr * kind
with
    static member binding_separator = Config.Printing.type_annotation_sep

    member this.kind =
        match this with
        | T_Cons (_, k)
        | T_Var (_, k)
        | T_HTuple (_, k)
        | T_Closure (_, _, _, k) -> k
        | T_App (t1, _) ->
            match t1.kind with
            | K_Arrow (_, k) -> k
            | k              -> unexpected "non-arrow kind %O in left hand of type application: %O" __SOURCE_FILE__ __LINE__ k this

    override x.Equals y = CustomCompare.equals_with (fun x y -> (x :> IEquatable<ty>).Equals y) x y

    override this.GetHashCode () =
        match this with
        | T_Cons (x, k)             -> (x, k).GetHashCode ()
        | T_Var (α, k)              -> (α, k).GetHashCode ()
        | T_HTuple (ts, k)          -> (ts, k).GetHashCode ()
        | T_App (t1, t2)            -> (t1, t2).GetHashCode ()
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

let constr = new Computation.Builder.itemized_collection<_, _> (empty = constraints.empty, plus1 = (fun c (cs : constraints) -> let r = cs.add c in L.debug Normal "constr = %O" r; r), plus = (+))



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

type [< NoComparison; NoEquality >] predicate =
    {
        constraints      : constraints
        type_constraints : type_constraints
    }
with
    static member empty = { constraints = constraints.empty; type_constraints = C_Empty }
    
type [< NoComparison; NoEquality >] scheme =
    {
        forall  : Set<var>
        π       : predicate
        ty      : ty
    }
with
    static member binding_separator = ty.binding_separator


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
            | Jm_Overloadable -> "(overloadable) "
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

let (|Vi_T_Nodes|Vi_T_Var|Vi_T_Leaf|) = function
    | T_Var (α, k)     -> Vi_T_Var (α, k)
    | T_Closure _
    | T_Cons _ as t    -> Vi_T_Leaf t
    | T_App (t1, t2)   -> Vi_T_Nodes [t1; t2]
    | T_HTuple (ts, _) -> Vi_T_Nodes ts

    | T_Row (bs, αo) ->
        let bs = [ for x, t in bs -> x, t]
//        let f ts = List.map2 (fun (x, _) t -> x, t) bs ts
        let t0 =
            match αo with
                | Some ρ -> [T_Row_Var ρ]
                | None   -> []
        in
            Vi_T_Nodes (t0 @ (List.map snd bs))


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
    member __.dom = env.keys |> Set.ofSeq
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
    member k.apply_to_vars f R =
        match k with
        | K_Var α          -> f α
        | K_Cons (x, ks)   -> K_Cons (x, List.map R ks)

    member k.subst_vars (θ : vasubst) =
        let R (k : kind) = k.subst_vars θ
        in
            k.apply_to_vars (fun α -> match θ.search α with Some β -> K_Var β | None -> k) R
    
type ty with
    member t.apply_to_vars f R S =
        match t with
        | T_Var (α, k)                  -> f (α, k)
        | T_Cons (x, k)                 -> T_Cons (x, S k)
        | T_App (t1, t2)                -> T_App (R t1, R t2)
        | T_HTuple (ts, k)              -> T_HTuple (List.map R ts, S k)
        | T_Closure (x, Δ, τ, k)        -> T_Closure (x, Δ, τ, S k)

    member t.subst_vars (θ : vasubst) =
        let R (t : ty) = t.subst_vars θ
        let S (k : kind) = k.subst_vars θ
        in
            t.apply_to_vars (fun (α, k) -> match θ.search α with Some β -> T_Var (β, k) | None -> T_Var (α, S k)) R S

let rec subst_kind (Θ : ksubst) (k : kind) =
    let R = subst_kind Θ
    in
        k.apply_to_vars (fun α -> match Θ.search α with Some k -> k | None -> K_Var α) R

let rec subst_ty (θ : tsubst, Θ : ksubst) (t : ty) =
    let R = subst_ty (θ, Θ)
    let S = subst_kind Θ
    in
        t.apply_to_vars (fun (α, k) -> match θ.search α with Some t -> t | None -> T_Var (α, S k)) R S

//// first argument is the NEW subst, second argument is the OLD one
let compose_ksubst (θ1 : ksubst) θ2 = θ1.compose subst_kind θ2

let compose_tksubst (θ1 : tsubst, Θ1) (θ2, Θ2) =
    let Θ = compose_ksubst Θ1 Θ2
    let θ = θ1.compose (fun θ -> subst_ty (θ, Θ)) θ2
    in
        θ, Θ
        

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
            | T_Tuple _ -> None // NOTE: tuples are encoded via records, so they must be matched before
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

            | T_HTuple (([] | [_]), _) as t -> unexpected "empty or unary htuple: %O" __SOURCE_FILE__ __LINE__ t
            | T_HTuple (ts, _)              -> mappen_strings (fun t -> (match t with A _ -> sprintf "%s" | _ -> sprintf "(%s)") (R t))  ", " ts

            | T_Sym_Cons (x, K_Star) -> sprintf "(%s)" x
            | T_Sym_Cons (x, k)      -> sprintf "((%s) :: %O)" x k
            | T_Cons (x, K_Star)     -> x
            | T_Cons (x, k)          -> sprintf "(%s :: %O)" x k

            | T_Arrow (T_Arrow _ as t1, t2) -> sprintf "(%s) -> %s" (R t1) (R t2)
            | T_Arrow (t1, t2)              -> sprintf "%s -> %s" (R t1) (R t2)

            | T_App (App s) -> s

            | T_Closure (x, _, τ, k) -> sprintf "<[%O] :: %O>" (Te_Lambda ((x, None), τ)) k
        in
            R this

    override this.ToString () = this.pretty
    
    static member fresh_var = T_Star_Var var.fresh

    member this.fv =
        match this with
        | Vi_T_Var (α, k) -> Set.singleton α + k.fv
        | Vi_T_Leaf t     -> t.kind.fv
        | Vi_T_Nodes ts   -> List.fold (fun set (t : ty) -> set + t.fv) Set.empty ts


type predicate with
    override π.ToString () = π.pretty

    member π.pretty =
        let cs = π.constraints
        let tcs = π.type_constraints
        let cspart = if cs.is_empty then "" else predicate.pretty_constraints cs
        let tcspart = if tcs.is_empty then "" else predicate.pretty_type_constraints tcs
        in
            if not cs.is_empty && not tcs.is_empty then sprintf "%s /\\ %s" tcspart cspart
            else tcspart + cspart

    static member pretty_constraints cs = sprintf "{ %O }" cs

    static member pretty_type_constraints tcs = sprintf "(%O)" tcs

    member π.fv = Computation.set { for c in π.constraints do yield! c.ty.fv }


type scheme with    
    override this.ToString () = this.pretty

    member σ.pretty =
        match σ with
            | { forall = αs; π = { constraints = cs } as π; ty = t } ->
                use N = var.reset_normalization αs
                let αspart = if αs.IsEmpty then "" else sprintf "%s%s. " Config.Printing.dynamic.forall (flatten_stringables Config.Printing.sep_in_forall αs)
                let πpart = if cs.is_empty then "" else sprintf "%O => " π
                in
                    sprintf "%s%s%O" αspart πpart t
                        
    member this.fv =
        match this with
            | { forall = αks; π = π; ty = t } -> (t.fv + π.fv) - αks



// substitution applications
//

// TODO: implement actual substitution of type constraints for GADTs
let subst_type_constraints _ tcs = tcs

let subst_predicate Σ π =
    { constraints       = π.constraints.map (fun c -> { c with ty = subst_ty Σ c.ty })
      type_constraints  = subst_type_constraints Σ π.type_constraints }

let subst_scheme (θ : tsubst, Θ) σ =
    let { forall = αs; π = π; ty = t } = σ
    let θ = θ.remove αs
    in
        { forall = αs; π = subst_predicate (θ, Θ) π; ty = subst_ty (θ, Θ) t }
        
let subst_kscheme (Θ : ksubst) σκ =
    let { forall = αs; kind = k } = σκ
    let Θ = Θ.remove αs
    in
        { forall = αs; kind = subst_kind Θ k }

let subst_jenv Σ (env : jenv) = env.map (fun _ ({ scheme = σ } as jv) -> { jv with scheme = subst_scheme Σ σ })
let subst_kjenv Θ (env : kjenv) = env.map (fun _ -> subst_kscheme Θ)
let subst_tenv Σ (env : tenv) = env.map (fun _ -> subst_ty Σ)

// type primitives

let fv_env fv (env : Env.t<_, _>) = env.fold (fun αs _ v -> Set.union αs (fv v)) Set.empty

let fv_Γ (Γ : jenv) = fv_env (fun { scheme = σ } -> σ.fv) Γ

let private var_refresher αs = new vasubst (Set.fold (fun (env : Env.t<_, _>) (α : var) -> env.bind α α.refresh) Env.empty αs)

let instantiate { forall = αs; π = π; ty = t } =
    let θ = var_refresher αs
    let cs = constr { for c in π.constraints do yield { c.refresh with ty = c.ty.subst_vars θ } }
    in
        { π with constraints = cs }, t.subst_vars θ
         
let refresh_ty (t : ty) =
    instantiate { forall = t.fv; π = predicate.empty; ty = t } |> snd
   
let generalize (π : predicate, t : ty) Γ restricted_vars =
    let αks = (t.fv + π.fv) - (fv_Γ Γ) - restricted_vars
    in
        { forall = αks; π = π; ty = t }

let (|Ungeneralized|) = function
    | { forall = αks; π = _; ty = t } when αks.Count = 0 -> t
    | σ -> unexpected "expected an ungeneralized type scheme but got: %O" __SOURCE_FILE__ __LINE__ σ

let Ungeneralized t = { forall = Set.empty; π = predicate.empty; ty = t }

// kind primitives

let fv_χ (χ : kjenv) = fv_env (fun (ς : kscheme) -> ς.fv) χ

let kinstantiate { forall = αs; kind = k } =
    let θ = var_refresher αs
    in
        k.subst_vars θ

// TODO: restricted named vars should be taken into account also for kind generalization?
let kgeneralize (k : kind) χ =
    let αs = k.fv - (fv_χ χ)
    in
        { forall = αs; kind = k }

let (|KUngeneralized|) = function
    | { forall = αs; kind = k } when αs.Count = 0 -> k
    | ς -> unexpected "expected an ungeneralized kind scheme but got: %O" __SOURCE_FILE__ __LINE__ ς

let KUngeneralized k = { forall = Set.empty; kind = k }