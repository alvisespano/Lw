(*
 * Lw
 * Typing/Ops.fs: typing utilities
 * (C) 2000-2014 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Ops

open FSharp.Common.Prelude
open FSharp.Common.Log
open FSharp.Common
open Lw.Core
open Lw.Core.Absyn
open Lw.Core.Globals
open Lw.Core.Typing
open Lw.Core.Typing.Defs

let vars_in_term (|Var|Leaf|Nodes|) =
    let rec R = function
        | Var x  -> Set.singleton x
        | Leaf   -> Set.empty
        | Nodes ps as p0 ->
            List.fold (fun set p ->
                    let set' = R p
                    let xs = Set.intersect set set'
                    in
                        if Set.isEmpty xs then Set.union set set'
                        else Report.Error.variables_already_bound_in_pattern (p : node<_, _>).loc xs p0)
                Set.empty ps
    in
        R

let rec vars_in_kind k =
    Computation.B.set {
        match k with
        | K_Var α        -> yield α
        | K_Cons (_, ks) -> for k in ks do yield! vars_in_kind k }

let vars_in_patt p =
    let (|Var|Leaf|Nodes|) (p : patt) =
        match p.value with
        | P_Var x        -> Var x
        | P_PolyCons _
        | P_Cons _
        | P_Lit _
        | P_Wildcard     -> Leaf
        | P_Annot (p, _) 
        | P_As (p, _)    -> Nodes [p]
        | P_App (p1, p2)
        | P_Or (p1, p2) 
        | P_And (p1, p2) -> Nodes [p1; p2]
        | P_Record bs    -> Nodes [for _, p in bs -> p]
        | P_Tuple ps     -> Nodes ps
    in
        vars_in_term (|Var|Leaf|Nodes|) p

let vars_in_ty_patt : ty_patt -> _ =
    let (|Var|Leaf|Nodes|) (p : ty_patt) =
        match p.value with
        | Tp_Var x         -> Var x
        | Tp_Cons _ 
        | Tp_Wildcard      -> Leaf
        | Tp_Annot (p, _) 
        | Tp_As (p, _)     -> Nodes [p]
        | Tp_App (p1, p2) 
        | Tp_Or (p1, p2) 
        | Tp_And (p1, p2)  -> Nodes [p1; p2]
        | Tp_HTuple ps     -> Nodes ps        
        | Tp_Row (xps, po) -> Nodes (List.map snd xps @ (match po with None -> [] | Some p -> [p]))
    in
        vars_in_term (|Var|Leaf|Nodes|)

let rec vars_in_decl (d : decl) =
    let B = Computation.B.set
    let pars bs = B { for b in bs do let x, _ = b.par in yield x }
    let inline ids bs = B { for b in bs do yield (^x : (member id : id) b) }
    in
        B {
            match d.value with
            | D_Bind bs     -> for b in bs do yield! vars_in_patt b.patt
            | D_Rec bs      -> yield! pars bs
            | D_Type bs     -> yield! pars bs
            | D_Kind bs     -> yield! ids bs
            | D_Overload bs -> yield! ids bs
            | D_Open _      -> ()
            | D_Datatype b  -> yield b.id
            | D_Reserved_Multi ds -> for d in ds do yield! vars_in_decl d
        }


let E_CId (c : constraintt) = Id c.pretty_as_translated_id
let E_Jk (jk : jenv_key) = Id jk.pretty_as_translated_id
let P_CId (c : constraintt) = P_Var c.pretty_as_translated_id
let P_Jk (jk : jenv_key) = P_Var jk.pretty_as_translated_id

let possibly_tuple L0 e tuple cs =
    match [ for c in cs -> L0 (e c) ] with
    | []  -> unexpected "empty tuple" __SOURCE_FILE__ __LINE__
    | [p] -> p
    | ps  -> L0 (tuple ps)


// substitution applications
//

let rec subst_kind (kθ : ksubst) =
    let S = subst_kind kθ
    in function
    | K_Cons (x, ks) -> K_Cons (x, List.map S ks)
    | K_Var α as k ->
        match kθ.search α with
        | Some β -> β
        | None   -> k

let subst_var (tθ : tsubst) α =
    match tθ.search α with
    #if DEBUG
    | Some (T_Var (β, _)) as t -> L.warn Min "substituting quantified var: %s" (subst.pretty_item α t); β
    | None                     -> α
    | t                        -> unexpected "substituting quantified var to non-var type: %s" __SOURCE_FILE__ __LINE__ (subst.pretty_item α t)
    #else
    | Some (T_Var (β, _)) -> β
    | _                   -> α
    #endif

let rec subst_ty (tθ : tsubst, kθ : ksubst) =
    let S = subst_ty (tθ, kθ)
    let Sk = subst_kind kθ
    in function
    | T_Var (α, _) as t ->
        match tθ.search α with
        | Some t' -> t'
        | None    -> t

    | T_Forall (α, t)           -> T_Forall (subst_var tθ α, S t)
    | T_Cons (x, k)             -> T_Cons (x, Sk k)
    | T_App (t1, t2)            -> T_App (S t1, S t2)
    | T_HTuple ts               -> T_HTuple (List.map S ts)
    | T_Closure (x, Δ, τ, k)    -> T_Closure (x, Δ, τ, Sk k)

let rec subst_fxty (tθ : tsubst, kθ : ksubst) =
    let S = subst_fxty (tθ, kθ)
    let St = subst_ty (tθ, kθ)
    let Sk = subst_kind kθ
    in function
    | Fx_Bottom k             -> Fx_Bottom (Sk k)
    | Fx_F_Ty t               -> Fx_F_Ty (St t)
    | Fx_Forall ((α, ϕ1), ϕ2) -> Fx_Forall (( α, S ϕ1), S ϕ2)


//let rec subst_kind (kθ : ksubst) (k : kind) = 
//    let Sk = subst_kind kθ
//    in
//        k.map_vars (fun _ k -> k) Sk
//
//let rec subst_ty (tθ : tsubst, kθ : ksubst) (t : ty) =
//    let S = subst_ty (tθ, kθ)
//    let Sk = subst_kind kθ
//    in
//        t.map_vars (fun t _ -> t) (fun α -> function T_Var (β, _) -> β | _ -> α) tθ S Sk
//
//let rec subst_fxty (tθ : tsubst, kθ : ksubst) (ϕ : fxty) =
//    let S = subst_fxty (tθ, kθ)
//    let St = subst_ty (tθ, kθ)
//    let Sk = subst_kind kθ
//    in
//        ϕ.map_vars (fun t _ -> t) (fun α -> function T_Var (β, _) -> β | _ -> α) tθ S St Sk

//// first argument is the NEW subst, second argument is the OLD one
let compose_ksubst (kθ' : ksubst) (kθ : ksubst) = kθ.compose subst_kind kθ'

let compose_tksubst (tθ' : tsubst, kθ') (tθ : tsubst, kθ) =
    let kθ = compose_ksubst kθ' kθ
    let tθ = tθ.compose (fun tθ -> subst_ty (tθ, kθ)) tθ'
    in
        tθ, kθ

let subst_prefix θ Q = prefix.B { for α, ϕ in Q do yield α, subst_fxty θ ϕ }

let subst_type_constraints _ tcs = tcs

let subst_constraints θ (cs : constraints) = cs.map (fun c -> { c with ty = subst_ty θ c.ty })

let subst_scheme θ σ =
    let { constraints = cs; fxty = ϕ } = σ
    in
        { constraints = subst_constraints θ cs; fxty = subst_fxty θ ϕ }
        
let subst_kscheme (kθ : ksubst) σκ =
    let { forall = αs; kind = k } = σκ
    let kθ = kθ.remove αs
    in
        { forall = αs; kind = subst_kind kθ k }

let subst_jenv θ (env : jenv) = env.map (fun _ ({ scheme = σ } as jv) -> { jv with scheme = subst_scheme θ σ })
let subst_kjenv kθ (env : kjenv) = env.map (fun _ -> subst_kscheme kθ)
let subst_tenv θ (env : tenv) = env.map (fun _ -> subst_ty θ)


// active patterns for unquantification, instantiation etc. 
//

let (|Fx_Unquantified_Ty|_|) = function
    | Fx_Bottom _         
    | Fx_Forall _ 
    | Fx_F_Ty (T_Forall _) -> None
    | Fx_F_Ty t            -> Some t

// this has the normal behaviour: quantified vars are not touched
let Fx_ForallsQ (Q : prefix, ϕ) = Fx_Foralls (Seq.toList Q, ϕ)
let (|Fx_ForallsQ|) (Fx_Foralls (qs, ϕ)) = prefix.ofSeq qs, ϕ

let (|Fx_Inst_ForallsQ|) (Fx_ForallsQ (Q, ϕ1) as ϕ0) =   // this has a special behaviour: quantified types are refreshed and right-hand is guaranteed an unquantified F-type
    match ϕ1 with
    | Fx_Unquantified_Ty t -> 
        let θ = new tsubst (Env.t.B { for α, ϕ in Q do yield α, T_Var (var.fresh, ϕ.kind) }), ksubst.empty
        in
            subst_prefix θ Q, subst_ty θ t

    | _ -> unexpected "right-hand of %O is not unquantified: %O" __SOURCE_FILE__ __LINE__ ϕ0 ϕ1

let (|T_ForallK|_|) = function
    | T_Forall (α, t) -> let k = (t.search_var α).Value in Some ((α, k), t)
    | _ -> None

let (|T_ForallsK|) = (|Foralls|) (|T_ForallK|_|)


// ty augmentation
//

type ty with
    member t.instantiate αs =
        let env = Env.t.B { for α in αs do yield α, var.fresh }
        let Sk = subst_kind (new ksubst (env.map (fun _ β -> K_Var β)))
        let rec S = function
            | T_Var (α, k) -> 
                let β =
                    match env.search α with
                    | Some β -> β
                    | None   -> α
                in
                    T_Var (β, k)

            | T_Cons (x, k)             -> T_Cons (x, Sk k)
            | T_App (t1, t2)            -> T_App (S t1, S t2)
            | T_HTuple ts               -> T_HTuple (List.map S ts)
            | T_Forall (α, t)           -> T_Forall (α, S t)
            | T_Closure (x, Δ, τ, k)    -> T_Closure (x, Δ, τ, Sk k)
        in
            S t

    member t.instantiate_fv = t.instantiate t.fv


type fxty with
//    member this.is_unquantified =
//        match this with
//        | Fx_Unquantified_Ty _ -> true
//        | _                    -> false

    member this.nf =
        match this with
        | Fx_F_Ty _
        | Fx_Bottom _ as t -> t
        | Fx_Forall ((α, ϕ1), ϕ2) ->
            if not <| Set.contains α ϕ2.fv then ϕ2.nf
            elif match ϕ2.nf with
                 | Fx_F_Ty (T_Var (β, _)) -> α = β
                 | _                      -> false
            then ϕ1.nf
            else
                match ϕ1.nf with
                | Fx_Unquantified_Ty t -> (subst_fxty (new tsubst (α, t), ksubst.empty) ϕ2).nf
                | ϕ1'                  -> Fx_Forall ((α, ϕ1'), ϕ2.nf)

    member t.ftype =
        let rec R = function
            | Fx_F_Ty t -> t

            | Fx_Bottom k ->
                let α, tα = ty.fresh_var_and_ty k   // TODO: is this fresh var really correct?
                in
                    T_Forall (α, tα)

            | Fx_Forall ((α, Fx_Inst_ForallsQ (Q, t1)), ϕ2) ->
                let θ = new tsubst (α, t1), ksubst.empty
                in
                    R (Fx_ForallsQ (Q, subst_fxty θ ϕ2))

        in
            R t.nf      // normalization can be left out of the recursion

    member t.is_ftype =
        match t with
        | Fx_F_Ty _ -> true
        | _         -> false


let Ungeneralized t = { constraints = constraints.empty; fxty = Fx_F_Ty t }

let (|Ungeneralized|) = function
    | { constraints = cs; fxty = Fx_F_Ty t } when cs.is_empty -> t
    | σ -> unexpected "expected an ungeneralized type scheme but got: %O" __SOURCE_FILE__ __LINE__ σ


// operations over constraints, schemes and environments
//

type constraintt with
    member c.instantiate αs = { c with num = fresh_int (); ty = c.ty.instantiate αs }

type constraints with
    member this.fv = Computation.B.set { for c in this do yield! c.ty.fv }

    member cs.instantiate αs = constraints.B { for c in cs do yield c.instantiate αs }

type scheme with
    member this.fv =
        let { constraints = cs; fxty = t } = this
        in
            cs.fv + t.fv

    member this.instantiate =
        let { constraints = cs; fxty = Fx_ForallsQ (Q, _) as ϕ } = this
        in
            { constraints = cs.instantiate Q.dom; fxty = ϕ }

let internal fv_env fv (env : Env.t<_, _>) = env.fold (fun αs _ v -> Set.union αs (fv v)) Set.empty

let fv_Γ (Γ : jenv) = fv_env (fun { scheme = σ } -> σ.fv) Γ


// operations over kinds
//

let fv_γ (γ : kjenv) = fv_env (fun (kσ : kscheme) -> kσ.fv) γ

type kscheme with
    member this.instantiate =
        let { forall = αs; kind = k } = this
        let kθ = new ksubst (Env.t.B { for α in αs do yield α, K_Var α.refresh })
        in
            subst_kind kθ k

// TODO: restricted named vars should be taken into account also for kind generalization? guess so
let kgeneralize (k : kind) γ named_tyvars =
    let αs = k.fv - (fv_γ γ) - named_tyvars
    in
        { forall = αs; kind = k }

let (|KUngeneralized|) = function
    | { forall = αs; kind = k } when αs.Count = 0 -> k
    | kσ -> unexpected "expected an ungeneralized kind scheme but got: %O" __SOURCE_FILE__ __LINE__ kσ

let KUngeneralized k = { forall = Set.empty; kind = k }


// operations over prefix
//

type prefix with
    // TODO: rewrite split in a less complicated way
    member Q.split αs =
        let rec R Q αs =
            match Q with
            | Q_Nil -> Q_Nil, Q_Nil
            | Q_Cons (Q, (α, t)) ->
                if Set.contains α αs then
                    let Q1, Q2 = R Q (Set.remove α αs + t.fv)
                    in
                        Q_Cons (Q1, (α, t)), Q2
                else
                    let Q1, Q2 = R Q αs
                    in
                        Q1, Q_Cons (Q2, (α, t))
        let Q1, Q2 as r = R Q αs
        #if DEBUG_UNIFY
        L.debug Normal "[split] [%O][{ %s }]\n        = [%O][%O]" Q (flatten_stringables ", " αs) Q1 Q2
        #endif
        r

    member Q.extend (α, ϕ : fxty) =
        let Q', θ' as r =
            match ϕ.nf with
            | Fx_Unquantified_Ty t -> Q, (new tsubst (α, t), ksubst.empty)
            | _                    -> Q + (α, ϕ), empty_θ
        #if DEBUG_UNIFY
        L.debug Normal "[ext] [%O][%O : %O]\n      = [%O][%O]" Q α ϕ Q' θ'
        #endif
        r

    member Q.insert i =
        let rec R = function
            | Q_Nil          -> Q_Cons (Q_Nil, i)
            | Q_Cons (Q, i') -> Q_Cons (R Q, i')
        in
            R Q

    member this.slice_by p =
        let rec R (q : prefix) = function
            | Q_Nil         -> None
            | Q_Cons (Q, i) -> if p i then Some (Q, i, q) else R (q.insert i) Q
        in
            R Q_Nil this

    member this.lookup α =
        match this.search α with
        | Some x -> x
        | None   -> unexpected "type variable %O does not occur in prefix %O" __SOURCE_FILE__ __LINE__ α this

    member this.search α = Seq.tryFind (fst >> (=) α) this |> Option.map snd


let (|Q_Slice|_|) α (Q : prefix) = Q.slice_by (fst >> (=) α) 


type prefix with
    // TODO: rewrite these update methods without the overcomplicated slicing thing
    member inline private Q.update f (α, ty : ^t) =
        match Q.split (^t : (member fv : _) ty) with
        | Q0, Q_Slice α (Q1, _, Q2) -> f (α, ty, Q0, Q1, Q2)
        | _                         -> unexpected "item %O : %O is not in prefix: %O" __SOURCE_FILE__ __LINE__ α ty Q

    static member private update_prefix__reusable_part (α, t : ty, Q0 : prefix, Q1, Q2) =
        let θ = new tsubst (α, t), ksubst.empty
        in
            Q0 + Q1 + subst_prefix θ Q2, θ

    member this.update_prefix_with_bound (α, ϕ) =
        let Q, θ as r =
            this.update <| fun (α, ϕ : fxty, Q0, Q1, Q2) ->
                match ϕ.nf with
                | Fx_Unquantified_Ty t' -> prefix.update_prefix__reusable_part (α, t', Q0, Q1, Q2)
                | _                     -> Q0 + Q1 + (α, ϕ) + Q2, (tsubst.empty, ksubst.empty)
            <| (α, ϕ)
        #if DEBUG_UNIFY
        L.debug Normal "[up-Q] [%O][%O :> %O]\n       = [%O][%O]" this α ϕ Q θ
        #endif
        r

    member this.update_prefix_with_subst (α, t : ty) =
        let Q, θ as r = this.update prefix.update_prefix__reusable_part (α, t)
        #if DEBUG_UNIFY
        L.debug Normal "[up-S] [%O][%O := %O]\n       = [%O][%O]" this α t Q θ
        #endif
        r

[< CompilationRepresentationAttribute(CompilationRepresentationFlags.ModuleSuffix) >]
module prefix =
    let B = new Computation.Builder.itemized_collection<_, _> (empty = Q_Nil, plus1 = (fun i Q -> Q_Cons (Q, i)), plus = (+))


