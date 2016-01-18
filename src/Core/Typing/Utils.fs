(*
 * Lw
 * Typing/Utils.fs: typing utilities
 * (C) 2000-2014 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Utils

open FSharp.Common.Prelude
open FSharp.Common.Log
open FSharp.Common
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
    Computation.set {
        match k with
        | K_Var α        -> yield α
        | K_Cons (_, ks) -> for k in ks do yield! vars_in_kind k }

//let rec vars_in_ty t =
//    Computation.set {
//        match t with
//        | T_Var (α, k)     -> yield α; yield! vars_in_kind k
//        | T_Cons (_, k)    -> yield! vars_in_kind k
//        | T_HTuple (ts, k) -> for t in ts do yield! vars_in_ty t; yield! vars_in_kind k
//        | T_App (t1, t2)   -> yield! vars_in_ty t1; yield! vars_in_ty t2
//        | T_Closure ( kind }

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
    let B = Computation.set
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

let rec subst_kind (kθ : ksubst) (k : kind) = 
    let Sk = subst_kind kθ
    in
        k.map_vars (fun α -> match kθ.search α with Some k -> k | None -> K_Var α) Sk


let rec subst_ty (tθ : tsubst, kθ : ksubst) (t :ty) =
    let S = subst_ty (tθ, kθ)
    let Sk = subst_kind kθ
    in
        t.apply_to_vars (fun t _ -> t) tθ S Sk

//// first argument is the NEW subst, second argument is the OLD one
let compose_ksubst (tθ' : ksubst) tθ = tθ'.compose subst_kind tθ

let compose_tksubst (tθ' : tsubst, kθ') (tθ, kθ) =
    let kθ = compose_ksubst kθ' kθ
    let tθ = tθ'.compose (fun tθ -> subst_ty (tθ, kθ)) tθ
    in
        tθ, kθ

let subst_prefix θ Q = [ for α, t in Q do yield α, subst_ty θ t ]

// TODO: implement actual substitution of type constraints for GADTs
let subst_type_constraints _ tcs = tcs

let subst_constraints θ (cs : constraints) = cs.map (fun c -> { c with ty = subst_ty θ c.ty })

let subst_scheme θ σ =
    let { constraints = cs; ty = t } = σ
    in
        { constraints = subst_constraints θ cs; ty = subst_ty θ t }
        
let subst_kscheme (kθ : ksubst) σκ =
    let { forall = αs; kind = k } = σκ
    let kθ = kθ.remove αs
    in
        { forall = αs; kind = subst_kind kθ k }

let subst_jenv θ (env : jenv) = env.map (fun _ ({ scheme = σ } as jv) -> { jv with scheme = subst_scheme θ σ })
let subst_kjenv kθ (env : kjenv) = env.map (fun _ -> subst_kscheme kθ)
let subst_tenv θ (env : tenv) = env.map (fun _ -> subst_ty θ)

// operations over types, schemes and prefixes

let internal fv_env fv (env : Env.t<_, _>) = env.fold (fun αs _ v -> Set.union αs (fv v)) Set.empty

let fv_Γ (Γ : jenv) = fv_env (fun { scheme = σ } -> σ.fv) Γ

let private var_refresher αs = new vasubst (Set.fold (fun (env : Env.t<_, _>) (α : var) -> env.bind α α.refresh) Env.empty αs)

let instantiate { constraints = cs; ty = T_Foralls (Q, t) } =
    let αs = prefix_dom Q
    let tθ = var_refresher αs
    let cs = constr { for c in cs do yield { c.refresh with ty = c.ty.subst_vars tθ } }
    in
        cs, Q, t.subst_vars tθ
          
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

type ty with
    // normal form
    member this.nf =
        match this with
        | T_Forall ((α, t1), t2) ->
            if not <| Set.contains α t2.fv then t2.nf
            elif match t2.nf with
                 | T_Var (β, _) -> α = β
                 | _            -> false
            then t1.nf
            else
                let t' = t1.nf
                in
                    if t'.is_unquantified then subst_ty (new tsubst (α, t'), ksubst.empty) t2
                    else T_Forall ((α, t'), t2.nf)

        | t -> t

    member this.is_nf = this = this.nf


// operations over kinds
//

let fv_γ (γ : kjenv) = fv_env (fun (ς : kscheme) -> ς.fv) γ

let kinstantiate { forall = αs; kind = k } =
    let tθ = var_refresher αs
    in
        k.subst_vars tθ

// TODO: restricted named vars should be taken into account also for kind generalization?
let kgeneralize (k : kind) γ =
    let αs = k.fv - (fv_γ γ)
    in
        { forall = αs; kind = k }

let (|KUngeneralized|) = function
    | { forall = αs; kind = k } when αs.Count = 0 -> k
    | ς -> unexpected "expected an ungeneralized kind scheme but got: %O" __SOURCE_FILE__ __LINE__ ς

let KUngeneralized k = { forall = Set.empty; kind = k }


// prefix management
//

let split_prefix =
    let rec R Q αs =
        match Q with
        | [] -> [], []
        | (α, t : ty) :: Q->
            if Set.contains α αs then
                let Q1, Q2 = R Q (Set.remove α αs + t.fv)
                in
                    (α, t) :: Q1, Q2
            else
                let Q1, Q2 = R Q αs
                in
                    Q1, (α, t) :: Q2
    in
        R
            
let extend_prefix (Q : prefix) (α, t : ty) =
    let t' = t.nf
    in
        if t'.is_unquantified then Q, (new tsubst (α, t'), ksubst.empty)
        else (α, t) :: Q, (tsubst.empty, ksubst.empty)

let extend_prefix_many Q Q' =
    List.fold (fun (Q, θ) (α, t) -> let Q', θ' = extend_prefix Q (α, t) in Q', compose_tksubst θ' θ) (Q, (tsubst.empty, ksubst.empty)) Q'

let slice f =
    let rec R l1 = function
        | []      -> None
        | x :: xs -> if f x then Some (l1, x, xs) else R (x :: l1) xs
    in
        R []

let (|Prefix_Slice|_|) α = slice (fst >> (=) α) 
    

let private update_prefix f Q (α, t : ty) =
    match split_prefix Q t.fv with
    | Q0, Prefix_Slice α (Q1, _, Q2) -> f (α, t, Q0, Q1, Q2)
    | _                              -> unexpected "item (%O : %O) is not in prefix: %O" __SOURCE_FILE__ __LINE__ α t (pretty_prefix Q)

let private update_prefix__reusable_part (α, t, Q0, Q1, Q2) =
    let θ = new tsubst (α, t), ksubst.empty
    in
        Q0 @ Q1 @ subst_prefix θ Q2, θ

let update_prefix_with_bound =
    update_prefix <| fun (α, t, Q0, Q1, Q2 as args) ->
        let t' = t.nf
        in
            if t'.is_unquantified then update_prefix__reusable_part args
            else Q0 @ Q1 @ [α, t] @ Q2, (tsubst.empty, ksubst.empty)

let update_prefix_with_subst = update_prefix update_prefix__reusable_part


let (|T_ForallsK|) = function
    | T_Foralls (Q, t) ->
        let rec R t =
          [ match t with
            | T_Bottom _      
            | T_Closure _
            | T_Cons _                  -> ()
            | T_Var (α, k)              -> match List.tryFind (fst >> (=) α) Q with Some (_, t') -> yield (α, t', k) | None -> ()
            | T_HTuple ts               -> for t in ts do yield! R t
            | T_App (t1, t2)     
            | T_Forall ((_, t1), t2)    -> yield! R t1; yield! R t2 ]
        in
            R t, t

let (|T_ForallK|_|) = function
    | T_Foralls ([α, t1, k], t2) -> Some ((α, t1, k), t2)
    | _                          -> None