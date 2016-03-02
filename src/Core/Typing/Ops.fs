(*
 * Lw
 * Typing/Ops.fs: typing utilities
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Typing.Ops

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
    let S x = subst_kind kθ x
    in function
    | K_Cons (x, ks) -> K_Cons (x, List.map S ks)
    | K_Var α as k ->
        match kθ.search α with
        | Some β -> β
        | None   -> k

let subst_var (tθ : tsubst) α =
    match tθ.search α with
    #if DEBUG
    | Some (T_Var (β, _)) -> β
    | None                -> α
    | t                   -> unexpected "substituting var to non-var type: %s" __SOURCE_FILE__ __LINE__ (subst<_>.pretty_item (α, t))
    #else
    | Some (T_Var (β, _)) -> β
    | _                   -> α
    #endif

let rec subst_ty θ =
    let S x = subst_ty θ x
    let Sk = subst_kind θ.k
    in function
    | T_Var (α, k) ->
        match θ.t.search α with
        | Some t' -> S t'               // reapply substitution to the resulting tyvar, which actually is not needed except for substituting kinds
        | None    -> T_Var (α, Sk k)    // substitute kinds also in the resulting tyvar

    | T_Forall (α, t)           -> T_Forall (subst_var θ.t α, S t)
    | T_Cons (x, k)             -> T_Cons (x, Sk k)
    | T_App (t1, t2)            -> T_App (S t1, S t2)
    | T_HTuple ts               -> T_HTuple (List.map S ts)
    | T_Closure (x, Δ, τ, k)    -> T_Closure (x, Δ, τ, Sk k)

let rec subst_fxty θ =
    let S x = subst_fxty θ x
    let St = subst_ty θ
    let Sk = subst_kind θ.k
    in function
    | Fx_Bottom k             -> Fx_Bottom (Sk k)
    | Fx_F_Ty t               -> Fx_F_Ty (St t)
    | Fx_Forall ((α, ϕ1), ϕ2) -> Fx_Forall ((subst_var θ.t α, S ϕ1), S ϕ2)


/// first argument is the NEW subst, second argument is the OLD one
let compose_ksubst (kθ' : ksubst) (kθ : ksubst) = kθ'.compose subst_kind kθ
let compose_tksubst { t = tθ'; k = kθ' } { t = tθ; k = kθ } =
    let kθ = compose_ksubst kθ' kθ
    let tθ = tθ'.compose (fun tθ -> subst_ty { t = tθ; k = kθ }) tθ     // this correct! left argument of compose is 'this' when calling method compose, and composition have the NEW subst as first argument, i.e. left
    in
        { t = tθ; k = kθ }

let subst_prefix θ Q = prefix.B { for α, ϕ in Q do yield subst_var θ.t α, subst_fxty θ ϕ }

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


// active patterns for dealing with quantification, instantiation etc. 
//

type ty with
    member t.is_unquantified =
        match t with
        | T_Forall _ -> false
        | _          -> true

let Fx_ForallsQ (Q : prefix, ϕ : fxty) = Fx_Foralls (Seq.toList Q, ϕ)
let FxU_ForallsQ (Q, t : ty) = Fx_ForallsQ (Q, Fx_F_Ty t)

// all outer quantified vars are taken, both from the flex type and from possible F-type quantifiers, hence right hand is guaranteed unquantified
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



// ty augmentation
//

type ty with
    member t.instantiate_wrt αs =
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

    member t.instantiate = t.instantiate_wrt t.fv

    member t.nf =
        match t with
        | T_Closure _
        | T_Var _
        | T_Cons _ -> t

        | T_App (t1, t2) -> T_App (t1.nf, t2.nf)
        | T_HTuple ts    -> T_HTuple (List.map (fun (t : ty) -> t.nf) ts)

        | T_Forall (α, t2) ->
            if not <| Set.contains α t2.fv then t2.nf
            else T_Forall (α, t2.nf)

    member t.is_nf = t = t.nf
        


type fxty with
    static member instantiate_unquantified (Q : prefix, t : ty) =
            assert t.is_unquantified
//            assert not Q.is_empty
            let θ = !> (new tsubst (Env.t.B { for α, ϕ in Q do yield α, T_Var (var.fresh, ϕ.kind) }))
            in
                subst_prefix θ Q, subst_ty θ t

    member this.nf =
        let r =
            match this with
            | Fx_F_Ty t        -> Fx_F_Ty t.nf
            | Fx_Bottom _ as ϕ -> ϕ 
            | Fx_Forall ((α, ϕ1), ϕ2) ->
                if not <| Set.contains α ϕ2.fv then ϕ2.nf
                else
                    match ϕ2.nf with
                    | Fx_F_Ty (T_Var (β, _)) when α = β -> ϕ1.nf
                    | _ -> 
                        match ϕ1.nf with
                        | FxU_Unquantified t -> (subst_fxty (!> (new tsubst (α, t))) ϕ2).nf                        
                        | ϕ1'                -> Fx_Forall ((α, ϕ1'), ϕ2.nf)
        #if DEBUG_NF
        L.debug High "[nf] nf(%O) = %O" this r
        #endif
        r

    member this.is_nf = this.nf = this

    member this.ftype =
        let rec R = function
            | Fx_F_Ty t -> t

            | Fx_Bottom k -> T_Bottom k

            | Fx_Forall ((α, FxU0_Bottom _), ϕ) ->
                T_Forall (α, R ϕ)

            | Fx_Forall ((α, FxU0_ForallsQ (Q, t1)), ϕ2) ->
                let θ = !> (new tsubst (α, t1))
                in
                    R (Fx_ForallsQ (Q, subst_fxty θ ϕ2))
        let r = R this.nf
        #if DEBUG_NF
        L.debug High "[ftype] ftype(%O) = %O" this r
        #endif
        r

    member this.is_really_flex =
        match this with
        | FxU_ForallsQ (Q, _) when Seq.forall (function (_, Fx_Bottom _) -> true | _ -> false) Q -> false
        | FxU_Unquantified _ -> false
        | _ -> true


let Ungeneralized t = { constraints = constraints.empty; fxty = Fx_F_Ty t }

let (|Ungeneralized|) = function
    | { constraints = cs; fxty = Fx_F_Ty t } when cs.is_empty -> t
    | σ -> unexpected "expected an ungeneralized type scheme but got: %O" __SOURCE_FILE__ __LINE__ σ


// operations over constraints, schemes and environments
//

type constraintt with
    member c.instantiate αs = { c with num = fresh_int (); ty = c.ty.instantiate_wrt αs }

type constraints with
    member this.fv = Computation.B.set { for c in this do yield! c.ty.fv }

    member cs.instantiate αs = constraints.B { for c in cs do yield c.instantiate αs }

type scheme with
    member σ.fv =
        let { constraints = cs; fxty = t } = σ
        in
            cs.fv + t.fv

    member σ.instantiate = σ    // TODOH: there must be something to do with constraints and quantified variables

let internal fv_env fv (env : Env.t<_, _>) = env.fold (fun αs _ v -> Set.union αs (fv v)) Set.empty

let fv_Γ (Γ : jenv) = fv_env (fun { scheme = σ } -> σ.fv) Γ

type ty with
    member t.auto_generalize loc Γ =
        let αs = t.fv - fv_Γ Γ
        if t.is_unquantified then T_Foralls (Set.toList αs, t)
        elif not αs.IsEmpty then Report.Error.unquantified_variables_in_type loc t
        else t


// operations over kinds
//

let fv_γ (γ : kjenv) = fv_env (fun (kσ : kscheme) -> kσ.fv) γ

type kscheme with
    member this.instantiate =
        let { forall = αs; kind = k } = this
        let kθ = new ksubst (Env.t.B { for α in αs do yield α, K_Var α.refresh })
        in
            subst_kind kθ k

type kind with
    member k.generalize γ named_tyvars =
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
    member this.split =
        let rec R Q αs =
            match Q with
            | Q_Nil -> Q_Nil, Q_Nil
            | Q_Cons (Q, (α, ϕ)) ->
                if Set.contains α αs then
                    let Q1, Q2 = R Q (Set.remove α αs + ϕ.fv)
                    in
                        Q1 + (α, ϕ), Q2
                else
                    let Q1, Q2 = R Q αs
                    in
                        Q1, Q2 + (α, ϕ)
        in
            fun αs ->
                let Q1, Q2 as r = R this αs
                #if DEBUG_HML
                L.debug Normal "[split] %O ; { %s }\n        = %O\n          %O" this (flatten_stringables ", " αs) Q1 Q2
                #endif
                r

    member Q.extend (α, ϕ : fxty) =
        let Q', θ' as r =
            match ϕ.nf with
            | FxU_Unquantified t -> Q, !> (new tsubst (α, t))
            | _                  -> Q + (α, ϕ), tksubst.empty
        #if DEBUG_HML
        L.debug Normal "[ext] %O ; (%O : %O)\n      = %O\n        %O" Q α ϕ Q' θ'
        #endif
        r

    member Q.insert i =
        let rec R = function
            | Q_Nil          -> Q_Cons (Q_Nil, i)
            | Q_Cons (Q, i') -> Q_Cons (R Q, i')
        in
            R Q

    member this.lookup α =
        match this.search α with
        | Some x -> x
        | None   -> unexpected "type variable %O does not occur in prefix: %O" __SOURCE_FILE__ __LINE__ α this

    member this.search α = Seq.tryFind (fst >> (=) α) this |> Option.map snd

    member this.slice_by p =
        let rec R (q : prefix) = function
            | Q_Nil         -> None
            | Q_Cons (Q, i) -> if p i then Some (Q, i, q) else R (q.insert i) Q
        in
            R Q_Nil this

let (|Q_Slice|_|) α (Q : prefix) = Q.slice_by (fst >> (=) α)


type prefix with
    #if ENABLE_HML_OPTS
    member Q.update_with_subst (α, t : ty) =
        let θ = !> (new tsubst (α, t))
        let Q' = prefix.B { for β, _ as i in Q do if α <> β then yield i } |> subst_prefix θ
        #if DEBUG_HML
        L.debug Normal "[up-S] %O ; %s\n       = %O\n         %O" Q (subst<_>.pretty_item ("(", ")", α, t)) Q' θ
        #endif
        Q', θ

    member Q.update_with_bound (α, ϕ2 : fxty) =
        let Q', θ as r =
            match ϕ2.nf with
            | FxU_Unquantified t -> Q.update_with_subst (α, t)
            | _                  -> prefix.B { for β, ϕ in Q do if α = β then yield α, ϕ2 else yield β, ϕ }, tksubst.empty
        #if DEBUG_HML
        L.debug Normal "[up-Q] %O ; %s\n       = %O\n         %O" Q (prefix.pretty_item (α, ϕ2)) Q' θ
        #endif
        r

    #else
    member Q.update_with_subst (α, t : ty) =
        let Q', θ as r =
            match Q.split t.fv with
            | Q0, Q_Slice α (Q1, _, Q2) ->
                let θ = !> (new tsubst (α, t))
                in
                    Q0 + Q1 + subst_prefix θ Q2, θ
                
            | _ -> unexpected "item %O : %O is not in prefix: %O" __SOURCE_FILE__ __LINE__ α t Q
        #if DEBUG_HML
        L.debug Normal "[up-S] %O ; %s\n       = %O\n         %O" Q (subst<_>.pretty_item ("(", ")", α, t)) Q' θ
        #endif
        r

    member Q.update_with_bound (α, ϕ2 : fxty) =
        let Q', θ as r =
            match Q.split ϕ2.fv with
            | Q0, Q_Slice α (Q1, _, Q2) ->
                match ϕ2.nf with
                | FxU_Unquantified t ->
                    let θ = !> (new tsubst (α, t))
                    in
                        Q0 + Q1 + subst_prefix θ Q2, θ

                | _ -> Q0 + Q1 + (α, ϕ2) + Q2, tksubst.empty
                
            | _ -> unexpected "item %O : %O is not in prefix: %O" __SOURCE_FILE__ __LINE__ α ϕ2 Q
        #if DEBUG_HML
        L.debug Normal "[up-Q] %O ; %s\n       = %O\n         %O" Q (prefix.pretty_item (α, ϕ2)) Q' θ
        #endif
        r
    #endif

[< CompilationRepresentationAttribute(CompilationRepresentationFlags.ModuleSuffix) >]
module prefix =
    let B = new Computation.Builder.itemized_collection<_, _> (empty = Q_Nil, plus1 = (fun i Q -> Q_Cons (Q, i)), plus = (+))


