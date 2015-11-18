(*
 * Lw
 * Eval.fs: evaluator
 * (C) 2000-2014 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.Eval

#nowarn "21"
#nowarn "40"

open System
open FSharp.Common.Prelude
open FSharp.Common.Parsing
open FSharp.Common.Log
open FSharp.Common
open Lw.Core.Absyn
open Lw.Core.Globals
open System.Threading

type [< NoComparison; NoEquality >] context = {
    cancellation_token : CancellationToken
}
with
    static member non_cancellable = { cancellation_token = CancellationToken.None }

type env = Env.t<id, value>

and [< NoComparison; CustomEquality >] value =
    | V_Const of lit
    | V_Cons of id * value list
    | V_Tuple of value list
    | V_Record of Env.t<id, value>
    // TODO: remove string item from V_Redux pair in order to increase performance a little, thanks to many sprintf's not occuring anymore
    | V_Redux of string * (context -> value -> value)
with
    override this.ToString () = this.pretty

    interface IEquatable<value> with
        member x.Equals y =
            match x, y with
            | V_Const l1, V_Const l2                -> l1 = l2
            | V_Cons (x1, v1o), V_Cons (x2, v2o)    -> x1 = x2 && v1o = v2o
            | V_Tuple v1s, V_Tuple v2s              -> v1s = v2s
            | V_Record env1, V_Record env2          -> env1 = env2
            | _                                     -> false

    override x.Equals y = CustomCompare.equals_with (fun x y -> (x :> IEquatable<value>).Equals y) x y

    override __.GetHashCode () = not_implemented "hash" __SOURCE_FILE__ __LINE__

    member this.pretty =
        match this with
        | V_Const lit         -> lit.pretty
        | V_Cons (x, [])      -> x
        | V_Cons (x, vs)      -> sprintf "%s of %s" x (mappen_stringables (sprintf "[%O]") " " vs)
        | V_Tuple vs          -> sprintf "(%s)" (mappen_strings (sprintf "%O") ", " vs)
        | V_Redux (s, _)      -> sprintf "<%s>" s
        | V_Record env        -> sprintf "{ %s }" (env.pretty "=" "; ")

module Report =
    type runtime_error (message, loc) =
        inherit located_error ("runtime error", message, loc)

    let E loc fmt = throw_formatted (fun msg -> new runtime_error (msg, loc)) fmt

    let incomplete_cases loc v = E loc "match cases are incomplete for value: %O" v
    let unexpected_value loc name expected source_file line v = unexpected "%s at %O does not evaluate to a %s value: %O" source_file line name loc expected v
    let unexpected_after_translation loc source_file line e = unexpected "expression at %O should not occur after translation: %O" source_file line loc e


let beta_redux ctx loc v1 v2 =
    match v1 with
    | V_Redux (_, f) -> f ctx v2
    | V_Cons (x, vs) -> V_Cons (x, vs @ [v2])
    | _              -> Report.unexpected_value loc "left hand of application" "closure" __SOURCE_FILE__ __LINE__ v1


let rec enclose ctx (x, e, Δ : env ref as cl) = V_Redux (Config.Interactive.pretty_closure cl, (fun ctx v -> eval_expr ctx ((!Δ).bind x v) e))

// TODO: implement Δ with a fast hashmap: do not worry about scoping as the bindings can be left inside the map and overwritten, as type checking already dealt with scoping
and eval_expr (ctx : context) Δ (e0 : expr) =
    ctx.cancellation_token.ThrowIfCancellationRequested ()
    let E Δ e = eval_expr ctx Δ e
    match e0.value with
    | Lit lit            -> V_Const lit
    | FreeVar x
    | Var x              -> Δ.lookup x
    | PolyCons x         
    | Reserved_Cons x    -> V_Cons (x, [])
    | Lambda ((x, _), e) -> enclose ctx (x, e, ref Δ)           
    | Tuple ([] | [_])   -> unexpected "empty or unary tuple" __SOURCE_FILE__ __LINE__
    | Tuple es           -> V_Tuple (List.map (E Δ) es)
    | Annot (e, _)
    | Loosen e
    | Val e              -> E Δ e

    | Let (d, e) ->
        let Δ = eval_decl ctx Δ d
        in
            E Δ e

    | App (e1, e2) ->
        let v2 = E Δ e2
        in
            beta_redux ctx e1.loc (E Δ e1) v2

    | If (e1, e2, e3) ->
        let v1 = E Δ e1
        in
            E Δ (match v1 with
                 | V_Const (Bool true)  -> e2
                 | V_Const (Bool false) -> e3
                 | _                    -> Report.unexpected_value e1.loc "if-guard expression" "boolean" __SOURCE_FILE__ __LINE__ v1)

    | Combine es ->
        let rec R = function
            | []       -> unexpected "empty expression list in combine" __SOURCE_FILE__ __LINE__
            | [e]      -> E Δ e
            | e1 :: es -> ignore (E Δ e1); R es
        in
            R es

    | Match (e, cases) ->
        let v = E Δ e
        in
            try
                cases |> List.pick (fun (p, weo, e) ->                    
                                        match eval_patt ctx Δ p v with
                                        | Some Δ when (something (fun we -> match E Δ we with
                                                                            | V_Const (Bool b) -> b
                                                                            | wv               -> Report.unexpected_value we.loc "when-guard in match case" "boolean" __SOURCE_FILE__ __LINE__ wv)
                                                            true weo)
                                            -> Some (E Δ e)
                                        | _ -> None)
            with :? System.Collections.Generic.KeyNotFoundException -> Report.incomplete_cases e.loc v
                     
    | Record (xes, eo) ->
        let venv = something (fun e -> match E Δ e with
                                       | V_Record venv -> venv
                                       |  _            -> Report.unexpected_value e.loc "record expression" "record" __SOURCE_FILE__ __LINE__ e)
                        Env.empty eo
        in
            V_Record (List.fold (fun venv (x, e) -> venv.bind x (E Δ e)) venv xes)

    | Restrict (e, l) ->
        match E Δ e with
        | V_Record venv -> V_Record (venv.remove l)
        |  _            -> Report.unexpected_value e.loc "record expression" "record" __SOURCE_FILE__ __LINE__ e

    | Select (e, l) ->
        match E Δ e with
        | V_Record venv -> venv.lookup l
        |  _            -> Report.unexpected_value e.loc "record expression" "record" __SOURCE_FILE__ __LINE__ e
        
    | Solve _
    | Inject _
    | Eject _ -> Report.unexpected_after_translation e0.loc __SOURCE_FILE__ __LINE__ e0
            
       
and eval_patt ctx Δ p v =
    let R = eval_patt ctx Δ
    match p.value, v with
    | P_Var x, v                                            -> Some (Δ.bind x v)
    | P_Or (p1, p2), v                                      -> match R p1 v with None -> R p2 v | Some _ as r -> r
    | P_And (p1, p2), v                                     -> match R p1 v, R p2 v with Some Δ1, Some Δ2 -> Some (Δ1 + Δ2) | _ -> None
    | P_Cons x, V_Cons (x', []) when x = x'                 -> Some Δ   // TODO: this case is probably unneeded because the case below includes this one as well
    | P_Apps ((P_Cons x) :: ps), V_Cons (x', vs)
        when x = x' && ps.Length = vs.Length                -> Some (List.fold2 (fun Δ p v -> either Δ (R (ULo p) v)) Δ ps vs)
    | P_Lit lit, V_Const lit' when lit = lit'               -> Some Δ
    | P_Tuple ps, V_Tuple vs when ps.Length = vs.Length     -> Some (List.fold2 (fun Δ p v -> either Δ (R p v)) Δ ps vs)
    | P_Annot (p, _), v                                     -> R p v
    | P_As (p, x), v                                        -> Option.map (fun (Δ : env) -> Δ.bind x v) (R p v)
    | P_Wildcard, _                                         -> Some Δ
    | P_Record xps, V_Record venv
        when List.forall (fun (x, _) ->
                venv.exists (fun x' _ -> x = x')) xps       -> Some (List.fold (fun Δ (x, p) -> either Δ (R p (venv.lookup x))) Δ xps)
    | _                                                     -> None


and eval_decl ctx Δ0 (d0 : decl) =
    match d0.value with
    | D_Bind bs ->
        let bs = bs |> List.map (function { patt = ULo (P_Var x); expr = e } -> x, eval_expr ctx Δ0 e
                                        | { patt = p }                       -> not_implemented "pattern in let-bindings: %O" __SOURCE_FILE__ __LINE__ p)
        in            
            Δ0.binds bs

    | D_Rec bs ->
        let rec Δ' = 
            List.fold (fun (Δ : env) { par = (x, _); expr = e } -> Δ.bind x (V_Redux (Config.Interactive.pretty_rec_closure (x, e, Δ),
                                                                                      fun ctx v -> beta_redux ctx e.loc (eval_expr ctx Δ' e) v)))   // DO NOT CURRY variable 'v' or recursion won't stop
                Δ0 bs
        in
            Δ'

    | D_Reserved_Multi ds ->
        List.fold (eval_decl ctx) Δ0 ds

    | D_Overload _
    | D_Kind _   
    | D_Datatype _
    | D_Type _     -> Δ0

    | D_Open _ -> Report.unexpected_after_translation d0.loc  __SOURCE_FILE__ __LINE__ d0
                
let eval_prg ctx Δ0 prg =
    let Δ = List.fold (eval_decl ctx) Δ0 prg.decls
    in
        match prg.main with
        | None   -> Δ, None
        | Some e -> Δ, Some (eval_expr ctx Δ e)


