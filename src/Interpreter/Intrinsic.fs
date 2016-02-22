(*
 * Lw
 * Intrinsic.fs: intrinsic stuff
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.Intrinsic

open System
open System.Text.RegularExpressions
open FSharp.Common.Prelude
open FSharp.Common.Log
open FSharp.Common.Parsing.LexYacc
open FSharp.Common
open Lw.Core.Absyn
open Lw.Core.Globals
open Lw.Core.Typing
open Lw.Core.Typing.Defs
open Lw.Core.Typing.Ops

module C = Lw.Core.Config

module Builtin =
    
    module Types =

        let private Arity arrow atom n s = s, Arrows arrow (List.init (n + 1) (fun _ -> atom))
        let private Stars = Arity K_Arrow K_Star
        let private Arrows ts s = s, K_Arrows ts

        let γ0 = 
            [
                Stars 0 "int"
                Stars 0 "float"
                Stars 0 "char"
                Stars 0 "unit"
                Stars 0 "bool"
                Stars 0 "string"

                Stars 2 "->"
                Arrows [K_Row; K_Star] C.Typing.TyCons.Rows.record
                Arrows [K_Row; K_Star] C.Typing.TyCons.Rows.variant
            ]

    module Values =
        open Lw.Interpreter.Eval

        let private redux (s, f) = V_Redux (s, fun _ -> f)

        let private un (t1, _, (|P1|_|)) (t2, _, _) f name =
            T_Arrow (t1, t2),
            redux ((Id name).pretty, (function V_Const (P1 a) -> f a
                                             | v              -> unexpected "unary redux argument value: %O" __SOURCE_FILE__ __LINE__ v))

        let private un2 a1 (_, C2, _ as a2) f = un a1 a2 (fun v -> V_Const (C2 (f v)))

        let private un1 a = un2 a a

        let private bin3 (t1, _, (|P1|_|)) (t2, _, (|P2|_|)) (t3, C3, _) f name =
            Arrows T_Arrow [t1; t2; t3],
            redux ((Id name).pretty, (fun v1 ->
                redux (sprintf "%O %O" (Id name) v1, (fun v2 ->
                    match v1, v2 with
                        | V_Const (P1 a), V_Const (P2 b) -> V_Const (C3 (f a b))
                        | _                              -> unexpected "non integer constants in primitive binop: %O, %O" __SOURCE_FILE__ __LINE__ v1 v2))))

        let private bin2 a = bin3 a a

        let private I = T_Int,     Int,    function Int x -> Some x | _ -> None
        let private F = T_Float,   Float,  function Float x -> Some x | _ -> None
        let private B = T_Bool,    Bool,   function Bool x -> Some x | _ -> None
        let private S = T_String,  String, function String x -> Some x | _ -> None

        let private un_ii = un1 I
        let private un_ff = un1 F
        let private un_bb = un1 B
        let private bin_iii = bin2 I I
        let private bin_fff = bin2 F F
        let private bin_sss = bin2 S S
        let private bin_iib = bin2 I B
        let private bin_bbb = bin2 B B
        let private bin_ffb = bin2 F B

        let private bin_ααb f name =
            let α = ty.fresh_star_var
            Arrows T_Arrow [α; α; T_Bool],
            redux (name, (fun v1 -> redux (sprintf "%O %O" (Id name) v1, (fun v2 -> V_Const (Bool (f v1 v2))))))

        let ΓΔ0 =
            [
                "+",    bin_iii (+)
                "+.",   bin_fff (+)
                "-",    bin_iii (-)
                "-.",   bin_fff (-)
                "*",    bin_iii (*)
                "*.",   bin_fff (*)
                "/",    bin_iii (/)
                "/.",   bin_fff (/)
                "%",    bin_iii (%)

                "<",    bin_iib (<)
                "<.",   bin_ffb (<)
                ">",    bin_iib (>)
                ">.",   bin_ffb (>)
                "<=",   bin_iib (<=)
                "<=.",  bin_ffb (<=)
                ">=",   bin_iib (>=)
                ">=.",  bin_ffb (>=)
                "=",    bin_ααb (=)

                "^",    bin_sss (+)
                "not",  un_bb (not)
                "%",    bin_iii (%)
                "&&",   bin_bbb (&&)
                "||",   bin_bbb (||)

                C.Typing.negate_symbol,   un_ii (~-)
            ]

let private Γ0, Δ0 =
    List.fold (fun (Γ : jenv, Δ : Eval.env) (x, f) ->
                    let (t : ty), v = f x
                    in
                        Γ.bind (Jk_Var x) { mode = Jm_Normal; scheme = { constraints = constraints.empty
                                                                         fxty        = Fx_F_Ty (T_Foralls (List.ofSeq t.fv, t))} },
                        Δ.bind x v)
        (Env.empty, Env.empty) Builtin.Values.ΓΔ0

let private γ0, δ0 =
    List.fold (fun (γ : kjenv, δ : tenv) (x, k) ->
                    let t = T_Cons (x, k)
                    in
                        γ.bind x (k.generalize γ Set.empty),
                        δ.bind x t) (Env.empty, Env.empty) Builtin.Types.γ0

type [< NoEquality; NoComparison >] envs = {
    Γ : jenv
    Δ : Eval.env
    γ : kjenv
    δ : tenv
}
with
    static member envs0 = { Γ = Γ0; Δ = Δ0; γ = γ0; δ = δ0 }

type StateMonad.state with
    static member state0 = { StateMonad.state.empty with Γ = envs.envs0.Γ; γ = envs.envs0.γ }

