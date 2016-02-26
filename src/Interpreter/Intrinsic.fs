(*
 * Lw
 * Intrinsic.fs: intrinsic stuff
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.Intrinsic

open System
open System.Text.RegularExpressions

open FSharp.Common.Log
open FSharp.Common
open Lw.Core.Absyn
open Lw.Core.Globals
open Lw.Core.Typing
open Lw.Core.Typing.Defs
open Lw.Core.Typing.Ops
open Lw.Core.Typing.StateMonad
open Lw.Core

module A = Lw.Core.Absyn
module N = Lw.Core.Config.Typing.Names
module T = N.Type
module K = N.Kind
module D = N.Data

module Builtin =
    
    module Types =

        let arrows l s = s, K_Arrows l
        let stars n = arrows [for _ in 1..n do yield K_Star]

        let γ0 = 
            [
                stars 1 T.unit
                stars 1 T.int
                stars 1 T.bool
                stars 1 T.float
                stars 1 T.char
                stars 1 T.string
                stars 3 T.arrow
                arrows [K_Row; K_Star] T.Row.record
                arrows [K_Row; K_Star] T.Row.variant
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
            T_Arrows [t1; t2; t3],
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
            T_Arrows [α; α; T_Bool],
            redux (name, (fun v1 -> redux (sprintf "%O %O" (Id name) v1, (fun v2 -> V_Const (Bool (f v1 v2))))))

        let ΓΔ0 =
            [
                // TODOL: many of these operators will have to become overloaded one day
                // arithmetic
                "+",    bin_iii (+)     
                "+.",   bin_fff (+)
                "-",    bin_iii (-)
                "-.",   bin_fff (-)
                "*",    bin_iii (*)
                "*.",   bin_fff (*)
                "/",    bin_iii (/)
                "/.",   bin_fff (/)
                "%",    bin_iii (%)
                N.int_negate,   un_ii (~-)
                N.float_negate, un_ff (~-)  // TODOL: this and other float operators are never used because the parser only supports integer versions at the moment

                // logic
                "<",    bin_iib (<)
                "<.",   bin_ffb (<)
                ">",    bin_iib (>)
                ">.",   bin_ffb (>)
                "<=",   bin_iib (<=)
                "<=.",  bin_ffb (<=)
                ">=",   bin_iib (>=)
                ">=.",  bin_ffb (>=)
                "=",    bin_ααb (=)
                "not",  un_bb (not)
                "&&",   bin_bbb (&&)
                "||",   bin_bbb (||)

                // strings
                "^",    bin_sss (+)
            ]

    module Decls =

//        let d s =
//            match (Parsing.parse_decl s).value with
//            | D_Datatype dbs -> dbs
//            | _              -> unexpected "declaration is expected to be a datatype" __SOURCE_FILE__ __LINE__

        let t = Parsing.parse_ty_expr

        let datatypes =
           List.map (fun x -> ULo (D_Datatype x))
             [
                // native datatypes here
                { id = T.list; kind = K_Arrows [K_Star; K_Star] // list datatype cannot be parsed and must be defined as a data structure, because constructor names are reserved ids which cannot be lexed
                  datacons =
                    [
                        { id = D.list_nil; signature = t "list 'a"  }
                        { id = D.list_cons; signature = t "'a -> list 'a -> list 'a"  }
                    ]
                }
            ]
          @ List.map Parsing.parse_decl [
                // parsable datatypes here
                sprintf "datatype %s :: * -> * = %s : option 'a | %s : 'a -> option 'a" T.option D.option_none D.option_some
            ]

        let all = datatypes


// make up environments
//


type [< NoEquality; NoComparison >] envs = {
    Γ : jenv
    Δ : Eval.env
    γ : kjenv
    δ : tenv
}
with
    static member create_envs () =
        L.msg Low "populating intrinsics..."
        // pupulate Γ and Δ with types and values of builtin functions
        let Γ01, Δ01 =
            Builtin.Values.ΓΔ0
                |> List.fold (fun (Γ : jenv, Δ : Eval.env) (x, f) ->
                                let (t : ty), v = f x
                                in
                                    Γ.bind (Jk_Var x) { mode = Jm_Normal; scheme = { constraints = constraints.empty
                                                                                     fxty        = Fx_F_Ty (T_Foralls (List.ofSeq t.fv, t))} },
                                    Δ.bind x v)
                    (Env.empty, Env.empty) 

        // populate γ and δ with kinds and type constructors of builtin types
        let γ01, δ01 =
            Builtin.Types.γ0
                |> List.fold (fun (γ : kjenv, δ : tenv) (x, k) ->
                            let t = T_Cons (x, k)
                            in
                                γ.bind x (k.generalize γ Set.empty),
                                δ.bind x t)
                    (Env.empty, Env.empty)

        // add declarations
        let Γ0, γ0, δ0 =
            Builtin.Decls.all
                |> List.fold (fun (Γ : jenv, γ : kjenv, δ) d ->
                        let (), st = Inference.W_decl context.top_level d { state.empty with Γ = Γ; γ = γ; δ = δ }
                        in
                            st.Γ, st.γ, st.δ)
                    (Γ01, γ01, δ01)

        let Δ0 = Δ01    // no more values to add to value environment
        L.msg Min "intrinsics created"
        { Γ = Γ0; Δ = Δ0; γ = γ0; δ = δ0 }

let lazy_envs0 = lazy envs.create_envs ()

type envs with
    static member envs0 = lazy_envs0.Value

type StateMonad.state with
    static member state0 = { StateMonad.state.empty with Γ = envs.envs0.Γ; γ = envs.envs0.γ }

