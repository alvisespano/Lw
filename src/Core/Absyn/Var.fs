(*
 * Lw
 * Absyn/Var.fs: variable type
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Core.Absyn.Var

#nowarn "60"

open System
open System.Collections.Generic
open FSharp.Common
open Lw.Core
open FSharp.Common.Log
open FSharp.Common.Parsing
open Lw.Core.Globals


[< CustomEquality; CustomComparison; System.Diagnostics.DebuggerDisplay("{ToString()}") >]
type var = Va of int * string option
with
    member this.uid =
        match this with
        | Va (n, _) -> n

    override x.Equals y = CustomCompare.equals_by (fun (α : var) -> α.uid) x y
 
    override x.GetHashCode () = match x with Va (n, so) -> hash (n, so)
 
    interface System.IComparable with
      member x.CompareTo y = CustomCompare.compare_by (fun (α : var) -> α.uid) x y

// this module is needed and cannot be turn into static members within the var class because static members are unit closures thus cannot be constants
[< CompilationRepresentationAttribute(CompilationRepresentationFlags.ModuleSuffix) >]
module var =
    type normalization_context () =
        member val cnt = 0 with get, set
        member val env = Env.empty with get, set

    let ctx_stack = new Stack<normalization_context> ()
    let forall : Set<var> ref = ref Set.empty

type var with
    static member fresh =
      #if DEBUG_FRESH_VARS
      let r =
      #endif
        Va (fresh_int (), None)
      #if DEBUG_FRESH_VARS
      L.hint Low "new fresh var: %O" r
      r
      #endif

    static member fresh_named s =
      #if DEBUG_FRESH_VARS
      let r =
      #endif
        Va (fresh_int (), Some s)
      #if DEBUG_FRESH_VARS
      L.hint Low "new fresh named var: %O" r
      r
      #endif

    member this.refresh =
        match this with
        | Va (_, Some s) -> var.fresh_named s
        | Va (_, None)   -> var.fresh

    static member private letterize n =
        let start, endd = Config.Printing.dynamic.tyvar_range
        let start, endd = Convert.ToInt32 start, Convert.ToInt32 endd
        let bas = endd - start + 1
        let chr n = n + start |> Convert.ToChar |> Convert.ToString
        let rec div n = let n' = n / bas in (if n' = 0 then "" else div n') + (chr (n % bas))
        in
            div n

    static member get_normalization_context = new var.normalization_context ()

    static member reset_normalization =
        #if !DISABLE_VAR_NORM
        var.ctx_stack.Push (var.get_normalization_context)
        #endif
        { new IDisposable with
            member __.Dispose () =
                #if !DISABLE_VAR_NORM
                ignore <| var.ctx_stack.Pop ()
                #endif
                ()
        }

    static member add_quantified α =
        var.forall := Set.add α !var.forall
        { new IDisposable with
            member __.Dispose () = var.forall := Set.remove α !var.forall
        }

    static member add_quantifieds αs =
        let ds = Seq.map var.add_quantified αs
        { new IDisposable with
            member __.Dispose () = for d in ds do d.Dispose ()
        }

    member __.is_quantification_enabled = not (!var.forall).IsEmpty
    member __.is_normalization_enabled = if var.ctx_stack.Count > 0 then Some (var.ctx_stack.Peek ()) else None
    
    member this.pretty =
        match this.is_normalization_enabled with
        | None     -> this.pretty_unnormalized
        | Some ctx -> this.pretty_normalized ctx

    override this.ToString () = this.pretty

    member this.pretty_unnormalized = 
        match this with
        | Va (n, None)   -> var.letterize n
        | Va (_, Some s) -> s
        |> this.pretty_with_quantification

    member this.pretty_normalized ctx =
        let env = ctx.env
        let name =
            match env.search this.uid with
            | Some s -> s
            | None ->
                let name_exists s = env.exists (fun _ s' -> s' = s)
                let next_fresh_name () =
                    let r = var.letterize ctx.cnt
                    ctx.cnt <- ctx.cnt + 1
                    r
                match this with
                | Va (_, None) ->
                    let rec R () =
                        let r = next_fresh_name ()
                        in
                            if name_exists r then R () else r
                    in
                        R ()

                | Va (_, Some s) ->
                    let rec R (root, n) =
                        let s = sprintf "%s%d" root n   // UNDONE
                        in
                            if name_exists s then R (root, n + 1) else s
                    in
                        R (s, 0)
        ctx.env <- env.bind this.uid name
        this.pretty_with_quantification name

    member this.pretty_with_quantification name =
        #if DEBUG_VAR_NAMES
        let fmt = 
            match this with
            | Va (_, Some _) -> Config.Printing.named_var_fmt
            | Va (_, None)   -> Config.Printing.anonymous_var_fmt
        sprintf fmt name this.uid
        #else
        name
        #endif
        |> sprintf (if not this.is_quantification_enabled || Set.exists (fun (α : var) -> α.uid = this.uid) !var.forall then Config.Printing.dynamic.tyvar_quantified_fmt
                    else Config.Printing.dynamic.tyvar_unquantified_fmt)

