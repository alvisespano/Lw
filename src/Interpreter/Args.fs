(*
 * Lw
 * Args.fs: command line argument parsing
 * (C) Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)
 
module Lw.Interpreter.Args

open FSharp.Common.Prelude
open FSharp.Common.Arg
open FSharp.Common.Log
open FSharp.Common.X.Assembly
open System
open System.Reflection
open Lw

let mutable filename = ""

let credits () =
    let now = DateTime.Now
    let core_asm = Assembly.GetAssembly (typeof<Lw.Core.Globals.logger>) // get Lw.Core assembly by getting any of the type defined in it
    let asm = Assembly.GetExecutingAssembly ()
    let name = asm.GetName ()
    let ver = name.Version
    let title = get_assembly_attribute<AssemblyTitleAttribute> asm
    let core_title = get_assembly_attribute<AssemblyTitleAttribute> core_asm
    let description = get_assembly_attribute<AssemblyDescriptionAttribute> asm
    let product = get_assembly_attribute<AssemblyProductAttribute> asm
    let copyright = get_assembly_attribute<AssemblyCopyrightAttribute> asm
    let company = get_assembly_attribute<AssemblyCompanyAttribute> asm
    let productize = function
        | []  -> ""
        | [s] -> sprintf "%s is" s
        | ss ->
            let last = List.last ss
            let firsts = List.take (List.length ss - 1) ss
            in
                sprintf "%s and %s are" (flatten_strings ", " firsts) last
    in
        sprintf "%s v%d.%d.%d build %d [%04d-%02d-%02d]\n\
                \n\
                %s\n\
                \n\
                %s %s, %s.\n"
            title ver.Major ver.Minor ver.Build ver.Revision now.Year now.Month now.Day
            description
            (productize [product; core_title; title ]) copyright company

let usage () =
    sprintf "\n\nusage: %s <SOURCE FILENAME>\n\n%s"
        (IO.Path.GetFileName (Diagnostics.Process.GetCurrentProcess ()).MainModule.FileName)
        (credits ())

let private other s =
    filename <- s


let private infos =
  [|
    Entry.bool "unicode" (fun b -> Core.Config.Printing.dynamic.unicode <- b)  "enable/disable Unicode output" (Some Core.Config.Printing.dynamic.unicode)
    Entry.flag "greek" (fun b -> Core.Config.Printing.dynamic.greek_tyvars <- true)  "enable greek letters for type variables"
    
    Entry.flag "interactive" (fun () -> Config.mode <- Config.Mode_Interactive)  "enable interactive mode, possibly after interpretation of a given source file"
    Entry.flag "unit-test" (fun () -> Config.mode <- Config.Mode_UnitTest)  "switch to unit-test mode, ignoring input files and performing all tests"

    Entry.flag "pedantic" (fun () -> Config.Log.cfg.all_thresholds <- Min)  "set all log thresholds to level Min"
    Entry.flag "v" (fun () -> Config.Log.cfg.all_thresholds <- Low) "set all log thresholds to level Low"
    Entry.flag "quiet" (fun () -> Config.Log.cfg.all_thresholds <- High) "set all log thresholds to level High"
    Entry.flag "silent" (fun () -> Config.Log.cfg.all_thresholds <- Unmaskerable) "set all log thresholds to level Unmaskerable"
    
    Entry.string "log-file" (fun s -> Core.Config.Log.cfg.filename <- Some s) "set log filename" Core.Config.Log.cfg.filename
    
    Entry.string "debug-threshold" (fun s -> Core.Config.Log.cfg.debug_threshold <- pri.Parse s) "set debug verbosity threshold" (Some Core.Config.Log.cfg.debug_threshold)
    Entry.string "msg-threshold" (fun s -> Core.Config.Log.cfg.msg_threshold <- pri.Parse s) "set informational messages verbosity threshold" (Some Core.Config.Log.cfg.msg_threshold)
    Entry.string "hint-threshold" (fun s -> Core.Config.Log.cfg.hint_threshold <- pri.Parse s) "set hint messages verbosity threshold" (Some Core.Config.Log.cfg.hint_threshold)
    Entry.string "warn-threshold" (fun s -> Core.Config.Log.cfg.warn_threshold <- pri.Parse s) "set warnings verbosity threshold" (Some Core.Config.Log.cfg.warn_threshold)
    
    Entry.int "-W" (fun n -> Core.Config.Report.disabled_warnings <- Set.add n Core.Config.Report.disabled_warnings) "suppress specific warning" None
    Entry.int "-H" (fun n -> Core.Config.Report.disabled_hints <- Set.remove n Core.Config.Report.disabled_hints) "suppress specific hint" None
  |] |> Array.concat

let parse () = ArgParser.Parse (infos, other, usage ())
