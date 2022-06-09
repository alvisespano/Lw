module Lw.Interpreter.UnitTest.Temp

open Lw.Interpreter.UnitTester
open Lw.Interpreter.UnitTester.Aux


let temp1 =
    { name = "Temp1"
      flags = [ ShowSuccessful; Verbose; ShowHints; ShowWarnings; (*Dependencies (Basic.all @ [HML.defs])*) ]
      entries = [
        "let id x = x",                                 typed_ok_ [ShowWarning 10]
        "let id x = x",                                 typed_ok_ [HideWarning 10]

    //    "let ids = [id]",                               typed_ok
    //
    //    "let ids : forall 'a. list ('a -> 'a) = ids
    //     in
    //        map poly ids",                              wrong_type_ [ShowHint 123]
        ]
    }