// FSharp.Compiler.ComponentTests PatternMatching/ConsList E_consOnNonList:
// a cons pattern against an int scrutinee
module Neg_cons_on_int
//! 7 type mismatch: int vs list<'a>
let f (x : int) =
    match x with
    | a :: b -> a
    | _ -> 0
printfn "%d" (f 1)
