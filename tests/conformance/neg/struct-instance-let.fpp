// an instance `let` is a constructor body a value type does not run — it
// was DROPPED whole, side effects included (static let stays legal)
module Neg_struct_instance_let
//! 7 instance `let` binding
[<Struct>]
type S(i : int) =
    let doubled = printfn "EFFECT"; i * 2
    member _.Get = i
printfn "%d" (S(21).Get)
