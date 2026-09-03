// string's members are a fixed builtin set, so the added member resolves to
// nothing — and the statement using it was DROPPED WHOLE: ran, printed
// nothing, exit 0
module Neg_extension_on_builtin
//! 6 cannot be extended
type string with
    member this.ReturnFive () = 5
printfn "%d" ("abc".ReturnFive ())
