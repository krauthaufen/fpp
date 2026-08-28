// the ARGUMENT is the thing that does not fit, not the function
module Neg_blame_argument
//! 7 type mismatch: int vs string
let f (a : int) : int = a
let z =
    f
        "s"
printfn "%d" z
