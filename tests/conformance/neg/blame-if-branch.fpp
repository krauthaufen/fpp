// the BRANCH that disagrees, not the `if`
module Neg_blame_if_branch
//! 8 type mismatch: int vs string
let v =
    if true then
        1
    else
        "s"
printfn "%A" v
