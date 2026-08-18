// the classic branch-type mismatch
module Neg_if_branch_types
//! 4 type mismatch: int vs string
let x = if true then 1 else "a"
printfn "%A" x
