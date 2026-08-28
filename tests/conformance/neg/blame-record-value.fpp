// the field's VALUE, not the field name
module Neg_blame_record_value
//! 7 type mismatch: int vs string
type R = { A : int }
let r =
    { A =
        "s" }
printfn "%A" r
