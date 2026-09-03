// null is not a proper value of a union — accepted, this built and TRAPPED
// at the first match
module Neg_null_into_union
//! 6 does not have 'null'
type DU = A of string | B of int | C
let x : DU = null
printfn "%A" x
