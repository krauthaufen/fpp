// one union declaring the same case twice
module Neg_duplicate_union_case
//! 4 the union U declares the case 'A' twice
type U = A of int | A of string
printfn "ok"
