// indexing a string with a non-int
module Neg_string_index_type
//! 5 type mismatch: bool vs int
let s = "abc"
let c = s.[true]
printfn "%c" c
