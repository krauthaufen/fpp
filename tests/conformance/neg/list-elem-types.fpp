// list literal mixing element types
module Neg_list_elem_types
//! 4 type mismatch: string vs int
let xs = [ 1; "two"; 3 ]
printfn "%d" (List.length xs)
