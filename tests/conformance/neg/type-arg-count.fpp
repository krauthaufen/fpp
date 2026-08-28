// a generic type applied at the wrong arity
module Neg_type_arg_count
//! 4 type mismatch: list<int, int> vs list<'a>
let xs : list<int, int> = []
printfn "%d" (List.length xs)
