// a recursive body cannot be copied into itself
module Neg_rec_inline
//! 4 recursive function cannot be inline
let rec inline test (x : bool) : int =
    if x then test false else 0
printfn "%d" (test true)
