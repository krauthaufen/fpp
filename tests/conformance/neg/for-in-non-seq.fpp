// iterating something that is not a sequence
module Neg_for_in_non_seq
//! 5 not lowerable: for-in (no GetEnumerator on the source)
let mutable n = 0
for x in 3 do
    n <- n + x
printfn "%d" n
