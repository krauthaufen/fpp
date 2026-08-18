// one type declaring the same member twice at one signature
module Neg_duplicate_member
//! 6 C already declares 'M' with this signature
type C() =
    member x.M () = 1
    member x.M () = 2
let c = C()
printfn "%d" (c.M ())
