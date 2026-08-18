// a static member called through an instance
module Neg_static_as_instance
//! 7 'S' is a static member of C — call it through the type
type C() =
    static member S () = 1
let c = C()
printfn "%d" (c.S ())
