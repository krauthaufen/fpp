// A type with only members has NO constructor: `C()` must be rejected
// (F# gives FS1133), not build a ghost object whose members read zero.
module NegNoCtor
type C =
    member x.P = 5
let c = C()
//! 6 no constructors are available
