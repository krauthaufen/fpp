// %d takes any integer WIDTH (the recorded kind decides at expansion), so
// the hole is polymorphic — and a type outside the family entirely fell
// through every kind to the "?" renderer: `%d` swallowed a ByRefCell and
// printed a question mark. Judged after inference, like the null literals.
module Neg_printf_int_hole_wrong_type
//! 8 expects an integer
type R = { V : int }
let go = printfn "%d" { V = 1 }
printfn "ok"
