// or-alternatives rebind one name and must agree on its type: bound at int
// in one arm and float in the other, `string x` answered off the wrong
// representation with no diagnostic anywhere
module Neg_orpat_binder_types
//! 8 type mismatch
let test (p : int * float) =
    match p with
    | x, 0.0
    | 0, x -> "mixed " + string x
    | _ -> "other"
printfn "%s" (test (3, 0.0))
