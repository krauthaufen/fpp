// a pattern naming a case the union does not declare.
//? fsc-accepts — F# BINDS an unresolvable uppercase pattern ident (warning
// FS0049); F++'s rule is that an uppercase pattern ident never binds, so an
// unknown case is an error (see DIVERGENCES.md)
module Neg_unknown_union_case
//! 11 unknown case 'C'
type U = A of int | B
let f (u : U) =
    match u with
    | A x -> x
    | C -> 1
    | B -> 2
printfn "%d" (f B)
