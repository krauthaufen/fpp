// a qualified case pattern naming a case the type does not have. It used to
// record nothing and lower to a WILDCARD, so the arm matched everything.
module Neg_unknown_qualified_case
//! 8 unknown case 'Purple'
type Colour =
    | Red
    | Green
let f (c : Colour) = match c with Colour.Red -> "r" | Colour.Purple -> "p" | _ -> "?"
printfn "%s" (f Colour.Red)
