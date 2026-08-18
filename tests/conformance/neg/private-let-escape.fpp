// a module-private let used from a sibling module
module Neg_private_let_escape
//! 8 'hidden' is private to module Neg_private_let_escape.A
module A =
    let private hidden = 42
    let visible = 1
module B =
    let peek = A.hidden
printfn "%d" B.peek
