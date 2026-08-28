// the ANNOTATION is right and the body is wrong, so the body is what the
// diagnostic must point at — it used to name the binder's line instead
module Neg_blame_annotation_body
//! 6 type mismatch: int vs string
let x : int =
    "s"
printfn "%d" x
