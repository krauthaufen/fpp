// a union case must start uppercase (F#'s FS0053) — and here the compiler's
// own pattern rule reads a lowercase identifier as a BINDER whenever the
// case is out of scope, so a lowercase case silently stops matching
module Neg_union_case_lowercase
//! 6 must start with an uppercase letter
type Lst = cons of int | Nil
printfn "ok"
