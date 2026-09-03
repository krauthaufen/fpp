// no known body to copy to the call site
module Neg_abstract_inline
//! 6 cannot be inline
[<AbstractClass>]
type Bad =
    abstract inline X : int
printfn "ok"
