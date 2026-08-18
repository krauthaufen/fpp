// A later `type foo()` shadows an earlier value `foo` ENTIRELY: the value
// is no longer nameable, so applying the old signature must be rejected
// (F# gives FS0501: the object constructor takes 0 arguments).
module NegShadowCtor
let foo (x : int) = x + 1
type foo() =
    member x.P = 17
let z = foo 1
//! 8 type mismatch
