// A CONTROL CONSTRUCT NEEDS ITS BUILDER METHOD, ported from dotnet/fsharp's
// Conformance/Expressions/DataExpressions/ComputationExpressions —
// E_MissingFor and its ten siblings (Yield, YieldFrom, Return, ReturnFrom,
// Zero, Combine, While, Using, TryWith, TryFinally), which are all one rule.
//
// A computation expression is a REWRITE into calls on the builder, so `for`
// becomes `builder.For(...)` and means nothing if the builder has no `For`.
// F# says so (FS0708). Here the rewrite emitted the call anyway: it compiled
// clean and the module TRAPPED when the construct was reached — a compile-
// time diagnostic arriving at run time, and only if that line ran.
//
// The check lives in the rewrite, because that is the only pass that knows
// which constructs a CE used. It cannot live where missing members are
// normally reported: the rewrite's own tokens are synthetic (above
// 500000000) and that diagnostic deliberately ignores them, since blaming a
// position the author never wrote is worse than saying nothing. So the
// builder record carries the CE's own offset and the error lands there.
module Neg_ce_missing_method
//! 24 defines a 'For' method
//! 24 defines a 'Yield' method
type B() =
    member _.Return (x : int) = [ x ]
let b = B()
let r = b { for i in [ 1; 2 ] do yield i }
printfn "%d" (List.length r)
