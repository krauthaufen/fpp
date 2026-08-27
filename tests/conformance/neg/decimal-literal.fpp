// the `m` suffix is System.Decimal, a base-TEN type this compiler does not
// have. Read as a float it answered 0.30000000000000004 for 0.1m + 0.2m.
module Neg_decimal_literal
//! 5 decimal is not supported
let a = 0.1m
let b = 0.2m
printfn "%s" (string (a + b))
