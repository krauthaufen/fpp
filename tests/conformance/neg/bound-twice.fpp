// A NAME MAY BIND ONLY ONCE IN ONE PATTERN, ported from dotnet/fsharp's
// Conformance/PatternMatching/Named/E_IdentBoundTwice.fs.
//
// `match (1, 2) with (x, x) -> x` used to answer 2: the second binder
// silently won. Nobody writes that meaning "whichever comes last" — they
// mean "both elements are equal", which is not what a pattern says in this
// language — and F# rejects it (FS0038) rather than choosing.
//
// The check is a walk of its own, NOT part of the type walk, because
// or-alternatives are sibling patterns that share one binder table on
// purpose: `| A x | B x ->` binds `x` on both sides and must. Each
// alternative is counted alone, so the legal form stays legal — the
// positive side of that is in suites/patterns.fpp.
module Neg_bound_twice
//! 17 bound twice
//! 18 bound twice
let f (p : int * int) = match p with | (x, x) -> x
let g (p : int * int) = match p with | (a, _) & (_, a) -> a
printfn "%d %d" (f (1, 2)) (g (3, 4))
