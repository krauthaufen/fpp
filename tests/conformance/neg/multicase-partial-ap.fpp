// MULTI-CASE PARTIAL ACTIVE PATTERNS ARE NOT A THING, ported from
// dotnet/fsharp's Conformance/PatternMatching/Named/E_Error_NonParam02.fs
// and its five siblings (Param02/03, LetRec02/03, NonParam03), which are all
// one rule.
//
// A TOTAL pattern answers which case matched, and rides a Choice. A PARTIAL
// one answers whether it matched at all, and rides an option. `(|A|B|_|)`
// asks for both, and no return type is both — F# rejects it outright.
//
// Accepted here, the cases were registered against a Choice while every
// caller read an option. The trailing `_` is the whole difference: with one
// case it makes a legal partial pattern, and those still work — the positive
// side is in suites/activepat.fpp.
module Neg_multicase_partial_ap
//! 16 multi-case partial
let (|Foo|Bar|_|) (x : int) = if x > 0 then Some x else None
let f (v : int) = match v with | Foo n -> string n | _ -> "none"
printfn "%s" (f 1)
