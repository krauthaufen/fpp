// KNOWN ISSUE: an unresolved name in STATEMENT position takes its whole
// statement with it, silently.
//
// Five roots reach the backend unresolved on purpose (`Array`, `obj`,
// `Object`, `System`, `Unchecked`), and a use of one becomes a stub. In
// VALUE position the stub behaves as documented — it answers 0 and the
// first thing that reads it as a pointer traps:
//
//     let s = System.String cs      // traps at s.Length
//
// In STATEMENT position nothing traps and nothing runs. The call below
// never reaches `bump`, so the side effect is lost and the program prints
// n=0 twice with no diagnostic:
//
//     bump (System.String cs)       // vanishes
//
// `fpp build --strict` DOES report it ("stubbed … unsupported unknown
// System"), so the information exists — it is the default build that is
// silent. The conformance gate catches this class only because a suite's
// test COUNT is part of its contract: the unicode port lost a test this
// way and showed up as 66 against the oracle's 67.
//
// The fix is presumably to emit a trap rather than `lowInt 0` for an
// unsupported node, but that is a behaviour change at every stub site and
// wants its own pass. `System.String (chars)` itself is separately
// unimplemented — the prelude spells it `String.ofArray`, which F# does
// not have.
module UnresolvedNameInStatement

let mutable n = 0

let bump (s : string) : unit =
    n <- n + 1
    printfn "called with %s" s

let cs = [| 'a'; 'b' |]

printfn "before n=%d" n
bump (System.String cs)               // F#: "called with ab"; F++: nothing
printfn "after n=%d" n                // F#: n=1; F++: n=0
