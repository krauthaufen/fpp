// A CANONICAL BODY'S CLASS CONSTANT NEVER RESOLVES: the prelude's
// `RangeOps.Seq (lo : 'a, hi : 'a) when Num<'a>` keeps `$class:Num:One:#1752`
// in its UNSTAMPED copy, and the backend records it on the quiet channel
// ("quietstub ... unsupported unknown $class:Num:One:#N"). Two of them are in
// any fpp.dom or fpp.adaptive build.
//
// NOT REACHED, as of 2026-09-08. Every call below answers correctly (5, 3, 5)
// because each one lands on a STAMPED copy, where the marker is mapped at
// stamping. The canonical copy is emitted and never entered — the same shape
// as the empty vtable rows next door, and the same caveat: if a program ever
// DOES reach it, it traps, and `--strict` will not have said so.
//
// Fixing it means resolving the marker in the canonical copy too — where `'a`
// is genuinely unknown, so the constant would have to come from a witness
// rather than from the stamp. See CLAUDE.md's class-constant section for the
// history of this marker family.
module CanonicalClassConstant
// RangeOps.Seq's CANONICAL copy stubs on `$class:Num:One:#N`. Is it reachable?
let span (lo : 'a) (hi : 'a) : int when Num<'a> when Ordered<'a> =
    List.length [ lo .. hi ]
let a = printfn "%d" (span 1 5)
let b = printfn "%d" (span 2.0 4.0)
let c = printfn "%d" (List.length [ 1 .. 5 ])
