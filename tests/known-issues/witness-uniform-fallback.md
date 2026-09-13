# 33 witness arguments go out UNIFORM, and the safety argument is DEAD

`FPP_WITSCAN=1` prints the count: 45 of 6986 witness arguments in fpp.dom's CE
build, 41 of 4677 in fpp.adaptive's. `FPP_WITSTRICT=1` names each site and
`FPP_WITWHY=<callee>` prints the parameter types, the argument types and the
witness registers the caller holds.

A uniform witness says "a traceable pointer, compare kind 5". The worry is
obvious: a generic argument could be a raw int or a struct, and describing it
as a pointer would have the collector chase it.

THAT WORRY IS CORRECT. This file used to answer it with an invariant —
"canonical (all-obj) code only ever meets canonical values" — and **2026-09-13
DISPROVED IT**. `CountingHashSet`'s `static let traceNoRefCount` was built once
at the canonical instantiation, so a `cset<int>` handed RAW ints to
`ComputeDelta$obj` and `ApplyDeltaNoRefCount$obj`: canonical code meeting raw
values, an untagged key in a tagged cell, and the collector tracing a small
integer as a pointer. `call-unnamed:trace` was in this very census while that
bug was live. The 2026-09-08 probe below found no counterexample; it was
looking in the wrong place, and absence of one is not the invariant.

So these sites are LATENT DEFECTS of a shape that has now bitten twice, not an
optimisation gap. Treat the count as a correctness budget.

The probe that went looking for a counterexample (sets and maps of ints and of
structs, hashed and compared through their identity members, through an `obj`
hop, and through generic `hashOf`/`eqOf` functions that never learn the
instantiation) answers correctly on all twelve cases, `--strict` clean. So does
`gcuniq-gate`, `byref-gate` under the semi shakeout, the adaptive suite's
19300 property cases and `noalloc-gate`.

FIXED SINCE: base-constructor arguments are now typed with the expected
parameter type flowing in, which closed the 6 `trace` sites (39 -> 33) at the
RIGHT instantiation. What remains, by family:

* 17 sites: generic UNIONS carry no per-instance witnesses. Identified
  concretely: the prelude's `Set.GetHashCode () = hash (x.Items ())` and
  `Map.GetHashCode () = hash (x.Pairs ())` with their `Equals` twins. Classes do
  (`WitnessedClasses`, read back by `selfWits`), but all cases of a union share
  ONE class-id, so the slots cannot sit after the fields the way a class' do —
  they would have to move ahead of the payload, relocating every field access,
  pattern match and refoffs map for that union.
* 6 sites (was 12): nullary generics whose witness lives in the callee's
  RESULT type. The `trace` half is FIXED — they were values passed to a base
  constructor, whose arguments were never inferred; `neg/inherit-arg-typechecked.fpp`
  pins the check. The `empty` half remains: module-level generic VALUES, still
  forced Canon by the value guard in `classify`.
* 4 sites (was 8): generic VALUES. Link now stamps a generic class' STATIC
  per instantiation, which ate half this family; the rest are module-level
  generic values, still forced Canon by the value guard in `classify`.
* 6 sites: lifted lambdas whose enclosing body has no witnesses either
  (`LamWits` already captures them when it does).
* 4 sites: `slot-freevar` and `call-notgeneric` tail.

Two attempts to derive the answer at the call site instead — an `EField` case
in `argTy`, and applying the definition-scheme fallback to inner calls — both
measured EXACTLY ZERO change and were reverted. The fix that did work (a use
carrying no scheme borrows the definition's, 54 -> 45) is in `7c74e8b`.
