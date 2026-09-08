# 45 witness arguments go out UNIFORM, and that is not (yet) a defect

`FPP_WITSCAN=1` prints the count: 45 of 6986 witness arguments in fpp.dom's CE
build, 41 of 4677 in fpp.adaptive's. `FPP_WITSTRICT=1` names each site and
`FPP_WITWHY=<callee>` prints the parameter types, the argument types and the
witness registers the caller holds.

A uniform witness says "a traceable pointer, compare kind 5". The worry is
obvious: a generic argument could be a raw int or a struct, and describing it
as a pointer would have the collector chase it.

MEASURED, 2026-09-08: it does not happen, because of an invariant worth
naming. **Canonical (all-obj) code only ever meets canonical values.** A value
with a RAW representation — a packed int array, an inline struct — exists only
inside a STAMPED clone, and there the witness is a compile-time constant from
the stamp, never the fallback. Every uniform fallback sits in a canonical body,
where the payload really is a tagged scalar or a pointer.

The probe that went looking for a counterexample (sets and maps of ints and of
structs, hashed and compared through their identity members, through an `obj`
hop, and through generic `hashOf`/`eqOf` functions that never learn the
instantiation) answers correctly on all twelve cases, `--strict` clean. So does
`gcuniq-gate`, `byref-gate` under the semi shakeout, the adaptive suite's
19300 property cases and `noalloc-gate`.

So driving the count to zero is an OPTIMISATION — precise witnesses would let
raw representations reach places that are uniform today — not a correctness
fix. What it would take, by family:

* ~15 sites: generic UNIONS carry no per-instance witnesses. Classes do
  (`WitnessedClasses`, read back by `selfWits`), but all cases of a union share
  ONE class-id, so the slots cannot sit after the fields the way a class' do —
  they would have to move ahead of the payload, relocating every field access,
  pattern match and refoffs map for that union.
* 12 sites: nullary generics (`trace`, `empty`) whose witness lives in the
  callee's RESULT type. Needs the instantiation recorded upstream, in Infer or
  Lower — the change with the widest blast radius, since it feeds
  monomorphization.
* 8 sites: generic VALUES, which have no parameters and no caller. Needs Link
  to stamp values per instantiation the way it stamps functions.
* 6 sites: lifted lambdas whose enclosing body has no witnesses either
  (`LamWits` already captures them when it does).
* 4 sites: `slot-freevar` and `call-notgeneric` tail.

Two attempts to derive the answer at the call site instead — an `EField` case
in `argTy`, and applying the definition-scheme fallback to inner calls — both
measured EXACTLY ZERO change and were reverted. The fix that did work (a use
carrying no scheme borrows the definition's, 54 -> 45) is in `7c74e8b`.
