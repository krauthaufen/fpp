# Compiler requests from fpp.shader (the FShade twin)

STATUS 2026-09-03: the session at 5391c1f GRANTED nearly everything below.
Verified against a build of that tree; fpp.shader deleted its interim
spellings accordingly. #37 fixed in e361c2b — verified, the sampler CE is
now 1:1 and NO interim spellings remain. Thank you. Still real at scale:
fpp.base #36 (GC %g trap — re-verified present on e361c2b; fpp.shader gates
run with FPPRT_HEAP_MB=512) and #30 (uint16, blocks C3us/C4us colors).

## Blocking 1:1 source parity

1. Record-field attributes (KNOWN-ISSUES #31) — GRANTED. `{ [<Semantic
   "Positions">] pos : V4d }` parses; the reifier reads real per-field
   attributes; [<FieldSemantics>] interim removed.
2. `(?)` dynamic-access operator — GRANTED. `uniform?Name` works (incl.
   cross-file); reifier lowers it to the uniform-read marker; `uniformValue`
   interim removed.
3. CE custom operations — GRANTED, incl. cross-file (e361c2b); was: NOT recognized
   ACROSS FILES, which is exactly fpp.shader's case (sampler builders live in
   the library, shaders in user files). The `sampler2d { ... }` CE is the
   ONE remaining interim (`sampler*Tex`); everything else is 1:1.
4. Stable function-value identity — GRANTED. `box f` is ReferenceEquals
   across boxings; `Effect.ofFunction f` now resolves by value (the
   generator registers `box <fn>` → key); `ofFunctionKey` kept as fallback.
5. Named attribute arguments — GRANTED. `[<LocalSize(X = 8, Y = 8)>]` parses;
   reifier + ComputeShader read named args; positional kept.

## Still open

37. **[<CustomOperation>] builders are not recognized across files** (new,
    KNOWN-ISSUES #37, repro banked) — the last blocker for the 1:1 sampler
    CE. Same-file works.
30. uint16/int16 conversions type as uint32/int (KNOWN-ISSUES #30) — blocks
    fpp.base's C3us/C4us colors (not fpp.shader).

## Infrastructure (lower priority; tool path works today)

6. External generator registration from .fppproj — an external-generator
   mechanism landed in 5391c1f; fpp.shader has not yet migrated its
   pre-build tool onto it (evaluated separately).
7. tastOf/TExpr fidelity — still bypassed via the green-tree walk (fine).
8. Per-expression source spans — for shader error messages (future).

## 2026-09-05: #36 recheck on your latest tree

Improved but not gone: fpp.shader's glsl gate now passes at the DEFAULT
heap; the larger backend2 gate still traps unpinned — wasm trap during a
printfn right after emitting `texture(arraySampler, vec3(...))` GLSL.
Repro: fpp.shader tests/backend2-run.sh with the inline
`--env FPPRT_HEAP_MB=512` removed. Pins stay in until this one is green.
