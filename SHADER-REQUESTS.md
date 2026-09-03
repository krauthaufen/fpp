# Compiler requests from fpp.shader (the FShade twin)

STATUS 2026-09-03: the session at 5391c1f GRANTED nearly everything below.
Verified against a build of that tree; fpp.shader deleted its interim
spellings accordingly. One follow-up remains (#37).

## Blocking 1:1 source parity

1. Record-field attributes (KNOWN-ISSUES #31) — GRANTED. `{ [<Semantic
   "Positions">] pos : V4d }` parses; the reifier reads real per-field
   attributes; [<FieldSemantics>] interim removed.
2. `(?)` dynamic-access operator — GRANTED. `uniform?Name` works (incl.
   cross-file); reifier lowers it to the uniform-read marker; `uniformValue`
   interim removed.
3. CE custom operations — GRANTED same-file, but see #37: NOT recognized
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
