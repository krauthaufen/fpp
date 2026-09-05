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

## 2026-09-05 (later): #36 AND #30 FIXED

#36 root cause: an ENUM-typed field in an inline (POD) record was marked as
a REFERENCE leaf in the layout's refoffs (enum names were not in storLTy),
so the collector chased AsmState.selfStage's raw stage value during a
collection — heap-size-dependent, which is why 512 MB "fixed" it. Enum
names now resolve as scalar words in the layout. backend2-run.sh passes at
the DEFAULT heap; the 512 MB pins can come out.

#30: uint16/int16 conversions produce the narrow type itself now (they
shared the int/uint32 arm), with .NET truncation/sign-extension semantics
— verified byte-for-byte against dotnet fsi, conformance suite
`narrowconv` pins it. C3us/C4us are unblocked. NOTE: the repro header's
"expected 232" for `uint16 70000u` was a miscalc — fsi says 4464.

## 2026-09-05 (later): RESOLVED — #36 fixed on 546ba26

All fpp.shader gates pass without the 512 MB pins now. One residual worth a
look: the two LARGEST gate programs (tests/wgsl-run.sh, tests/webgl-run.sh)
still die at the 16 MB default heap with a bare `unreachable` (fine at
64 MB, kept there). If that is a clean out-of-memory, an "out of memory"
message instead of the bare trap would save the next person a bisect; if it
is a residual rooting case under extreme pressure, the repro is: strip the
`--env FPPRT_HEAP_MB=64` from either script. uint16 (#30) confirmed fixed
too — fpp.base is picking C3us/C4us up separately.

## 2026-09-05: external command generators ADOPTED

fpp.shader's reifier now runs via `generator <cmd>` in every gate project —
pre-build step and checked-in generated files deleted; all 11 gates green.
Protocol feedback from the adoption:
* `fpp build -o out <proj>` (flags first) silently treats the .fppproj as a
  SOURCE file and floods "unbound value 'name'" — a "did you mean
  `fpp build <proj> -o out`?" diagnostic would save the next person.
* The placement anchor (last type-declaring file) bit us once: generated
  code that references helper LETS from a types-free file (reflected.fpp)
  lands too early unless a type-declaring file follows. Worth a line in the
  docs, or an optional explicit anchor on the generator directive.
* Multi-module stdout files work — that made the single-output contract a
  non-issue. Progress chatter must go to stderr; also fine. 120s budget:
  our largest run uses well under half.
