# Compiler requests from fpp.shader (the FShade twin)

fpp.shader (github krauthaufen/fpp.shader) is complete and gated, but five
language gaps force interim spellings where FShade sources should compile
letter-for-letter, and three infra wishes would let its tooling move into
the compiler. Repros for the numbered snags are in fpp.base's
tests/known-issues/ (KNOWN-ISSUES.md, mirrored at ~/claude/fpp-base-snags.md);
the running detail file is ~/claude/fpp-shader-hooks.md.

## Blocking 1:1 source parity (each has an interim spelling today)

1. **Record-field attributes don't parse** (fpp.base KNOWN-ISSUES #31) —
   `{ [<Semantic "Positions">] pos : V4d }` is rejected; attributes on lets
   and types are fine. Interim: type-level `[<FieldSemantics "pos=…;…">]`.
   The most visible gap: every FShade vertex type uses field attributes.
2. **No `?` dynamic-access operator** — FShade's `uniform?Name` /
   UniformScope extension members via `(?)`. Interim: `uniformValue x "Name"`.
   A `(?)` desugaring to a string-indexed call restores parity.
3. **No CE custom operations** (`[<CustomOperation>]`) — the
   `sampler2d { texture …; filter … }` builder syntax. Interim: record-based
   `sampler2dTex`.
4. **Function values have no stable identity** (`box f` twice is not
   reference-equal), so `Effect.ofFunction f` cannot key the reflected-
   definition table by value. Interim: `Effect.ofFunctionKey "Module.name"`.
   Either stable identity for top-level function values, or a rewrite hook.
5. **No named attribute arguments** — donor spells `[<LocalSize(X = 8)>]`;
   only positional `[<LocalSize(8, 8, 1)>]` parses.

## Infrastructure (works today via an external tool linking Fpp.Compiler)

6. **Generator registration from project config** (`generator <asm|cmd>` in
   .fppproj) — moves the shader reifier from a pre-build tool into the
   compiler's own Generator pipeline.
7. **tastOf/TExpr fidelity** — structured match patterns, imperative bodies,
   record literals (today: TOther / stringly); the tool bypasses tastOf by
   walking the green tree + ExprTypes + BindResult directly.
8. **Per-expression source spans** exposed alongside types — for shader
   error messages that point at user code.

## Fixed-workaround snags a fix would simplify

fpp.base KNOWN-ISSUES #32 (tuple active patterns silently fail cross-file),
#33/#35 (union-case miscompiles: case named like a type; last payload of a
multi-payload case corrupted at program scale), #36 (GC-at-scale %g trap —
fpp.shader's gates pin FPPRT_HEAP_MB=512), #30 (uint16 conversions type as
uint32 — blocks fpp.base's C3us/C4us colors, not fpp.shader).
