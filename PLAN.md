# F++ — Implementation Plan

Stages are strictly ordered by architectural risk, not feature glamour. Each
stage ends with something running in CI. Status legend: `[ ]` open,
`[~]` in progress, `[x]` done.

## Stage 0 — Skeleton & infrastructure
- [x] Repo, solution layout, CI-able test runner (Expecto)
- [~] Golden/snapshot test infrastructure
- [ ] Oracle harness: run a `.fs`-subset program under dotnet and under F++,
      diff stdout (activates end of Stage 4)

## Stage 1 — Lexer, lossless trees, LSP shell
- [x] Trivia-preserving lexer for the F# subset (round-trip property:
      concat of token texts == input, byte-for-byte)
- [x] Green/red lossless syntax tree infrastructure
- [x] Error-tolerant parser: modules, `let`, expressions, DUs, records,
      matches, offside rule, class/interface bodies, members (incl. static
      abstract + associated types), for/while, or-patterns, tuple lets;
      gate: zero diagnostics on the repo's own sources (CE bodies and
      record exprs remain lossless brace-soup, structured later)
- [x] Query engine core (Salsa-style: memoized queries, dependency tracking,
      invalidation on edit, early cutoff)
- [x] LSP server v0 as first query-engine client: diagnostics (syntax),
      document outline (`src/Fpp.Lsp`); `fpp check` CLI as second client
- Exit: open a `.fpp` file in an editor, see live syntax errors; parser
  round-trips the whole compiler's own source — REACHED (editor wiring
  is a client-side config away: `dotnet run --project src/Fpp.Lsp`)

## Stage 2 — Names & types (the long one)
- [x] Name resolution (modules, opens, shadowing) as queries — env-threading
      pass with module paths, exports/imports, `open`, qualified spine
      resolution; cross-file go-to-def; gate: whole compiler project (fsproj
      order) resolves + typechecks with zero diagnostics
- [~] HM inference core — v0 done: unification with levels (Rémy),
      let-generalization, schemes keyed by def-offset (resolver solves all
      scoping), DU/GADT constructor schemes, generic type params, same-file
      abbreviation expansion, ascriptions, literals/apps/ops/match/if/lists;
      typed hover; gate: ZERO type diagnostics on own sources. Open:
      deferred constraints (overloads/classes), records, member types,
      cross-file
- [ ] Overload resolution as its own specced algorithm
- [ ] Nominal subtyping, interfaces, classes
- [ ] GADT mode: per-case schemes, match refinement, existentials,
      escape diagnostics
- [ ] Kinds + HKT: `'m<_>` params, bare-constructor type args,
      `when 'm : Monad` constraints, spine unification, trailing-`_` sections
- [ ] Typeclass resolution: definition-site instances, conditional
      instances, associated types + injectivity
- [ ] LSP grows: hover types, go-to-def, find-refs
- Timebox rule: ship an ugly-but-honest solver first (annotations required
  in more places than ideal), reach running programs, then iterate inference
  quality against the oracle suite
- Exit: compiler's own source (common subset) typechecks

## Stage 3 — Typed core
- [x] Small typed core IR (`Core/Core.fs`) — binders/ctors carry schemes;
      dictionaries and GADT coercions arrive with the typeclass layer
- [x] Elaboration surface → core (`Core/Lower.fs`) for the v1 emission
      subset (functional core + records/DUs); out-of-subset constructs
      produce notes, never failures
- [x] Core linter (`Core/Lint.fs`): independent re-typecheck; gate:
      lint-clean on all sample programs AND on everything lowered from the
      compiler's own sources
- [x] REPRESENTATION.md: boxed/unboxed, structs, arrays, generics — the
      uniform-slot baseline + specialization plan (user requirement)
- Exit: REACHED — sample programs lower 100% note-free and lint-clean;
  next stop is the wasm-GC emitter consuming Core.Ir

## Stage 4 — First backend: wasm-GC
- [x] Core → wasm-GC lowering (`Backend/EmitWasm.fs`): uniform anyref repr,
      i31 ints, GC structs for records/DU cases/tuples/closures, $cons
      lists, i8-array strings via passive data, known-call fast path +
      curry wrappers, pattern compilation with br-chains, structural $equal
- [x] Runtime shims in emitted WAT: WASI fd_write putc/printi/prints,
      printval, equal, append, applyc
- [x] `fpp build -o out.wat` CLI; end-to-end tests run wasmtime and assert
      stdout (hello/factorial, DUs+closures+records+lists+equality,
      guards/tuples/negatives)
- [x] Oracle harness ACTIVE: programs run under dotnet fsi AND fpp+wasmtime,
      outputs diffed byte-exact — first catch: i31 overflow on fact 13,
      fixed by the box-spill
- [x] int32 box-spill ($ofi/$toi, normalize-on-box; full int32 wraparound
      semantics verified by the oracle)
- [x] tail calls (return_call in tail positions; oracle: 1M-deep loop)
- [ ] inner let rec, match-body tail positions, more oracle programs

## Stage 4.5 — Expanded mandate (user directive: "all of it")
- [ ] More F# surface area end-to-end: while/for loops, mutables, arrays,
      exceptions (try/with parse + raise/failwith semantics), string ops,
      printf-family formatting, CE bodies (structured, not soup)
- [ ] Linker: fat-IR library format (serialize Core.Ir), demand-closure
      instantiation fixpoint, tier-1 struct specialization, symbol dedup
      (see REPRESENTATION.md tiers)
- [ ] C FFI: extern declarations, wasm component/host imports on wasm,
      direct C ABI on native; blittable struct passing rules
- Exit: hello world through real programs run — REACHED

## Stage 5 — Stdlib & dogfood
- [ ] Prelude reimplemented in F++ (the bootstrap seam closes)
- [ ] Core collections, string, IO; Functor/Monad/Collection hierarchy
      proves out or gets revised
- [ ] Generic `monad<'m>` CE builder as the HKT showcase test

## Stage 6 — Self-host flip
- [ ] Compiler source compiles under itself (stage 2 binary)
- [ ] Fixpoint: stage2-compiled compiler recompiles source → byte-identical
      stage3; test pinned in CI forever
- Exit: dotnet becomes optional for development

## Stage 7+ — Native backend & beyond
- [ ] LLVM or Cranelift native backend, MMTk (Boehm to start)
- [ ] Monomorphization/unboxing optimization pass over uniform baseline
- [ ] Plugin (type-provider successor) declaration-IR + query endpoint API
- [ ] Scoped given-imports iff definition-site coherence proves too tight

## Standing decisions (see DESIGN.md for rationale)
- Query-based incremental compiler; LSP is client #1
- Written in the F#/F++ common subset; runtime touchpoints behind `Prelude`
- No type-level lambdas; kinds capped ~rank 2; associated types not fundeps;
  no orphans; uniform representation baseline
