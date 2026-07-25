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
- [~] Trivia-preserving lexer for the F# subset (round-trip property:
      concat of token texts == input, byte-for-byte)
- [ ] Green/red lossless syntax tree infrastructure
- [ ] Error-tolerant parser: modules, `let`, expressions, DUs, records,
      matches, offside rule
- [ ] Query engine core (Salsa-style: memoized queries, dependency tracking,
      invalidation on edit)
- [ ] LSP server v0 as first query-engine client: diagnostics (syntax),
      document outline, formatting stub
- Exit: open a `.fpp` file in an editor, see live syntax errors; parser
  round-trips the whole compiler's own source

## Stage 2 — Names & types (the long one)
- [ ] Name resolution (modules, opens, shadowing) as queries
- [ ] Constraint-based HM inference: generate + solve with deferral
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
- [ ] Small typed core IR: explicit dictionaries, explicit GADT coercions,
      kinds
- [ ] Elaboration surface → core
- [ ] Core linter (re-typecheck after every pass), on in CI always
- Exit: every green Stage-2 test elaborates to lint-clean core

## Stage 4 — First backend: wasm-GC
- [ ] Core → wasm-GC lowering (uniform boxed representation)
- [ ] Minimal runtime shims (strings, arrays, exceptions story v0)
- [ ] Execute tests under wasmtime/node in CI
- [ ] Activate the oracle harness: dotnet vs F++ differential tests
- Exit: hello world through real programs run; oracle suite green

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
