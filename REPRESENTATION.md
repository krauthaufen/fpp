# F++ — Value Representation

How values are laid out at runtime, per backend. The core constraint (from
DESIGN.md): GADTs force polymorphic recursion, so whole-program
monomorphization is off the table — there must always be a **uniform
representation** every value can fall back to. Monomorphization and unboxing
are *optimizations over* that baseline, never the semantics.

## The uniform slot

Every value fits one uniform slot:

- **wasm-GC**: `anyref`. Heap values are GC structs/arrays; small ints ride
  in `i31ref` (see below).
- **native (later)**: one machine word, OCaml-style low-bit tagging —
  pointers are aligned, immediates carry tag bit 1.

Polymorphic code (`'a` positions, GADT payloads, dictionary-passing class
methods) always works on uniform slots. Code with statically known types
works on unboxed machine values and boxes only at uniform boundaries.

## Primitives

- **int is int32 with F# semantics** (wrap-around, exact width). Unboxed
  `i32` in known contexts. In a uniform slot: values fitting 31 bits go in
  `i31ref`, the rest box — normalize on boxing, so equality of the two forms
  never diverges. Native: 63-bit immediate with the same spill-box rule.
- **int64 / float**: unboxed in known contexts; boxed in uniform slots.
  We do **not** repeat OCaml's magic float-array special case; float
  performance comes from specialization (below), not representation hacks.
- **bool / char / unit**: immediates (i31 / tagged word). `char` is a
  Unicode scalar value, 21 bits, always immediate.
- **string**: immutable **UTF-8** bytes + cached length.
  ⚠ OPEN DECISION: this breaks .NET's UTF-16 `s.[i]`/`s.Length` code-unit
  semantics. Recommendation: accept the break — `string` indexes by byte,
  `Rune`-based iteration in stdlib — and audit Prelude when the seam closes.
  The alternative (UTF-16 for F# compat) buys compat we don't owe anyone.

## Records, unions, tuples

- **Records**: wasm-GC `struct` with one field per record field (unboxed
  where the field type is statically primitive, uniform otherwise). Native:
  heap block. First slot: vtable (see equality).
- **DUs**: one abstract supertype per union; one struct subtype per case
  (wasm-GC subtyping does the case test via `ref.test`). Nullary cases are
  preallocated singletons. Payload fields typed like record fields. GADT
  cases: same layout — the refinement is a compile-time fact, the payload is
  uniform wherever the per-case signature has variables.
- **Tuples**: anonymous structs, same as records. Flattening into locals in
  monomorphic contexts is an optimization pass.

## Structs (value types)

Key observation: for **immutable** data, copy-semantics vs
reference-semantics is unobservable — so `[<Struct>]` records/DUs get the
same heap representation as their boxed cousins in v1, at zero semantic
cost. The observable difference only appears with mutable struct fields;
those are **rejected in v1**. True flat/inline/stack struct layout arrives
later as an escape-analysis + monomorphization optimization, not as a
representation commitment.

## Arrays

- `'a[]` in polymorphic positions: wasm-GC array of uniform slots.
- Arrays created at statically primitive element types (`int[]`, `float[]`,
  `byte[]`) use unboxed payload arrays — distinct runtime array types.
- Polymorphic code receiving an array dispatches on the array's runtime
  type (`ref.test` chain / vtable) for load/store. Numeric hot loops are
  expected to be monomorphized, which erases the dispatch entirely.

## Generics

- Baseline: **erased to uniform slots**. No runtime type tokens, no
  reification; `typeof` is dropped from the language (spec keep/drop table).
- Constraints (future typeclasses, static interface members): **implicit
  dictionary parameters** (DESIGN.md) — a dictionary is an ordinary record
  of functions/values in this same representation.
- **Monomorphization is a directed optimization**: visible instantiations
  may be cloned and unboxed; polymorphic recursion / HKT / escaping
  polymorphism silently stay on the uniform path. Correctness never depends
  on specialization succeeding.

## Closures & currying

Closure = struct { code : funcref; env fields... }. Multi-argument functions
compile with known-arity fast paths; the curried uniform entry point exists
for higher-order/polymorphic call sites. Known direct calls skip the
closure entirely.

## Equality, hashing, comparison

Structural, with **per-type generated functions** installed in the type's
vtable (slot 0 of every boxed value). `=` on `'a` calls through the value's
vtable — no reflection, no runtime type walking. Once typeclasses land,
these become ordinary `Eq`/`Ord`/`Hash` dictionaries; the vtable slot is the
pre-typeclass bridge and remains as the default-instance fast path.

## What the typed core must carry (consequences for Stage 3)

- Types on every binder (done — inference schemes).
- Union/record declarations with field/payload types (for struct layout).
- Distinguished prim ops (int vs float arithmetic resolved by type).
- Boxing is **not** represented in core — it is inserted during emission
  from type information (uniform boundary crossings are computable there).
