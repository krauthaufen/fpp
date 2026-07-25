# F++ — Value Representation

**NORMATIVE INVARIANT (user requirement, gate-tested):** structs and
primitives are NEVER boxed unless mathematically unavoidable (tier-3:
polymorphic recursion / first-class polymorphism), and flat layouts are the
ONLY layouts — no runtime representation dispatch. Vector types (V2d etc.)
are the primary workload; `V2d[]` is SoA-flat (one typed field-array per
field), `int[]`/`float[]`/... are typed scalar arrays, and generic array
access without a statically known element type is a compile-time error
until specialization serves it. The remaining transient boxing at the
expression layer (locals/temporaries) is scheduled for deletion via typed
emission — see Stage 4.5.

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
- **int64**: unboxed `i64` in known contexts (native wasm arithmetic, same
  cost as int). Uniform slots: values fitting 31 bits ride `i31` (no
  type-confusion risk — static typing means int and int64 never share a
  polymorphic slot), the rest spill to `$boxl (struct i64)`, normalize-on-
  box like `$ofi`. Native: 63-bit immediates make the spill nearly
  extinct — better than OCaml's always-boxed Int64.
  ⚠ CURRENT GAP: `42L` is silently computed in i32 — int64 is a queued
  feature; until then the suffix is a trap the oracle would catch.
- **float**: unboxed in known contexts; boxed in uniform slots.
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
  preallocated singletons. Payload fields typed like record fields.
- **GADT cases**: same layout. The refinement (`Expr<int>` vs `Expr<bool>`)
  is compile-time knowledge — at runtime only the case tag exists. Concrete
  payload positions (`Lit : int -> Expr<int>`) are unboxed like any field.
  Uniformity is forced ONLY at type-variable positions reachable through
  polymorphic recursion or existentials — the precise place where boxing
  must exist in principle. Even there the tier-3 witness upgrade applies:
  small structs inline in an opaque buffer (Swift existential-container
  style), large ones spill — the eventual cost floor is a witness memcpy,
  not an allocation. A GADT used at concrete instantiations without
  polymorphic recursion is just a DU and specializes under tier 1.
- **Tuples**: anonymous structs, same as records. Flattening into locals in
  monomorphic contexts is an optimization pass.

## Structs (value types) — first-class, C layout everywhere

**NORMATIVE (user requirement): every POD struct has exactly one layout —
the C ABI layout** (field offsets by natural alignment, struct alignment =
max field alignment, size rounded up; what clang would compute). Every
memory materialization uses it: arrays (linear AoS), buffers, nested
structs (inlined at their C offsets), FFI (pointer or by-value per C ABI).
The only permitted deviation mirrors C compilers themselves: values in
locals/params may be scalarized into registers until materialized in
memory. Field size table v1: int 4, float32 4, float 8, int64 8 (bool/char
widths to be fixed with the C type-mapping table when bindgen lands).
GC-heap struct encodings are temporaries, never the memory truth.

**Requirement (explicit):** structs are first-class citizens; boxing only
where specialization is impossible in principle.

Structs are flat value types: unboxed in locals, parameters, returns,
record/DU fields, and arrays whenever the code path is specialized or the
type is statically known — which tiers 1–2 of the generics scheme (below)
make the common case. A struct boxes ONLY at tier-3 boundaries, and the
compiler can report where.

- wasm-GC note: "unboxed" there means flattened into the enclosing
  struct/array/locals rather than a separate allocation; wasm-GC has no
  interior pointers, so struct arrays flatten fields into the array payload.
- Native note: true flat layout in registers/stack/inline fields, C-style.
- Mutable struct fields: deferred until the emitter enforces copy
  semantics; immutable structs meanwhile share representation soundness
  by construction (copy vs reference unobservable).

## Linear-memory lifetimes (struct arrays / buffers)

wasm-GC has NO finalizers and NO weak refs — the engine collects a
{ptr,len} handle silently; nothing can free the linear block from inside
the module. Layered answer:

- **Handle uniqueness (invariant)**: exactly one GC handle per linear
  block, created at allocation, never duplicated (F# arrays alias by
  reference anyway). Handle death == block death; free exactly once.
- **JS hosts**: FinalizationRegistry — allocation notifies the host via a
  tiny import; the registry frees on collection (best-effort timing; fine
  for memory, never for scarce resources).
- **First-class story: deterministic lifetimes** — arenas (per-frame
  regions, bump-alloc, wholesale free: the natural shape of geometry
  workloads) and `use`/IDisposable for individual buffers. v1: bump
  allocator, program-lifetime blocks.
- **Native backend**: problem disappears — our GC (MMTk/Boehm) has real
  finalization.
- Watch: wasm-GC post-MVP finalization/weak-ref proposals.

## Arrays

- `'a[]` in polymorphic positions: wasm-GC array of uniform slots.
- Arrays created at statically primitive element types (`int[]`, `float[]`,
  `byte[]`) use unboxed payload arrays — distinct runtime array types.
- Polymorphic code receiving an array dispatches on the array's runtime
  type (`ref.test` chain / vtable) for load/store. Numeric hot loops are
  expected to be monomorphized, which erases the dispatch entirely.

## Buffers — linear memory for interop (planned)

wasm-GC modules carry BOTH heaps: the GC heap (structs, flat arrays —
opaque to hosts) and linear memory (exported; JS sees an ArrayBuffer with
zero-copy TypedArray views; views detach on grow). Two array flavors:

- **Managed arrays** (default): GC-flat as specified above.
- **`Buffer<'T>`** (T scalar or flat struct): contiguous bytes in linear
  memory. F++ access compiles to raw load/store (typed emission); the same
  bytes are directly a Float64Array in JS / a WebGPU upload source — zero
  copies for bulk vector data (the primary workload).
- Unification: on native, linear memory is malloc — `Buffer<'T>` is ALSO
  the C FFI array representation (pointer + length into a .so). One
  abstraction serves WebGPU and C interop.

## Generics — three tiers (decided)

Survey of prior art that shaped this: C++ (templates + COMDAT linker
dedup), Rust (generic MIR shipped in rlibs, instantiated downstream,
symbol-hash dedup), .NET (specialize per value type, share `__Canon` for
all reference types; NativeAOT does it ahead of time), Swift (unspecialized
generic code over value-witness tables — no boxing even unspecialized),
MLton (whole-program mono; possible only because SML lacks polymorphic
recursion), Zig/D (comptime). GADTs force polymorphic recursion on us, so
full monomorphization is impossible *in general* — but that only dictates
the fallback tier, not the common case.

- **Struct-array layout (FINAL — GC-managed C-image AoS)**: default
  arrays are ordinary GC values — no finalizers, no disposal, no arenas
  (user requirement). Representation: the struct's exact C byte image
  packed into a GC `(array (mut i64))` — C natural alignment guarantees no
  field of size <=8 straddles an 8-byte word, so clang-exact offsets map
  onto words: f64 via i64.reinterpret_f64, 4-byte fields sharing words via
  shift/mask (all register ops; zero-alloc access preserved, ps.[i].X =
  one array.get + reinterpret). FFI/JS/GPU boundary = straight block copy
  into linear staging (the .NET blittable-marshalling model; the image is
  already C-exact so the copy is a dumb word loop, never per-field). For
  copy-intolerant hot paths, `Buffer<'T>` (linear memory, zero-copy,
  explicit lifetime) is the OPT-IN — the special case, not the default.
  (Superseded design below kept for the record:)
- **Struct-array layout (superseded — linear-by-default)**:
  layout IS semantics at FFI boundaries; `V2d[]` must BE C layout. The
  emscripten model, adopted: **POD struct arrays live in LINEAR MEMORY,
  byte-exact C layout** — contiguous interleaved fields with C
  sizes/alignment. The array value is a GC handle `{ptr:i32; len:i32}`;
  element/field access compiles to raw typed load/store at
  `ptr + i*sizeof + offset` (composes with typed emission — allocation-
  free hot loops, now on true AoS). C FFI receives `ptr` directly; JS gets
  zero-copy TypedArray views. `Buffer<'T>` and struct arrays UNIFY — one
  concept. Ref-containing structs cannot live in linear memory (GC cannot
  trace it — same boundary emscripten has by having no refs at all); they
  keep a GC-side layout, and are exactly the structs C interop is
  meaningless for. Allocator: bump v1 → free-list/RC later; JS hosts may
  assist via FinalizationRegistry. Primitive arrays may stay GC-flat
  ($parr_*) or move to linear per the same rule — linear preferred for
  FFI-facing data. (Background: emscripten/Rust/TinyGo have trivial
  interop precisely because everything is linear memory; the GC-heap
  layout problem was self-inflicted.)
- **Generic containers of structs flatten**: `list<MyStruct>` stamps a
  cons cell with MyStruct's fields INLINE in the node (one allocation per
  node, zero boxing); `MyStruct[]` is a flat field-group array. Escape
  rule (v1): construction sites whose values can reach tier-3 positions
  (conservative escape check) build the uniform representation instead,
  with a compiler note; the witness-table endgame deletes this fallback
  by making tier-3 code layout-agnostic. Boxing is a property of program
  points, never of types — and all such points are enumerable at link.
- **Tier 1 — specialized per struct instantiation.** Library "objects" are
  serialized typed Core IR (fat rlibs, Rust-style): the generic's IR *is*
  the template; instantiation = type substitution + ordinary code gen. The
  F++ link step — ours, type-aware — computes the demand closure as a
  fixpoint from the roots (stamping may transitively demand more),
  deduplicates by mangled instantiation identity, and binds call sites,
  vtable slots and dictionary entries to the stamped symbols. Demands flow
  across library boundaries in both directions (library generic at an
  app-defined struct works: layout travels with the type in IR). Libraries
  may pre-stamp instances for their internal uses; the final link stamps
  the rest. `Map<Vec2,_>` gets real flat `Vec2` code.
- **Tier 2 — one shared body for ALL reference-type instantiations** (the
  .NET `__Canon` insight). References are uniform already; sharing kills
  the C++/Rust bloat problem for the majority of instantiations.
- **Tier 3 — fallback where specialization is impossible in principle**:
  polymorphic recursion (GADTs), HKT-generic code, first-class polymorphic
  values. v1: box structs at this boundary (with a compiler note).
  Upgrade path: Swift-style value-witness tables remove even that boxing
  later with no semantic change — the design keeps that door open.
- No runtime type tokens, no reflection; `typeof` stays dropped. Runtime
  instantiation can never be demanded (no `MakeGenericType`), so the
  link-time closure of instantiations is complete except through tier 3 —
  which is exactly what tier 3 is for.
- Constraints (typeclasses, static interface members): **implicit
  dictionary parameters**; in tier-1 code the dictionary is resolved
  statically and inlined away, in tiers 2–3 it is a real record argument.

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
