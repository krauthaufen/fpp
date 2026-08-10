# LowIR — a shared machine IR for the linear/tagged backends

The C backend (`CEmit`, over fpprt) and the direct wasm-linear backend
(`WasmLin`) re-implement the same lowering: lambda lifting, closure
representation, pattern-match compilation, the tagged value model, f64/i64
boxing, and record/union/array/list layout. Two copies of one meaning drift,
and neither has a place to put a representation-aware optimisation. LowIR is
that shared substrate: Core lowers to it once, the backends select
instructions from it, and optimisations are LowIR→LowIR passes.

The wasm-GC backend (`BinDriver`) is deliberately NOT a LowIR client. It is
the self-host oracle and uses a different value model (engine GC structs,
arrays and `i31ref`, not a tagged word in linear memory). It stays as it is.

## The idea

A value in LowIR is a machine word `W` — a tagged value or a raw pointer:
`i32` on wasm-linear, `intptr_t` in C — or a wide payload (`I64`/`F64`) that a
box holds. Crucially, **there are no tag/box/unbox primitives**. Tagging a
31-bit int is `shl` + `or`; boxing an `f64` is `alloc 8` + `store` + the
pointer. Core→LowIR expands those, so LowIR is honest machine work and nothing
below it has to know the value model — which is exactly what lets one IR feed
the C backend, this wasm-linear backend, and an eventual native backend the
same way.

- **Optimisations** become LowIR→LowIR transforms: box elimination, "don't
  materialise a struct for a POD", alloc sinking — the representation-aware
  ones that have no home in the type-directed `Core/Optimize.fs`.
- **Backends** are instruction selection. The C backend needs NO register
  allocation (C locals are virtual registers; gcc allocates). The wasm-linear
  backend colours LowIR registers into local slots by liveness. A future
  x64/arm64 backend slots in as one more selector, with real register
  allocation and spilling as the only new machinery — everything above it
  (closure conversion, match compilation, layout, the opt passes) is shared.

## Native, and where wasm-linear fits

"Compile wasm-linear to native" is already true via wasmtime AOT (`fpp exe`
embeds it and Cranelift compiles the module to machine code). So wasm-linear
is both an execution/distribution target AND, through wasmtime, the pragmatic
native story today — no new backend. But wasm bytecode is a poor IR to
*optimise* on (a stack machine with structured control flow), so the
optimisations still live on LowIR. A direct LowIR→x64/arm64 backend is pure
upside later, only if the wasmtime dependency is worth shedding — not a
prerequisite.

## Status: the whole gate program lowers through LowIR

`Core/LowIR.fs` defines the IR (`LExpr`/`LStmt`/`LFunc`, the `LOp` ALU, `LTy`,
`LReg`). `WasmLin.fs` gained a Core→LowIR lowering (`coreToLowE`/`coreToLowS`
plus `lowObj`/`lowList`/`lowBoxF`/`lowBoxI`/`lowPatTest`/`lowClosure`/
`lowApply`, tag/box expanded here) and a LowIR→wasm emitter (`emitLowE`/
`emitLowS`, `emitFuncLow` for top functions and inits, `emitLambdaLow` for
lifted lambda bodies). `fpp build --lowir` routes a body through LowIR where a
`lowSupported` predicate says the whole body is in the covered subset, and
**falls back to the hand-lowering `lower` otherwise** — the two paths coexist
in one interoperating module (a LowIR-built closure and a hand-lowered body
share one ABI), so output can never regress. `FPP_LOWIR_STATS=1` reports how
many bodies took each path.

Covered subset: integers, floats and int64 (boxed wide payloads), arithmetic /
comparison / conversions, `let`/`let mutable` and globals, top-level functions
with direct calls and recursion, `if`/`elif`/`while`/assignment/sequencing,
records, unions, tuples, arrays (`.[]`, `.Length`, `zeroCreate`/`create`),
`match` (literals, constructors, tuples, cons, `[]`, `as`, wildcards, guards),
lists, options, closures / higher-order functions / indirect calls, string
literals, int-to-string, `%f` formatting, concat, `printfn`, and `failwith` &
friends (trap). Registers are one wasm local per `LReg` (no liveness colouring
yet — that IS the register-allocation pass, still to come).

The nesting-safe scratch pools the hand path needs (`$ab`/`$pt`/`$ms`/`$fd`…,
indexed by allocation/match/box depth) FALL AWAY: every allocation, match
temp and box gets a fresh `LReg`, so nesting safety is structural.

Gated by `tests/tooling/cback/lowir-gate.sh`: a WHOLE-LANGUAGE program
(recursion, while/mutable, records, unions, tuples, arrays, match, lists,
options, floats, int64, closures, HOFs) is built with `--lowir`, the stats are
asserted to show **zero fallbacks** (every function, init and lambda body took
the LowIR path), and the output is diffed against the wasm-GC oracle — a THIRD
independent emission path agreeing on one meaning, with `lower` proven unused
on the whole-language program. Both `fixpoint.fsx` and `fixpoint.fsx self`
reproduce byte-for-byte with the new code among the compiled sources.

**`lower` is DELETED.** LowIR is the sole wasm-linear lowering — `--linear`
routes every body through it, and the ~590-line hand-lowering (`lower`,
`buildObj`, `emitPatTest`, the box/closure helpers, the depth-indexed scratch
pools) is gone, along with the `St` fields that served it. It turned out
`lower` covered *exactly* what LowIR covers — both errored on the same nodes —
so retiring it needed no new ports, only proving the equivalence. The compiler
shrank ~29 KB (the duplicate lowering is no longer among the compiled sources).

The nodes neither path ever handled on this leg — exceptions (`ETry`),
typeclass dispatch (`EIfaceCall`), casts / type tests, or-patterns, non-empty
list-literal patterns, array pinning — remain genuinely unimplemented on
wasm-linear. Implementing them is new work (a wasm exception model, a vtable
lowering), but now there is only ONE place to add it.

## Completing the backend (the current push)

The goal is now to make the wasm-linear backend, through LowIR, handle the
WHOLE language — so the C backend can be dropped once this proves out. LowIR
stays wasm-only; it is NOT retargeted to C.

**Landed:** or-patterns (`POr`, nested blocks), exact list-literal patterns
(`[a; b]` → nested cons), char / null / float / string literal patterns
(strings via a new `$streq` runtime — value equality by length then units),
char-literal expressions, and `:>` widening casts (identity in the tagged
model). `return` (opcode 0x0F) added to the assembler.

**Universal object header + type tests — LANDED.** Every heap object now
carries a **class-id** at offset 0 (`HDR = 4`): records and unions are numbered
from `CID_FIRST_USER`, the built-in shapes (tuple, array, list, closure, float
box, int64 box, string) take reserved ids `CID_*`. A union's cases share the
union's id and are told apart by their tag (now at `HDR`, payloads after).
Strings reuse their existing word-0 (was a `kind` tag) for the id, so the
string runtime is untouched. `ETypeTest` / `PTypeTest` read the header, guarded
behind an even-and-nonzero pointer test so a tagged int or null answers false
without dereferencing. NOTE: the wasm-GC oracle CANNOT type-test against a
union ("not a class"), so `lowir-typetest-gate.sh` checks the answer directly —
the linear backend is strictly MORE capable here.

**Still missing:**

- **Vtables / interface dispatch — DONE** (`lowir-iface-gate.sh`). `x.M args`
  dispatches through a flat class-id-indexed vtable; `:? IFoo` matches
  implementors, `:? Base` subclasses (`lowTypeTest` over a class-id SET from
  `SubsOf`/`ImplsOf`). Class methods read ctor params as receiver fields (the
  frontend lowers them to `EField` already). Two general bugs had to be fixed:
  `freeVars`/`discover` were incomplete (didn't traverse records/arrays/match/
  iface-calls, so a lambda over them lost its captures), and `scanConsts`
  skipped the function position of an application (a string in an eta-expansion
  lambda interned late, past `$hp`). Still TODO: the 3 identity slots
  (Equals/GetHashCode/Compare — need `$cmpv`/`$hashv`), built-in-seq iteration
  (`for` over a list dispatches `IEnumerable` with no vtable entry), and prelude
  class dispatch (only user impls are rooted today).

  DECIDED: approach (a). And it turns out to need NO `__desc` remapping — the
  `__desc`/`__idhash` fields are SYNTHESISED by the reference (BinDriver prepends
  them to its `FieldsOf`); they are NOT in the Core IR. A class emits a `DClass`
  (dispatch) AND a `DRecord` (its real fields), so our driver already gives every
  class a class-id via its `DRecord`, and `:? Class` (exact) already works. The
  universal header IS the descriptor.

  Concrete `EIfaceCall` plan (interface-method dispatch; skip the 3 identity
  slots Equals/GetHashCode/Compare — they need `$cmpv`/`$hashv` we don't have):
  1. From `decls0`: `classDecls` = the `DClass`es, `interfaceDecls` = `DInterface`s.
     `bareIface n` strips a `` ` ``-arity suffix. `vtableSlots` = distinct-sorted
     `(bareIface, method)` from interface decls + every class's impl clauses;
     `SlotOf(bareIface,method) → index`, `NSLOTS = count`.
  2. `chainOf`/`subclassesOf`/`slotImpl` ported from BinDriver: `slotImpl cn iface
     method` walks the inheritance chain to the `VarId` implementing that slot.
  3. Reachability: the impl `VarId`s are dispatched dynamically, so they are NOT
     reached by the ref walk — add their keys as ROOTS before filtering `decls`,
     or they get dropped and the vtable points at nothing.
  4. Give each impl function a table slot (`tblIdx st.M (fn v)`), like lifted
     lambdas, and ensure `$lfn(1+nargs)` types are declared.
  5. Bake a flat VTABLE into the data segment: for `cid` in 0..maxCid, for `slot`
     in 0..NSLOTS-1, a 4-byte function table-index (0 = none), row-major. Record
     `VTABLE_BASE`.
  6. `EIfaceCall(iface, method, recv, args)` → bind `recv` to a reg `t`;
     `cid = load t[0]`; `fnidx = load VTABLE_BASE + (cid*NSLOTS + slot)*4`; push
     `t, args, fnidx`; `call_indirect $lfn(1+len args)`. (Currying: interface
     methods are uncurried — recv + args, matching the reference's `$v(1+n)`.)
  7. Built-in seqs (lists/arrays as `IEnumerable`) carry no vtable entry — the
     reference pre-tests and routes to `$iterNew`/`$iterNext`; port later.
  Hierarchy type tests: generalise `lowTypeTest` to a SET of class-ids —
  `SubsOf(class)` (subclasses' cids) for `:? Base`, `ImplsOf(iface)` (implementor
  cids) for `:? IFoo`. Gateable against the wasm-GC oracle (it CAN do interface
  dispatch, unlike union type tests).

  `:?>` downcasts to a class-id-carrying type are now runtime-checked (trap on
  mismatch); to an untracked type they stay the identity.

- **Exceptions** (`ETry`, real `raise`). The reference uses the wasm EH
  proposal (`try_table` / `throw` / tags); wasmtime supports it (the oracle
  runs `-W exceptions=y`). The linear leg would emit the same and enable EH at
  run time; `failwith`/`raise` currently just trap.

**Smaller:** array pinning (`EArrayPin`/`Unpin`/`Bytes`) needs packed/POD
arrays (the linear backend boxes elements today); remaining `EUnknown`
intrinsics (`print`/`printb`/`printc`/`printu`, cells, monitor/parallel ops).

The end-state test is self-hosting on `--lowir`: compiling the compiler itself
through the linear backend. That needs all of the above (the compiler leans on
typeclasses and exceptions heavily).

## THE GOAL: full parity with the C backend (drop C)

Nothing less. The wasm-linear backend must compile everything CEmit/fpprt does,
correctly. Two fronts:

**Language (≈95% — nearly done).** Types, unions, records, closures, HOFs,
pattern matching, interface dispatch, exceptions, strings, captured mutables —
all at parity, oracle-verified. Remaining is the self-host punch-list below.

**Runtime / systems (the real distance).** In priority order:
1. **A real GC.** Today the linear backend BUMP-allocates and never frees;
   fpprt has a precise moving collector (Whippet). Needed for any long-running
   program. The value model is already fpprt's tagged word, so a semispace
   copier or a compiled vendored collector drops in against the same
   representation. THE big piece.
2. **POD / struct value semantics.** The linear backend boxes everything
   (reference semantics); CEmit has `[<Struct>]` value records with COPY
   semantics (`fpp_rec_clone`/`fpp_pod_clone`) and packed `int[]`. A struct
   assigned by value must copy — this is semantics, not perf. The LowIR
   struct/copy enrichment.
3. **Pinning + native interop** (`EArrayPin`/`Unpin`/`Bytes`, `DExtern`).
4. **Threads / parallelism** (`fpp_parallel_for`, monitors).

Milestone order: finish self-host (proves the language) → GC → struct semantics
→ pinning/interop → threads → **BENCHMARK against C** → only then drop C.

**The drop criterion is BENCHMARKS, not just feature parity.** C stays until the
wasm-linear backend is measured against it (the `tests/tooling/perf/` suite that
already compares against C — run wasm-linear via wasmtime AOT / `fpp exe`) and
proven competitive. That makes PERFORMANCE a first-class requirement, so two
items that would otherwise be "correctness done, optimise later" are actually
load-bearing for the goal:
- **Register allocation** (liveness colouring of `LReg` → wasm locals; today it
  is one local per register). Needed before the numbers mean anything.
- **POD/struct value semantics + packed arrays.** Boxing every numeric/struct
  value is not just a semantics gap — it is the perf gap on the vertex/array
  benchmarks where CEmit worked hardest (see the C-backend perf history).
Measure, do not reason (the repo's own hard-won rule): the benchmark suite,
best-of-three warm, is the arbiter — not instruction counts.

## The self-host RUN (proving the language) — the concrete next step

Two things stand between "compiles most of the source" and a `--lowir` self-host
fixpoint:
1. **Host imports (`DExtern`).** The compiler reads its input (corpus, prelude)
   through host services that BinDriver emits as wasm imports from the `env`
   module (`fixpoint.fsx` preloads `env.wat`). The linear backend only imports
   WASI `fd_write` today — it must emit the same `DExtern` imports so a
   `--lowir`-built compiler can read its input under the same host contract.
2. **Trap vs. garbage on unimplemented nodes.** `lowInt 0` fallback lets a
   `--lowir` module build despite unsupported intrinsics; the self-host DIFF
   against stage-0 then pinpoints exactly which unimplemented node is on a LIVE
   path (dead ones — e.g. `int#t`, which BinDriver itself doesn't handle — never
   matter). So the remaining intrinsic work is DEMAND-DRIVEN by the diff, not a
   blind sweep of the whole prelude surface.

Then a `--lowir` self-host fixpoint: emit the compiler via `--lowir`, run it
under wasmtime with the `env` host, diff its output against stage-0. Green = the
language is proven on the linear backend.

## Toward self-hosting on `--lowir`

Interface dispatch and exceptions landed, so the backend now covers the whole
*language*. The remaining question is the *library surface* the compiler's own
source uses. Compiling the compiler's 20 sources through `--lowir` emits ~2.1 MB
of wasm — it gets most of the way — with the gaps a BOUNDED list of intrinsics,
not architecture. From the gap histogram (probe: load the sources into a
`Workspace`, `EmitProgramWasmLinearWith true`, count the reported errors):

- DONE: `not`/`unot`, unary minus (int/int64), `int`/`char` conversions,
  `int` of a float, `refEq`, `$listLength`.
- **String methods** (~630): `$str.StartsWith` / `Substring` / `EndsWith` /
  `Contains` / `IndexOf`. The largest chunk — hand-emitted runtime routines over
  the `[cid][len][u16…]` string layout (like `$streq`).
- **`hash`** (~110): structural hashing (`$hashv` counterpart).
- **Cells** (~100): a closure-captured `let mutable` needs a heap cell — the
  read (`$cellget`) and the write (`assignment to captured mutable`, currently a
  clean-reported gap). Port the wasm-GC `$cellof`/`$cellget`/`$cellset` shape.
- **`int#t`** (string→int parse), and the remaining long tail of prelude
  intrinsics.

None of these are architectural — each is a runtime routine or a small lowering.
The finish line is a `--lowir` self-host fixpoint: stage-1 built through the
linear backend reproducing stage-0.

## The rest of the road

1. **Implement the still-missing nodes** (above) in Core→LowIR.
2. **A liveness register allocator** over `LReg` → wasm local slots, replacing
   one-local-per-register. This is the wasm backend's only real allocation
   work; C needs none.
3. **LowIR→C** in `CEmit`. CEmit uses the SAME tag model (`TAGI`/`UNTAGI`/
   `fpp_box_*` = the low-bit scheme, native-width), so LowIR ports there in
   principle. BUT CEmit's value model is RICHER than LowIR currently
   represents: copy-semantics POD structs (`fpp_rec_clone`/`fpp_pod_clone`),
   mutable cells for captured mutables (`$cellof`/`$cellget`), packed arrays,
   pinning. A naive LowIR→C would give a struct record REFERENCE semantics
   where C copies — wrong, not just slow. So this needs LowIR to grow struct /
   copy / cell representation first; then LowIR→C, validated against CEmit's
   native/ABI suite, retires the second copy of the lowering. Bigger than the
   wasm leg was.
4. **Optimisation passes** on LowIR: box elimination, POD-struct avoidance,
   alloc sinking — the representation-aware set.
5. **Native**: rely on wasmtime AOT now; a direct LowIR→x64/arm64 selector is
   the eventual dependency-free path.
