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

- **Vtables / interface dispatch** (`EIfaceCall`) and **class hierarchies**
  (subclass/implementor matching for `:? Base` / `:? IFoo`). The class-id
  header is the substrate; what's left is a per-class-id vtable table (a global
  `call_indirect` table indexed by class-id × slot) and processing
  `DClass`/`DInterface`/`DBaseInst`/`DMembers` to fill `SubsOf`/`ImplsOf`/slots.
  This is the main gate to self-hosting (the compiler leans on typeclasses).

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
