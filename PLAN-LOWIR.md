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

`lower` is NOT deleted: it still serves the genuinely-hard nodes the gate does
not reach — exceptions (`ETry`), typeclass dispatch (`EIfaceCall`), casts /
type tests, or-patterns, non-empty list-literal patterns, array pinning. Those
are the remaining ports before it can go.

## The road

1. **Port the remaining hard nodes** into Core→LowIR — exceptions, typeclass
   dispatch (vtables), casts / type tests, or-patterns, pinning — then delete
   `lower` on the wasm-linear leg. These need real new machinery (a wasm
   exception model, a vtable lowering), not just expansion.
2. **A liveness register allocator** over `LReg` → wasm local slots, replacing
   one-local-per-register. This is the wasm backend's only real allocation
   work; C needs none.
3. **LowIR→C** in `CEmit`, validated against CEmit's existing native/ABI test
   suite (its output must stay behaviourally identical). This is what retires
   the second copy of the lowering.
4. **Optimisation passes** on LowIR: box elimination, POD-struct avoidance,
   alloc sinking — the representation-aware set.
5. **Native**: rely on wasmtime AOT now; a direct LowIR→x64/arm64 selector is
   the eventual dependency-free path.
