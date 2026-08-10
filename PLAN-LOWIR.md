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

## Status: the seam is in and proven

`Core/LowIR.fs` defines the IR (`LExpr`/`LStmt`/`LFunc`, the `LOp` ALU, `LTy`,
`LReg`). `WasmLin.fs` gained a Core→LowIR lowering (`coreToLowE`/`coreToLowS`,
tag/box expanded here) and a LowIR→wasm emitter (`emitLowE`/`emitLowS`,
`emitFuncLow`). `fpp build --lowir` routes a function's body through LowIR
where a `lowSupported` predicate says the whole body is in the covered subset,
and **falls back to the hand-lowering `lower` otherwise** — so the two paths
coexist in one interoperating module and the output can never regress. As the
subset widens, `lower` shrinks; when it is empty, LowIR is the only path and
the hand-lowering is deleted.

Covered subset today: integers, arithmetic and comparison, `let`/`let mutable`
and top-level globals, top-level functions with direct calls and recursion,
`if`/`elif`/`while`/assignment/sequencing, string literals, int-to-string,
string concat, `printfn`. Registers are allocated one wasm local per `LReg`
(no liveness colouring yet — that IS the register-allocation pass, still to
come).

Gated by `tests/tooling/cback/lowir-gate.sh`: a program entirely inside the
subset (fib, fact, gcd, a polynomial, collatz, a summation loop, formatted
output) is emitted through Core→LowIR→wasm and diffed against the wasm-GC
oracle — a THIRD independent emission path agreeing on one meaning. The full
`wasmlin-gate.sh` program (closures, records, unions, arrays, floats, int64,
lists, match, options) also runs clean under `--lowir`: its in-subset
functions take the LowIR path, the rest fall back, and the mixed module still
matches the oracle. Both `fixpoint.fsx` and `fixpoint.fsx self` reproduce
byte-for-byte with `LowIR.fs` now among the compiled sources.

## The road

1. **Widen `lowSupported` + `coreToLowE`** to closures/indirect calls,
   records/unions/tuples, arrays, `match`, floats and int64 — porting each
   from `lower` into the Core→LowIR expansion. When the whole `wasmlin-gate`
   program lowers through LowIR, delete `lower`. The deferred wasm-linear
   features (local recursive closures, full-width ints, exceptions, typeclass
   dispatch) come nearly free here, since LowIR gives them a structured home.
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
