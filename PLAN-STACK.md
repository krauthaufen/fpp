# Stack-allocated value types for the wasm-linear/LowIR backend

Goal: `int`, `float`, `float32`, `int64`, and **all structs** live either in wasm
locals/registers (scalars) or in a **linear-memory value stack** / flat arrays —
never boxed on the GC heap in monomorphic code. Structs pass by value (copy to a
fresh stack offset) or by reference (pass the address). The moving GC learns
about references *inside* stack structs through per-frame descriptors, so a
struct with reference fields still travels on the stack.

This replaces "wide/aggregate → box on the GC heap" with the standard
native-with-a-moving-GC model (CoreCLR / Go / LLVM statepoints), adapted to
wasm's non-introspectable call stack via explicit frame push/pop (fpprt already
exposes `fpprt_frame_push` / `fpprt_frame_pop` + the wasm-roots table).

## Representation: `repr(T)`

Computed once per type, structurally, single-field-collapsing. No `newtype`
keyword — a one-field struct simply *is* its field.

    repr(scalar int/bool/char)      = W-scalar (raw i32 in a local; tagged only at a generic boundary)
    repr(float/float32/float16)     = F64-scalar (raw f64 in a local)
    repr(int64/uint64)              = I64-scalar (raw i64 in a local)
    repr(string/list/closure/ref)   = Ptr (tagged/aligned heap pointer)
    repr('a  / generic var)         = Uniform (a tagged word; the boxing boundary)
    repr(struct { })                = Unit (elided, zero cost)
    repr(struct { f })              = repr(f)                     -- COLLAPSE, transitive
    repr(struct { f1..fn }, n>1)    = Aggregate { repr(fi) at offset oi } + ref-slot map

Notes:
* The collapse is transitive: `A={x:B}`, `B={y:int}` ⇒ `repr(A)=repr(B)=int`.
* Types stay distinct to the checker; only the runtime representation is shared
  (the `newtype` benefit, made general and automatic).
* A one-field struct wrapping a **reference** flows through `'a` containers with
  ZERO boxing (it's already a pointer). A one-field struct wrapping a **scalar**
  still boxes at a generic boundary, same as the bare scalar.
* Aggregate layout: fields at natural-aligned offsets (must match the emscripten
  ABI the `tests/tooling/abi/` checks already enforce). The **ref-slot map** is a
  static list of the offsets that hold `Ptr`/`Uniform` (recursively flattened
  through nested aggregates) — this is what the frame descriptor registers.

## The value stack

A reserved, **non-moving** arena in linear memory (below the moving heap), with a
global value-stack pointer `$vsp`. It is a GC **root region**: the collector
SCANS the frames' ref slots and REWRITES those pointers when targets move, but
NEVER relocates the frames themselves (a moved frame would dangle a running
function's interior pointer — wasm can't rewrite a live local mid-call).

Frame discipline (mirrors emscripten's `__stack_pointer`):
* entry: `$vsp -= frameSize`; if the frame has ref slots, `fpprt_frame_push(base, descriptor)`.
* exit:  `fpprt_frame_pop()` (if pushed); `$vsp += frameSize`.

This RETIRES the hand-placed `$spush`/`$spop` for struct locals: a struct's ref
fields are covered by its frame descriptor, so rooting is structural and complete
(kills the "did I remember to root this" bug class).

## Calling convention

* **scalar** args/returns: wasm value (raw i32/f64/i64), by value. GC-invisible.
* **Ptr / Uniform**: single tagged word, by value.
* **aggregate** args: caller writes the struct into an arg slot (its frame or a
  scratch region) and passes the **address**. Value semantics = copy the bytes to
  a fresh offset first; byref = pass the caller's slot address without the copy.
  So byref falls out as "skip the copy."
* **aggregate returns**: caller passes a hidden **sret** pointer; callee writes
  through it (C ABI).

## Arrays

`float[]`, POD `struct[]` → a flat linear buffer with inline elements,
`base + i*stride`. No boxing, no GC scanning for POD element types. A `struct[]`
whose element has ref slots is an array root region (its per-element ref offsets
scanned by a descriptor), same idea as frames.

## Escape rule

Stack allocation is the default. A struct that ESCAPES — stored in a heap object
(list/closure/record field on the heap), returned as a boxed `'a`, address
captured beyond the frame — must be **heap-allocated** instead (or copied to the
heap at the escape point). This keeps the invariant: no heap object ever points
into the value stack. F#'s byref lifetime rules already forbid byrefs escaping
their frame, so the frontend does part of this.

## Generic boundary

`'a container` where `'a` is an aggregate:
* start: **box at the boundary** — flat in monomorphic code, heap-boxed only when
  crossing into a generic container.
* endgame: **monomorphize** hot generic code per element type so containers hold
  inline aggregates (what the wasm-GC backend gets from typed structs).

## Build order (each step lands green, self-host byte-exact)

1. **LowIR aggregate type + `repr(T)`** (collapse + ref map). The foundation; also
   unblocks LowIR→C. Everything hangs off `repr`.
2. **Flat inline arrays** (`float[]`, POD `struct[]`). Biggest isolated win, no GC
   entanglement.
3. **Value stack + POD-struct ABI** (by-value/sret/byref) for structs with NO ref
   fields. Still GC-invisible.
4. **Frame descriptors → precise roots**; extend the value stack to structs WITH
   ref fields; delete the manual shadow-stack pushes for struct locals.
5. **Escape analysis** (stack-by-default, heap-on-escape) + generic boundary
   (box-at-boundary, then monomorphize).

Kept behind the existing `--lowir`/seam so the current backend stays the default
and byte-exact until each piece proves out.
