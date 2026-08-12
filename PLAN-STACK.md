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

### fpprt already supports this (confirmed ABI)

The runtime (`fpprt.h`) already has the exact mechanism — no separate stack map
needed, the object's **tid IS the descriptor**:

    struct fpprt_frame {
      struct fpprt_frame *prev;   // linked list; fpprt_top_frame is the head
      uint32_t nslots;            // count of bare-ref slots
      fpprt_ref *slots;           // refs the GC reads AND UPDATES (moving)
      uint32_t npods;             // stack structs WITH ref fields
      struct fpprt_frame_pod *pods;
    };
    struct fpprt_frame_pod {
      char *base;   // struct address MINUS FPP_POD_OFF (blob-relative ref offsets apply)
      uint32_t tid; // the GC walks the type table's ref offsets for this tid
    };

So a stack struct with refs is registered as a frame POD `(base, tid)`; the
collector finds its inner ref fields through the tid's type-table ref-offset
list and scans+updates them in place. A pure-POD struct (no refs) needs no
registration at all. Pinning exists too (`fpprt_pin` / `fpprt_can_pin`, a
capability the `mmc` collector provides, `copying` does not) for the arena.

The wasm-linear work is: build a `fpprt_frame` in linear memory matching this
layout, push it (set the imported `fpprt_top_frame`) on entry, add stack structs
to `pods` with their `(base, tid)`, and pop on exit — plus reserving a
NON-MOVING value-stack region in the imported memory (the one piece needing
fpprt-side memory-layout coordination).

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

## Progress (wasm-linear)

Landed, each byte-exact self-host + run-gc + lowir gates green:

* **box-elim peephole** (`d73a594`): `unbox(box v) → v` at the LowIR level, and
  pushed through `LDo` (so a load-into-typed-local-then-box shape still cancels).
  This is what makes every unbox below reduce to a bare typed load in arithmetic.
* **Typed f64/i64 locals** (`da74e4b`): the emitter declared *every* register
  `i32`; now `LowCtx.RegTys` tracks a per-register wasm type and the declaration
  loops emit `f64`/`i64` locals. THE enabling primitive — an unboxed scalar now
  has somewhere to live across a call/allocation (a value local the GC never
  scans). `fReg`/`lReg`/`freshTmpT` construct them.
* **Flat scalar arrays** (`da74e4b`): `float[]`/`int64[]` are `FK_SCALAR_ARRAY`
  `[tag][len][elem×len]`, elems inline at HDR+4 stride 8 — no per-element box,
  GC-invisible. `int`/`bool`/`char` are already unboxed tagged words, so only the
  64-bit boxed scalars flatten (`flatScalarTy`); float32/16 still ride an f64 box.
* **Unboxed scalar `let`-bindings** (`29f5e3a`): a monomorphic `float`/`int64`
  `let` binds an unboxed typed local (`LowCtx.VarScalar`, `scalarLTy` off the
  binding's `Scheme.Body`). Reads re-box for the uniform-word contract (box-elim
  cancels it in arithmetic), captures re-box into the closure env, and captured
  mutables stay cells. Verified: fn-arg-derived locals, mutable loops, captured
  scalars, int64, and re-boxing a scalar into a generic `List`.

* **Unboxed scalar ABI** (`de6e53d`): a top-level function whose scheme has any
  `float`/`int64` param or return is emitted with a specialized wasm signature
  (raw f64/i64) via a per-function type, recorded in `St.FuncSig`. Scalar params
  arrive unboxed (registered in VarScalar); a scalar return is unboxed off the
  body's word. The direct-call site unboxes scalar args and re-boxes a scalar
  result (through a typed local — the call is a safepoint). Safe because a
  top-level fn is only ever direct-called: a first-class use eta-expands to a
  lambda that itself does a direct `LCall`, so it bridges for free (verified:
  `List.map sq fs`). Uniform `(env,arg)→word` closure convention untouched.

* **float32 unboxed** (`3320887`): the last boxed primitive value. `float32`
  rides an f64 box in this backend, so its arithmetic (`+s`…), locals, and ABI
  now lower exactly like `float` — a pre-existing gap where `s`-ops fell through
  to the tagged-int path (adding boxed pointers as ints → wild pointer) is fixed.
  `float32[]` packs as raw 4-byte f32 via reinterpret (`Bits2F`/`F2Bits`/`PromF`/
  `DemF`) with no new machine type — the f32 lives only transiently on the stack.
  `Array.zeroCreate` now fills the raw per-storage zero, not a mis-unboxed 0.

Net — the full primitive matrix, VALUES (locals/arithmetic/ABI):
* `int`/`char`/`bool`/`int16`/`byte`/`sbyte`/`nativeint`… — already unboxed as a
  tagged 31-bit word (never a heap object; the tag bit is the 31-bit cost).
* `float`/`int64` — unboxed f64/i64. `float32` — unboxed (rides f64). **All done.**

STORAGE (array elements; struct fields reuse the same `storLTy` table):
* `float`(f64)/`int64`(i64)/`float32`(4-byte f32) packed inline. ✓
* `byte`/`sbyte`/`int16`/`uint16` — `storBox`/`storUnbox` already carry their
  sign handling and `storLTy` maps them to I8/I16, but their element-kind string
  is not the plain type name at every site (bytes route through the string/`$str`
  packed-i8 path in the sibling backend), so the naive match disagreed between
  create and access. Held on the generic slot until that routing is shared —
  no regression.

### Next

* **Struct fields inline** (repr step 1, applied to records) — a record's
  `float`/`int64` field stored raw in the payload (`[header][f64 x][f64 y]`)
  instead of a boxed pointer; field read boxes (cancelled in arithmetic), write
  unboxes — the same transform as flat arrays. Needs a per-record LAYOUT (mixed
  4/8-byte fields, aligned) and a GC ref-map so the tid scans only the ref
  fields. This is the aggregate-`repr(T)` foundation the value stack also needs.
* **float32/float16 arrays + locals** — inline 4-byte f32 (stride 4) with
  demote/promote at the box boundary; extend `flatScalarTy`/`scalarLTy`.
* **Value-stack structs** (steps 3-4) — multi-field POD structs on the `$vsp`
  arena, by-value/sret/byref, then frame descriptors for ref-holding structs.
