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
* The FULL matrix packs inline now: `float`(f64), `double`, `int64`/`uint64`(i64),
  `float32`/`single`(4-byte f32 via reinterpret), `int16`/`uint16`(i16),
  `byte`/`sbyte`(i8). ✓ The earlier "byte/int16 disagree" belief was WRONG — it
  was purely a value bug: a suffixed integer literal (`100s`, `200uy`) hit
  `Int32.TryParse` with its type suffix and silently became 0, so every narrow-int
  round-trip read back 0. Stripping the suffix (int16 `s`, uint16 `us`, sbyte `y`,
  byte `uy`, uint32 `u`) fixed the values AND unblocked the packed arrays.

* **Inline value-type record storage** (`762cf11`, Phase 1): an all-scalar
  record/struct (`Vec3{x,y,z:float}`, `{a:float32;b:int64;c:float}`) stores its
  fields RAW inline — `[header][f64 x][f64 y]…`, GC-invisible (`FK_STRUCT`,
  nrefs=0), no per-field box. `St.RecPod` holds the field→(offset,kind) layout
  and object size; construction/`{with}`/read/write/mutation go through it, a
  field read boxes (cancelled by unbox in arithmetic). Verified: fields, `dot`,
  mutable fields, mixed 4/8-byte widths, functional update, structural equality.

### The model (settled with the user)

Real value types: `int`/`float`/`struct` box ONLY on an explicit `obj` upcast —
never in generics or function calls. That mandates **monomorphized/reified
generics** (a value type flows through unboxed; `List<Vec3>` holds inline Vec3s).
The residue that can't be statically monomorphized — polymorphic recursion,
first-class-polymorphic / HKT-existential values — is the genuine dynamic
boundary and takes an implicit box/vtable like `obj`; it is small and must be
flagged, never silently boxed. The tagged 31-bit word is NOT a heap box — it is
stack passing — so `int` and every ≤4-byte primitive already never heap-allocate.

* **Mixed inline records** (`2d84d14`, Phase 1b): a record with >=1 scalar field
  AND ref fields inlines its scalars raw and keeps the refs as word slots. Fields
  are laid out SCALARS-FIRST, REFS-LAST and registered `FK_TAGGED` with `start` =
  the first ref word — so the collector scans ONLY the ref suffix (never a raw
  f64 that could look like a pointer) with NO `refoffs` array (which would need
  stable memory the GC module lacks), and the existing `$cmpv` compares the
  scalar prefix raw and recurses only the refs. Construction roots each ref
  pointer on the shadow stack across the allocation. This also FIXED a latent
  Phase-1 bug where all-scalar records recursed on f64 words in `$cmpv` (could
  deref a float bit-pattern as a pointer) — both paths are unified on FK_TAGGED
  now. Verified: mixed fields, functional update, structural equality (recurses
  into the string field), and a 200k-record GC-stress run where a kept record's
  string field survived relocation.

* **Flat array-of-struct** (`c6521ab`, Phase 2): a `Vec3[]` (all-scalar element)
  stores its elements CONTIGUOUS and HEADERLESS (`[tag][len][fields][fields]…`,
  stride = the record's field bytes), GC-invisible (FK_SCALAR_ARRAY). A field
  access `arr.[i].f` fuses straight to the slot (`ARRHDR + i*stride + off-HDR`);
  a field WRITE must fuse (matched ahead of the plain POD-field cases, else it
  would mutate a copy-out throwaway). A whole-element read copies out to a fresh
  headed record; a whole-element write copies the source's fields into the slot;
  create/literal fill each slot, rooting the source across the alloc. Verified:
  fused read/write, whole read/write, literal, and a 1000-element array surviving
  2000 allocations of GC pressure with exact contents.

### Next

* **Value semantics + `$vsp`** — array elements already copy in/out (value
  semantics); struct LOCALS are still heap pointers. Put POD struct locals on the
  non-moving value stack, copy-on-pass / sret / byref (step 3).
* **Scalar monomorphization LANDED (float, wasm-linear)** (`6b8b271`): `classify`
  now stamps a specialised clone per `float`/`double` instantiation too — but
  ONLY on the wasm-linear target (`stampScalars`, threaded
  `LinkedCoreFor(forLinear:true) → monomorphizeWith → classify`; wasm-GC and C
  keep the shared body). So a generic used at `float` carries it UNBOXED through
  WasmLin's existing scalar lowering (`scalarLTy`/scalar ABI), while the wasm-GC
  self-host and adaptive suite are untouched. Structs ALREADY stamped for every
  target (`isStructName`), so structs were already unboxed in generics; this
  closes the boxed-scalar gap for float. Gated: byte-exact self-host, WasmLin
  probe (0 errors compiling the whole compiler WITH stamping), all 698 unit
  tests, run-gc on a generic fold over floats.
  EXTENDED (`9a8c27f`) to `int64`/`uint64`/`float32`/`single` — every boxed
  scalar now stamps unboxed through a generic on wasm-linear (self-host byte-
  exact, probe 0 errors, 698 tests, run-gc on generic twice/pick/fold over
  int64 and float32). Structs were already stamped for all targets, and flow
  through generics as a word-pointer with inline fields (verified twice/pick/
  fold over Vec3). So: NO value type is boxed passing THROUGH a generic on
  wasm-linear. The one gap left is a generic CONTAINER holding a struct INLINE
  in its node (`List<Vec3>` cons cells still point at the Vec3) — that needs the
  container TYPE monomorphized with inline element storage (`Vec3[]` already is).

* **Monomorphize generics** (step 4) — the endgame that removes the last uniform
  slots (so `List<Vec3>` holds inline Vec3s). Now PARTLY LANDED (structs + float
  on wasm-linear, above). Remaining, and why the wasm-GC path is still gated OFF: 
  - It lives in `Link.fs` (`classify`, `Link.fs:19`), NOT the backend — `EVarI`
    instantiations are consumed there and erased before any backend runs. Link
    already stamps a specialised clone per STRUCT instantiation; ref types share
    a boxed body. Widening `classify` to also stamp the boxed SCALARS
    (`float`/`double`, then `int64`/`float32`) is a ~1-line change and routes
    value-type generics through WasmLin's existing unboxing (scalarLTy/RecPod).
  - Adding `float` there: byte-exact self-host held (+105 bytes — float generics
    are rare in the compiler), corpus fixpoint + lowir gates + WasmLin probe all
    green, and a generic fold over floats runs correct on WasmLin.
  - BUT it broke 2 unit tests: the **wasm-GC backend** traps with `ref.cast`
    failure on a scalar-STAMPED generic (the adaptive suite) — the latent
    "vtable member keeps the all-anyref signature" limitation (see repo CLAUDE.md)
    surfacing on a concrete-scalar clone. The self-host didn't catch it (the
    compiler doesn't use float generics that way); the broader suite did.
  - Monomorphization runs ONCE in the shared IR pipeline (`Workspace.fs:953`),
    consumed by whichever backend runs, so it can't be gated to WasmLin cheaply.
    So the true NEXT step is in the **wasm-GC backend**: make a scalar-stamped
    generic body lower with the concrete scalar rep (fix the anyref-vtable-vs-
    concrete cast), THEN the one-line `classify` widening lands for both backends.
* **Mixed-record arrays** — `{x:float; tag:string}[]` needs FK_POD_ARRAY with a
  per-element refoffs map (stable-memory question again; array-of-struct is
  all-scalar for now).
* ~~Narrow-int packed arrays~~ — DONE (int16/uint16/byte/sbyte all pack; the
  blocker was the suffixed-literal value bug, now fixed).

## WasmLin self-host (the byte-exact gate for WasmLin)

Goal: run the self-host on the WASM-LINEAR backend, so WasmLin gets its own
byte-exact correctness gate (today's `fixpoint self` runs on wasm-GC and never
executes WasmLin code — corruption-prone arcs like `$vsp` can't be gated without
this). Attempted end-to-end; the state is concrete and promising:

* `fpp build --gc <compiler sources> <baked-corpus driver>` produces a **3.8 MB
  runnable module** — the whole compiler compiled through WasmLin.
* It **boots and survives startup** now (was: trapped at the first init). Two
  fixes got it there:
  - **self-hostable literal parsers** (`1e7714b`): WasmLin.fs used
    `System.Int32.TryParse`/`Double.TryParse` to lower numeric literals, which
    stub `coreToLowE`/`lowPatTest` to `unreachable`. Replaced with hand-written
    `parseI32Lit`/`parseI64Lit` (int) and the `parseFloat` prelude helper (float,
    isolating `Double.Parse` in a leaf), so the critical functions self-host.
  - **stubbed inits store 0, don't trap** (`3634a48`): a .NET-only top-level
    `let` (e.g. `let latin1 = System.Text.Encoding.Latin1`) lowered its init to
    `unreachable`, and `_start` runs every init → startup trap. A stubbed INIT
    now stores 0 (the value is only touched by already-stubbed .NET methods); a
    stubbed FUNCTION still traps loudly.
* Now traps in a CALLED stub on the compile path — the remaining blockers are a
  finite set: `$class:Num:One` (numeric-typeclass member), and the .NET-API
  stubs `ToString`/`GetEnvironmentVariable`/`eprintfn`/`DoubleToInt64Bits`
  (+ `box`). Each is: implement the intrinsic in WasmLin OR route it through an
  isolating leaf helper so the caller self-hosts.
* NOTE: the linear backend does not surface `st.Warnings` (it returns
  `st.Errors`; `EmitWarnings` is only set by the wasm-GC path) — surfacing them
  from `emitLinear` is the cheap next step to ENUMERATE the remaining stubs.
* For the FULL self-host (not just the baked-corpus run) WasmLin also needs
  `DExtern`/`readTextRaw` host-import support to read source files; a baked-corpus
  driver sidesteps that for the correctness-gate purpose.

This is a multi-step arc but no longer speculative: the module builds, boots, and
the remaining gaps are a concrete, finite stub list.

### WasmLin self-host — session progress (from "immediate trap" to "host-I/O boundary")

The WasmLin-compiled compiler (baked-corpus `wstest` driver: construct a
Workspace, SetFileText a trivial program) now BOOTS, runs its whole static-init
sequence, and executes the full startup + collection machinery. It advanced
blocker-by-blocker:

* literal parsers (`1e7714b`) + float-suffix parse (`fc2cd92`) → `coreToLowE`/
  `lowPatTest` self-host (were `TryParse`/`Double.Parse` stubs; `5.0f` crashed
  `Double.Parse`, now filtered + f32-rounded like BinDriver).
* stubbed inits store 0, don't trap (`3634a48`) → survives .NET-only global inits.
* freeVars captures `(builtin)`-path LOCALS (`fc2cd92`) → cleared DOZENS of
  `name=x/acc` capture stubs. Only bare `compare` (the one valueless intrinsic)
  stays excluded from capture.
* CORPUS FIX (not a compiler change): the self-host substitutes `Prelude.fs` →
  `stdlib/bootstrap.fpp` (line 43 of fixpoint.fsx) — the self-hostable `Vec`
  (`{Items; Count}` record over an array) vs `Prelude.fs`'s `Vec = .NET List`.
  An ad-hoc build that compiles `Prelude.fs` traps in `vecNew` (`List()` → LTrap).

Now blocked ONLY at the file-I/O boundary: `preludeSource()` calls
`preludeSourceRaw` (an `extern` host import), and WasmLin has no `DExtern`
handling, so it stubs → traps when the Workspace reads the prelude.

REMAINING for a running baked-corpus gate:
* **DExtern host imports** — emit `readTextRaw`/`preludeSourceRaw` as wasm imports
  (Core has `DExtern of VarId * Scheme`; BinDriver emits jsExterns via `importFn`).
* **A WasmLin host env** providing them with the fpprt/linear string ABI (the
  tricky part: the host must build an fpprt i16-array string to return), OR bake
  the prelude/corpus as constants so no host import is needed.

Diagnostics added this session (env-gated, harmless): `FPP_LINWARN` dumps the
linear backend's dropped `st.Warnings`; `FPP_FUNC_DUMP` maps `$f<hash>` → binding;
stub warnings now carry the function/lambda name.

### WasmLin self-host — deeper progress (real bugs found + fixed)

Grinding the self-host surfaced GENUINE WasmLin correctness bugs (untested because
run-gc programs and the wasm-GC self-host never exercised them):

* **`&&&`/`&&`/`|||`/`||`/`^^^`/`<<<`/`>>>` were lowered as `rem`** (`2e27b36`):
  `intArithOp` handled only `+-*/` and defaulted everything else to `RemSW`, so
  `255 &&& 15` gave 0 (= `255 rem 15`) and `A && B` gave `A rem B`. This is what
  trapped the self-compiled `dictSlotH` (`h &&& mask` → `h rem mask`, and later
  `A && B`). Fixed → the Dictionary machinery runs.

Progress chain (each a real fix, gated byte-exact + 698 tests):
boot → static inits (init-stub-as-0) → prelude read (extern → null) → inference
→ Dictionary (bitwise/logical fix) → traps now in `Query.GetInput`.

REMAINING, concrete:
* **`GetInput` miss**: the query `table` (a `Dict` with TUPLE keys `(query,key)`)
  misses under WasmLin though the minidrive works in .NET. Tuple EQUALITY is
  correct; tuple HASH is DEGENERATE (`hash("x","y") = hash("p","q")` → true, the
  `$hashv` "other → class-id" path) — consistent so still correct, just O(n). The
  miss itself is a separate not-yet-isolated bug in the self-compiled dict/query
  path (dictNew isn't in the user prelude, so it can't be reproduced in a small
  run-gc test — only in the self-compiled compiler).
* Then: more traps likely, AND a REAL fpprt-string host env (the extern→null is a
  hack that yields wrong output, so even a fully-running compiler wouldn't
  byte-exact self-host until the prelude/corpus are really read).

So: from "traps at the first init" to "runs boot+prelude+inference+Dictionary and
into the query engine", plus two real op-lowering bugs fixed. A byte-exact WasmLin
self-host is a multi-session finish, but no longer speculative.

### ROOT CAUSE of the GetInput/dict miss: generic `=` compared POINTERS

The self-host `GetInput` trap was a real WasmLin miscompile, now fixed and
verified end-to-end.

* Isolation: `geq<'k> a b = a = b` returned FALSE for two equal tuples, while
  the same `("q","a") = ("q","a")` at a concrete site returned true. Tuple
  EQUALITY and HASH were both fine; the generic wrapper was the difference.
* Cause: `shapeOfExpr` on a generic variable prunes to a type variable →
  `ShOther`, and `needsStructCmp(ShOther)` was FALSE, so `a = b` fell to the
  tagged-int/pointer fast path — which compares heap ADDRESSES. Two distinct
  but equal tuples/strings/records held in a generic `'k` always missed. That
  is exactly `dictSlotH`'s `d.Keys.[e-1] = k`: every tuple-keyed lookup missed,
  so the compiler's Query DB (`Dict<(query,key), Entry>`) reported "unset input".
* Fix: `needsStructCmp(ShOther) = true`. `$cmpv` is self-describing — it handles
  tagged ints, strings, floats and compounds uniformly — so the unknown/generic
  case routes through it correctly (a KNOWN `ShScalar` still keeps the fast path).
* Verified: generic tuple eq → true; tuple-keyed `Dict` resolves qa→10/qb→20;
  and `querydrive.fpp` (the FULL query engine: inputs, memo, dep-tracking,
  invalidation, early cutoff) run under WasmLin (`fpp build --gc`) prints
  `10computes 310computes 37computes 57` — byte-identical to the .NET
  `queryOracle`. The query engine, which `EmitProgramWasm` is built on, now
  works under WasmLin.

Gates after the fix: lowir cell/str/typetest/iface/exn PASS; byte-exact
`fixpoint self` still reproduces stage-0 (2613369 bytes); unit suite pending.
