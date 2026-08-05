# fpprt — the F++ runtime

The object model and GC every linear-address-space backend targets: native
now, wasm-linear later. The collector is [Whippet](gc/README.md) (vendored
under `gc/`, MIT, commit in `gc/VENDORED`), an embed-only C library with
several collectors behind one API — the runtime code is identical whichever
one is linked.

```
make COLLECTOR=semi test    # semispace: moves EVERYTHING, the root shakeout
make COLLECTOR=pcc  test    # parallel copying (default)
make COLLECTOR=mmc  test    # Immix-style mark-region: real per-object pinning
make test-all               # all three
make test-wasm              # wasm32 (semi AND mmc-with-pinning) under wasmtime
```

## What v0 gives the backends

* **Precise moving collection.** Every type registers a size and its
  reference-field byte offsets (`fpprt_register_type`) — the pointer maps
  the compiler already knows how to compute. No conservative anything.
* **Shadow-stack roots.** `FPPRT_FRAME(f, n)` / `FPPRT_LEAVE(f)` — every
  ref that must survive an allocation lives in a frame slot the collector
  can read and UPDATE. This is the discipline wasm forces (no stack
  walking) and native gets for free; `semi` punishes violations
  immediately by moving every object on every collection.
* **Real weak references** (`fpprt_weak_new`/`get`) — ephemerons underneath,
  so a weak ref keeps nothing alive and reads 0 after its target dies. The
  thing wasm-GC cannot express at all.
* **Real pinning** (`fpprt_pin`) on `mmc`: the object never moves again —
  no handle indirection, no copy-in/copy-out bounce, no
  one-pin-poisons-the-kind analysis.
* **Arrays** with ref or scalar elements: `[tag][len][elems]`, scalar
  payloads never scanned, never a per-element bounds-checked opcode.
* **Threads-shaped API.** `pcc`/`mmc` trace in parallel today; mutator
  threads are a Whippet feature this wrapper does not yet expose. The wasm
  builds are single-threaded (`semi`, and `mmc` with
  `GC_NO_BACKGROUND_THREAD` — a fixed-size heap needs none of the
  background thread's periodic work), so PINNING works under wasm32 too.

## Layout

* `fpprt.h` / `fpprt.c` — the runtime API (~150 lines of implementation).
* `fpprt-embedder.h` — Whippet's embedder contract over our tag word:
  `(typeid << 1) | 1` live, forwarding pointer when bit 0 is clear.
* `gc-platform-wasm.c` — the platform shim for emscripten/wasi builds
  (aligned_alloc reservations, no threads, no signals).
* `gc/` — vendored Whippet. Local changes (candidates for upstream):
  `semi.c` allocation counter widened to `uint64_t` for wasm32; `spin.h`
  pause portable off x86; `background-thread.h` gains
  `GC_NO_BACKGROUND_THREAD` for single-threaded wasm.
* `test/test_rt.c` — the v0 gate: list churn through forced compacting
  collections, ref/scalar arrays, weak death and weak survival, pin
  stability. Must pass under all three collectors AND the wasm build.

## What is deliberately NOT here yet

Finalizers (Whippet has them; wire when the language needs them), mutator
threads, the generational write-barrier fast path inlined into compiled
code (fpprt_write_ref calls out today), interior pointers (never), and the
wasm-GC interop story — that backend stays as the checked semantics
reference, and foreign refs will cross as externref table handles, not as
a second object representation.
