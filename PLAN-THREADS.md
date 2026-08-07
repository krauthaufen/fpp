# Threads, concurrency, parallelism

Design notes from 2026-08-06, before any implementation. The premise all of
this rests on: .NET's TPL fused two different things into `Task<T>` — an
interleaving of EFFECTS (concurrency) and a slice of pure COMPUTE
(parallelism) — and made one scheduler serve both. That is where the
pathologies live: CPU work starving the IO pool, sync-over-async deadlocks,
`ConfigureAwait`, `Parallel.For` and `await` fighting over one work-stealing
pool. F++ keeps the two apart, with different schedulers and different
contracts.

The split is not only taste — the web platform enforces it. The browser main
thread must never block, so concurrency there HAS to be event-loop-shaped.
Workers may block (`Atomics.wait`), which is exactly what a compute pool
needs. And shared LINEAR memory is the only memory workers can share today:
the wasm-GC backend cannot participate (shared-everything-threads is not
shipped), so real threading is a capability of the fpprt/wasm-linear leg —
one of the original reasons for building a runtime with its own GC.

## Concurrency: the async CE on an event loop

`async` stays what F#'s async got right: COLD, structured, cancellation
threaded through ambiently. Its scheduler is an event loop on the CURRENT
thread — the browser's own loop on the main thread (awaits wire to
promises/timers), a poll loop natively. No OS threads implied; this layer
works on every backend including wasm-GC, and lands before any threading
does.

Structure follows the modern consensus (Trio/Kotlin): child computations
cannot outlive their scope; cancellation is a tree, not a flag you remember
to check.

Communication between the two worlds is CHANNELS (a future is the one-shot
degenerate case). An async consumer awaits a channel that a parallel job
fills; neither scheduler knows about the other.

## Parallelism: virtual threads, phases, no blocked workers

The model is NOT P-lane SPMD and NOT task-per-element. The user-facing shape:

```fsharp
Parallel.dispatch n (fun vt ->        // n VIRTUAL threads, n ~ millions
    a.[vt.Index] <- a.[vt.Index] * 2.0
    vt.Sync()                          // group-scoped phase boundary
    if vt.Index > 0 then
        a.[vt.Index] <- a.[vt.Index] + a.[vt.Index - 1])
```

`Parallel.map/choose/scan/fold/init/iter` are LIBRARY code over dispatch —
no privileged primitives. Groups partition the virtual threads
(shader-style, explicit-with-default): `Sync()` without declared groups
means all n; declared groups make it group-local.

A virtual thread is never a fiber and never has a stack. The COMPILER
splits the kernel at every `Sync()` into phases; what survives a barrier is
the virtual thread's live locals, MATERIALIZED per thread — a live `float`
becomes one lane of a raw `float[]` of length n (the allocation diet is
what makes this cheap), refs go to a ref array. Each phase then compiles to
what the backend already generates fastest: a chunked flat loop over
virtual-thread indices with raw locals inside.

The schedule: the unit of work-stealing is a CHUNK of one group's virtual
threads in one phase. A group's phase i+1 becomes runnable the moment the
last chunk of ITS phase i retires — group barriers do not join the world,
so independent groups pipeline through phases like workgroups on a GPU. A
global sync is the degenerate one-group case. Workers never block at a
barrier: parked state is a phase counter per group, and a worker that
finishes a chunk steals whatever chunk is runnable anywhere. Load balancing
falls out of chunk granularity; no separate mechanism.

The rule this buys us, same as CUDA/WGSL and for the same reason: barriers
must be encountered UNIFORMLY within their group — a data-dependent barrier
cannot be phase-split. Compile-time diagnostic, applies only inside dispatch
kernels; divergent computation is fine, only the sync points must be
uniform.

The combinators need only 1–2 phases each and can be written phase-split BY
HAND before the compiler transform exists:

- map/init/iter: chunk per lane, zero barriers
- fold/reduce: local fold → one barrier → combine P partials (deterministic
  for a given chunking; chunking is a pure function of (n, P), so runs
  reproduce)
- scan: Blelloch — local scan, publish chunk totals → barrier → tiny scan
  of totals → barrier → add carry (two barriers)
- choose/filter: local count → barrier → prefix-sum of counts gives every
  lane its exact output offset → barrier → scatter into an exact-size
  result (two barriers, no compaction pass, no over-allocation)

## Barrier dependence analysis: weaker sync, same semantics

`Sync()` always MEANS "phase boundary". The analysis never changes
semantics — it proves the boundary can be IMPLEMENTED weaker. The ladder,
each rung shippable alone:

1. Barrier = group join. The baseline phase engine.
2. AFFINE dependence analysis on cross-barrier array subscripts (i, i-1,
   i+k, strided) yields dependence distance vectors. Two rewrites follow:
   intra-chunk the barrier EVAPORATES (ascending in-chunk order already
   satisfies a leftward distance — run phase loops per chunk, not
   per-element fusion; each fusion shape's legality falls out of the same
   vectors); inter-chunk it becomes a HALO HANDOFF — chunk c's phase i+1 is
   runnable as soon as chunk c-1 retires phase i. A wavefront: a million
   virtual threads in a few hundred chunks pipeline with no global stall.
   This is the ghost-cell pattern of stencil compilers; the hand-tuned GPU
   version of "×2 then add left neighbour" is decoupled-lookback scan, and
   the analysis derives what those implementations hard-code.
3. Pattern-level recognition where it pays: a barrier whose backward
   dependence is a full prefix gets the scan lowering; user-written scans
   and the library scan converge on the same code.

Scope boundary, stated honestly: subscripts that are indirect (`a[idx[i]]`)
or data-dependent are statically unknowable — the barrier lowers to the
conservative group join, still correct, just synchronous. No runtime
dependence tracking (Legion-style per-element graphs): the bookkeeping eats
the parallelism at this grain.

Later, if footprint precision needs it: kernels can declare what they
read/write across a sync when it is not derivable — but the common case is
derivable from the phase bodies.

## Shared state and the adaptive world

The parallel API's blessed shape is: kernels over their slice plus channels
— most programs cannot write a data race. Shared mutable heap access from
kernels WORKS (Whippet is built for parallel mutators) but is not the
advertised surface; raw `Thread`/`Monitor`/atomics exist underneath as
runtime plumbing.

The adaptive graph stays SINGLE-WRITER. FDA's transaction model is one
writer plus level-ordered evaluation; parallelizing marking/evaluation is a
research project this design deliberately does not couple to. Workers feed
values into `transact` through channels.

## Runtime groundwork (shared by native and wasm)

- TLS: `fpprt_top_frame` (shadow stack), the exception handler chain and
  `fpp_exn_` become `_Thread_local`.
- Safepoint polls: generated code needs `fpprt_safepoint()` at loop
  back-edges — today the world only stops at allocation, so a
  non-allocating loop on another thread blocks collection forever. The
  phase engine helps: barriers are explicit, known blocking points, and the
  barrier wait is where a worker PARKS as a GC mutator (Whippet's
  park/unpark) — a lane waiting at a barrier can never block another
  lane's collection. Kernels may allocate freely (per-mutator allocation
  regions; what pcc/mmc are for).
- Real locks: `Monitor.Enter`/`lock` are no-ops today (`TryEnter` returns
  constant true). Fine single-threaded, wrong with two mutators.
- Pool: fixed, sized to the hardware, created once. Work-stealing deques of
  chunk descriptors, per-group phase counters.

## wasm specifics

- Browser: COOP/COEP headers (cross-origin isolation) for
  SharedArrayBuffer — deploy config, not code.
- emcc `-pthread`: pthreads over workers+SAB; `gc-platform-wasm.c` is the
  no-threads shim — with `-pthread` most of the POSIX platform file should
  serve. `GC_NO_BACKGROUND_THREAD` concerned the collector's helper thread,
  not mutators.
- Main thread never blocks: dispatch is initiated from anywhere, but joins
  from the main thread are awaits (async layer), not blocking waits.
- wasmtime validates the threaded build headlessly (`--wasm threads=y`)
  before any browser is involved; native validates the same runtime work
  first.
- wasm-GC backend: the whole parallel library degrades to a sequential
  schedule of the same phases (P = 1) — same semantics, code stays portable
  across all three backends.

## GC extras this design can lean on

"Do I hold the only reference?" is implementable HONESTLY here, unlike in
.NET: every live reference is in a shadow-frame slot, a static root or a
heap field (raw C locals never hold refs), so the question is well-defined.
Two forms: an EXACT on-demand mark pass counting edges into x (O(live
heap), stop-at-2), and an AMORTIZED watch-list variant answered as of the
last collection (edge-counting piggybacked on the trace — nearly free, and
conservative in the safe direction for copy-on-write reuse). The API wants
a transactional shape (`GC.reuseIfUnique x (fun exclusive -> ...)`) so the
reference cannot escape between check and use. Under threads the query
runs at a safepoint. Also unexposed but present in the runtime: finalizers
and heap introspection (live bytes, per-type census).

First customer (decoupled from threading — can land any time): ADAPTIVE
cache eviction. Watch the AVAL node itself: when the sweep sees that no
reference outside the graph/cache can PULL the aval again, its cached
output is droppable — e.g. a vertex array already uploaded to the GPU
loses its CPU copy. The watch-list variant fits exactly: eviction is a
periodic sweep after commit, so answers-as-of-last-GC are safe (staleness
only defers a drop), and the cache's own lookup path is the only door a
reference could escape through between sweep and drop.

## Order of work

1. Async CE + event loop (no threads; useful on every backend immediately).
2. Runtime groundwork: TLS, safepoint polls at back-edges, real Monitor,
   the pool. Native first, gates green, then the emcc `-pthread` leg.
   PARTIALLY DONE (2026-08-06, c8897ef): multi-mutator runtime — TLS
   shadow stacks, attach/detach/park/unpark, thread-safe idhash, inline
   safepoint polls at loop back-edges, `make test-threads` (6 mutators
   under GC churn, pcc+mmc). Still open here: real Monitor, the pool,
   the emcc `-pthread` leg.
3. Phase engine: chunked dispatch, groups, work-stealing, barrier-as-join;
   hand-phase-split library combinators (map/fold/scan/choose) on top.
   This ships the efficient combinator library with no compiler changes.
4. The barrier-lift compiler pass: kernel fission at `Sync()`, live-set
   spilling into per-thread arrays, the uniformity diagnostic. User
   kernels now write straight-line sync code and get the phase-split form
   the library already uses.
5. Dependence analysis (ladder rung 2, then 3): affine distances →
   intra-chunk elision + halo wavefront; scan recognition.

Every step lands behind the existing gates: parity micros where output is
comparable, the adaptive gate untouched, plus a new threaded gate (a
deterministic parallel program whose output is chunking-independent) run
native AND under wasmtime with threads on.
