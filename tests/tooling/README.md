# Tooling checks

These two exercise the debug build through the tools people actually use. They
need a display, Chrome and VS Code, so they are NOT part of `dotnet test` — run
them by hand when the debug information changes.

## chrome-debug.js — breakpoints and locals in Chrome

Builds nothing itself: point it at a directory holding `prog.wasm`,
`prog.wasm.map` and `prog.fpp` (see `EmitProgramWasmWithSourceMap`), serve it,
then:

    python3 -m http.server 8731        # in that directory
    node tests/tooling/chrome-debug.js

It reads OUR source map, picks the byte offset for a chosen source line, sets a
breakpoint there over CDP, runs the program and prints the paused frame with its
locals. What it proves: the map's offsets land in the right function, and the
locals carry the names and values the source says they should.

Note: `Debugger.setBreakpointByUrl` against the `.fpp` URL does NOT bind from
raw CDP — resolving a source map to original locations is the DevTools
FRONTEND's job, not the backend's. Hence the breakpoint by byte offset, which is
what the frontend would compute anyway.

## vscode-hover — type hovers in real VS Code

Runs the editor's own extension-test host, so the whole pipeline is live:
VS Code -> our extension -> the LSP client -> `Fpp.Lsp` -> the compiler.

    code --extensionDevelopmentPath=tests/tooling/vscode-hover \
         --extensionTestsPath=tests/tooling/vscode-hover/test/index.js \
         --user-data-dir=/tmp/fpp-vscode --password-store=basic \
         --disable-workspace-trust playground

It opens `playground/main.fpp`, waits for the server, and writes the hovers it
got to `/tmp/.../hover-out.json`.

Two things that will waste an hour if you do not know them:
* `--password-store=basic`, or a GNOME keyring dialog blocks startup and the
  extension host never runs.
* the extension resolves the server relative to the WORKSPACE, so opening
  `playground` needs `fpp.server.path` set to a built `Fpp.Lsp` binary.

## dom-externref — can wasm hold JS objects without a handle table?

    wasm-tools parse dom-externref.wat -o dom.wasm   # beside dom-externref.html
    python3 -m http.server 8731
    node tests/tooling/dom-externref.js

It builds a `<div>`, stores the JS element IN A WASM-GC STRUCT FIELD, reads it
back out, sets its text and appends it — and Chrome renders it. So: JS objects
travel as `externref`, live in locals and struct fields, and the two garbage
collectors handle lifetime between them. No integer handles, no side table.

What it does NOT remove: wasm has no instruction that calls a JS method, so
every OPERATION is an imported function. A DOM binding is one import per
operation, not a handle table.

## wasm-features — what the browser actually gives us (Chrome 150, measured)

    wasm-tools parse jsstr.wat -o jsstr.wasm   # likewise threads/sharedgc
    python3 -m http.server 8731
    node tests/tooling/wasm-features.js

| capability | result |
|---|---|
| JS string builtins (`wasm:js-string`) | YES — `length("hello wasm")=10`, `concat("a","b")="ab"` |
| shared memory + atomics | YES — module validates, atomic RMW runs |
| `SharedArrayBuffer` | only under cross-origin isolation (COOP/COEP headers) |
| SHARED wasm-GC structs (shared-everything threads) | NO — `--experimental-wasm-shared` only |
| JSPI (`WebAssembly.Suspending`) | YES |

Why each matters for a DOM binding:
* JS objects cross as `externref` — a reference, not a copy — and may live in
  wasm-GC struct fields. Identity is preserved and neither side serializes.
* STRINGS are the exception. Our `string` is an i8 array in the GC heap; a JS
  string is a different thing. Copying at the boundary is the naive answer;
  `wasm:js-string` is the zero-copy one, and it is available — so a web-facing
  API should keep text as JS strings (`externref`) and only materialise an F++
  `string` when the program inspects it.
* THREADS: linear-memory threads work today, but wasm-GC objects CANNOT be
  shared between workers yet. Anything GC-allocated is per-thread until
  shared-everything-threads ships; across workers you either share linear
  memory or message-pass, and message-passing serializes.

## jsabi — all of JS through a handful of primitives

    wasm-tools parse jsabi.wat -o jsabi.wasm
    python3 -m http.server 8731 && node tests/tooling/jsabi.js

Nothing DOM-specific is imported — no `createElement`, no `appendChild`. Ten
generic primitives reach everything:

    global(name)              globalThis lookup, the bootstrap
    get(o, k) / set(o, k, v)  properties; an index is just a numeric key
    invoke1/2(o, k, args...)  method call with `this`
    construct1(C, a)          `new`
    func(funcref)             a WASM function handed to JS as a callback
    num / toNum               numbers across
    str(i)                    interned literals

Measured result: `<button id="made" title="1970">made through get/set/invoke</button>`
— element created, properties set, appended, `new Date(0).getUTCFullYear()`
evaluated — and after two JS-side `.click()`s the wasm counter reads 2, so a
wasm function really was installed as an event listener and called back.

Two things that make or break it:
* INTERN the property names. They are `externref`s created once (the `S` table),
  not strings marshalled per call. That is where the cost would otherwise be.
* Keep the glue monomorphic — each import does one thing, so the engine's inline
  caches stay happy.

A typed `Element`/`Node`/`Document` hierarchy generates DOWN to these. The
compiler needs `externref` plumbing once (an opaque handle type, and `externref`
rather than `anyref` in import signatures); everything above that is generated
F++ code, which is what the source-level plugins already do.

## jsabi-bench — what the boundary actually costs (Chrome 150, measured)

    wasm-tools parse bench.wat -o bench.wasm
    python3 -m http.server 8731 && node tests/tooling/jsabi-bench.js

Building 20 000 elements (median of 7 runs):

| | time | vs plain JS |
|---|---|---|
| plain JS | 28.8 ms | 1.00x |
| wasm, generic get/set/invoke | 33.1 ms | **1.15x** |
| wasm, one import per operation | 21.8 ms | **0.76x** |

2 000 000 property get+set on a plain object:

| | time | vs plain JS |
|---|---|---|
| plain JS | 3.3 ms | 1.00x |
| wasm, generic ABI | 115.7 ms | **35x** |
| pure wasm loop (the floor) | 4.0 ms | |

Read it as ONE number: a boundary crossing costs roughly 30 ns, and nothing
inlines across it.

* Where each operation is real DOM work (microseconds), 30 ns vanishes — the
  generic ABI lands within 15% of JS, and purpose-built imports BEAT it, because
  the driving loop runs in wasm rather than in JS.
* Where the work is a field access (nanoseconds), the crossing IS the work, and
  it is catastrophic: JS optimises `o.counter = o.counter + 1` into inline-cached
  machine code, wasm cannot.

So: keep hot state in wasm-GC objects and cross at the granularity of DOM
operations, never per field. A generated binding should also prefer a dedicated
import per operation over generic `invoke` — same shape for the author, fewer
crossings, and it measures faster than hand-written JS.

Intern property names into globals (this file does, via `initNames`) — naming a
property with a per-call `str(i)` costs an extra crossing each time, which was
worth 46x -> 35x on the property loop alone.

## Making the generic path cheaper — and whether to bother

`jsabi-bench2.js` (2 000 000 property get+set, Chrome 150):

| | time | vs plain JS | per crossing |
|---|---|---|---|
| plain JS | 3.3 ms | 1.0x | |
| generic, values BOXED through externref (4 crossings) | 84.0 ms | 25.5x | 11 ns |
| generic, TYPED accessors (2 crossings) | 51.3 ms | 15.5x | 13 ns |
| typed + monomorphic accessor built with `new Function` | 55.2 ms | 16.7x | 14 ns |
| a dedicated import per property (2 crossings) | 45.7 ms | 13.8x | 11 ns |

* A crossing costs ~11 ns and that is the whole story: it does not matter
  whether the JS side is generic `o[k]` or a purpose-built `o.counter`.
* TYPING the accessors is the win — `getNum`/`setNum` instead of
  `get`+`toNum`/`num`+`set` halves the crossings: 25.5x -> 15.5x, free.
* Specialising the JS side with `new Function` MADE IT SLOWER. Measured, dropped.
* Dedicated imports beat typed-generic by only 12%.

`import-cost.js` — what "one import per operation" costs if you emit them all:

| imports | module | build the JS glue | compile | instantiate |
|---|---|---|---|---|
| 40 | 1.3 KB | 0.1 ms | 0.5 ms | 0.0 ms |
| 500 | 16.8 KB | 0.5 ms | 0.4 ms | 0.3 ms |
| 2000 | 70.0 KB | 1.8 ms | 0.4 ms | 1.2 ms |
| 5000 | 178.4 KB | 4.6 ms | 1.3 ms | 3.2 ms |

But that ceiling is never reached, because DEAD-CODE ELIMINATION ALREADY PRUNES
UNUSED IMPORTS: declare 300 `extern`s, use two, and the module contains exactly
`domOp7` and `domOp42`. So a generated binding costs only what a program
touches — generate the whole WebIDL surface as typed `extern`s and let the
compiler drop the rest. The typed generic primitives stay for the genuinely
dynamic cases, where the property name is not known until run time.

## events — the event object, and handlers that carry state

`events.wat` installs a WASM FUNCTION as a `mousemove` listener and, from
inside wasm, reads the event's `type` (a string), `clientX`/`clientY` (numbers),
the NESTED `target.id`, and calls `preventDefault()` on it. Measured result:

    wasm read from the event : mousemove|37|91|stage
    event.preventDefault() called from wasm: true

So every field, nested object and method on an event is reachable. Cost is a
non-issue here: ten fields is ~110 ns, and even at 240 Hz that is 26 us per
second of wall clock. Events are not where the boundary hurts — tight field
loops are.

`closures.wat` is the part that actually needs designing. An F++ lambda is a
struct of code plus captured environment, not a bare `funcref`, so JS cannot
call it directly. The bridge is three lines:

* wasm exports ONE `applyCallback(closure, event)`,
* the JS import `makeCallback(clo)` returns `ev => applyCallback(clo, ev)`,
* the closure travels as `anyref` — a GC reference, no table, no leak.

Measured: two listeners built from the same code with different captured state,
fed events with `detail` 5, 7 and 100, end up holding 12 and 100. Captured
state and the event object are both live inside the handler.

Two consequences worth knowing:
* `preventDefault()` must happen synchronously, so a handler that defers to a
  promise before deciding has already lost the chance.
* The listener arrives typed as `Event`. Which concrete type it really is comes
  from the event NAME, so a generated binding should type `addEventListener` by
  name (`"mousemove" -> MouseEvent`) rather than making callers downcast.

## threads — what exists today (Chrome 150, measured)

    python3 tests/tooling/coop-server.py     # COOP/COEP, or SharedArrayBuffer stays off
    node tests/tooling/threads.js

    crossOriginIsolated : true
    sharedArrayBuffer   : true
    memoryIsShared      : true
    atomic     : 4 workers x 200000 atomic increments -> 800000 (expected 800000) in 76 ms
    nonAtomic  : same without atomics -> 676438 (races lost 123,562 increments)

Real parallelism, real shared state: four Workers instantiate the SAME module
over ONE `WebAssembly.Memory({shared:true})` and hammer one address. With
`i32.atomic.rmw.add` every increment lands; without atomics 123 562 of them are
lost to races — which is the proof that the workers genuinely run at the same
time on the same memory.

What that does NOT cover, and it is the part that matters for this language:

* Threads live in LINEAR MEMORY. Every F++ value is a wasm-GC object, and GC
  objects CANNOT be shared between threads — shared structs are
  `--experimental-wasm-shared` only (measured in wasm-features above). So a
  record, a list, a HashMap cannot be handed to a worker today.
* There is no thread SPAWN in wasm on the web: you create Workers in JS and each
  instantiates the module. `wasi-threads` and shared-everything-threads are the
  proposals that change this.
* What IS shareable today is exactly what F++ already puts in linear memory:
  PINNED POD arrays (`Array.pin`). That is the seam a parallel numeric kernel
  would use — pin, hand the address to workers, unpin — while everything
  GC-allocated stays on its own thread.
* COOP/COEP headers are mandatory. Without cross-origin isolation
  `SharedArrayBuffer` is simply absent, which is why the earlier probe reported
  it as false.

## postmessage — workers WITHOUT cross-origin isolation

    python3 -m http.server 8731        # no COOP/COEP on purpose
    node tests/tooling/postmessage.js

    page is cross-origin isolated : false | SharedArrayBuffer: false | Worker: true
    round trip to a worker and back (median of 9):
        1 KB   copy    0.10 ms   transfer   0.100 ms
        1 MB   copy    2.60 ms   transfer   0.100 ms
       16 MB   copy   69.80 ms   transfer   0.300 ms
      structured clone of a 50k-element array: 4.50 ms

Workers and `postMessage` need NO isolation — only `SharedArrayBuffer` does. So
a worker pool is available everywhere, and the cost depends entirely on how the
data travels:

* COPY (structured clone): ~2.6 ms per MB, and it scales with size — 16 MB costs
  70 ms per hop. A 50 000-element JS array costs 4.5 ms just to clone.
* TRANSFER (an ArrayBuffer in the transfer list): 0.1-0.3 ms REGARDLESS of size.
  It is a move, not a copy: the sender loses the buffer. 16 MB crosses 230x
  faster than copying it.

For this language that maps cleanly onto what already exists: GC objects
(records, lists, HashMap) cannot cross without being serialized, but a PINNED
POD array is bytes in linear memory, so it can be handed over as a transferred
ArrayBuffer for the price of a move. A worker pool that owns its own module
instance and exchanges pinned buffers is the design that works today with no
special headers.

Caveat: a non-shared `WebAssembly.Memory`'s own buffer is not transferable —
detaching it would break the instance. Copy the region into a fresh ArrayBuffer
(one copy) and transfer that, or use COOP/COEP and share the memory outright.

## worker — a typed worker over postMessage, in a real browser

    python3 -m http.server 8733 --directory tests/tooling/worker
    node tests/tooling/worker/run.js

    Sum of 3 points  : answer 18 (expected 18), sent 57 B, got 21 B
    Scale of 3 points: answer 3009 (expected 3009), sent 65 B, got 57 B
    Sum of 10000 points: answer 150015000 (expected 150015000), sent 160009 B in 2.2 ms
    bytes per point  : 16.00 (a V2d is 16)

`geo.fpp` is ONE module, instantiated twice: once on the page and once inside
the Worker, each with its own heap. `Worker<Geometry>` fixes `Command = Job`
and `Reply = Answer` as associated types, so both ends of the crossing are
generated from that one declaration and cannot disagree.

The wire has no header, no field names and no type tags — only a 4-byte
length so a host that cannot see the F++ types knows how much to hand over,
and one byte per union to say which case. A `V2d[]` costs exactly 16 bytes
per point, because a pinned array of an all-scalar struct IS its own C-layout
image: `writeArray` ships it with one `memory.copy` rather than walking it.

Copies per hop, on a page with no cross-origin isolation: pin (GC -> linear,
free if the array is already pinned), one copy out to a fresh ArrayBuffer,
the transfer itself (a move, free), and one copy into the other instance's
memory. With COOP/COEP and a shared memory the two middle steps go away and
only the pointer travels.

## abi — the pinned array stride, against a real C compiler

    ./tests/tooling/abi/run.sh

    emscripten:                 F++:
      V3f sizeof=12 stride=12     12
      V2d sizeof=16 stride=16     16
      V2f sizeof=8  stride=8       8
      V3i sizeof=12 stride=12     12
      V3d sizeof=24 stride=24     24

A pinned POD array is meant to be the array a C function would walk, so the
stride has to be C's. It is, because the backing store is chosen PER STRUCT
from its alignment — one, two, four or eight bytes. A size is always a
multiple of its alignment, so an element is always a whole number of words and
nothing is ever rounded up.

One fixed width cannot do that. Sixty-four-bit words gave `V3f` 16 bytes where
C gives it 12, so a foreign reader walking by 12 drifted by one float per
element — invisible from inside F++, where both ends agreed, and wrong the
moment anything else read the buffer. Thirty-two-bit words fixed that but left
`C3b` at 4 bytes instead of 3, and byte-sized fields were not blittable at all:
`Array.pin` rejected them.

Choosing per struct also made the wide types FASTER, because the word is now as
wide as the field: reading an `f64` out of a `V2d[]` is one array read where
32-bit words needed two and a shift. 32M field reads went from 999 ms to
599 ms — the same cost as reading a float.

The battery pins these strides as constants; this script is what checks them
against a compiler rather than against a reading of the ABI.

## perf — the same vertex loop in C and in F++

    ./tests/tooling/perf/run.sh

Fill a 1M-element `V3f[]`, then sum every component 20 times: 60M reads.

    C native (gcc -O2)     45 ms
    C -> wasm (wasmtime)   59 ms     wasm itself costs ~31%
    .NET steady state     100 ms     JIT, native, real structs
    F++ -> wasm (same)    174 ms

Both C and F++ run as wasm under the same wasmtime, so that pair is the fair
one: 2.9x. The .NET figure is steady state — `vertices.dotnet.fs` runs the
measurement ten times in-process and the first round (155 ms) is JIT warmup,
after which it sits flat at 100. Worth noting that nothing here reaches C:
.NET, with a mature JIT and no wasm in the way, is 2.2x native C on this loop.

Where the remaining F++ gap is, exactly. For one field read clang emits

    f32.load offset=1728

having strength-reduced the index into a walking pointer and folded the
field's byte offset into the load. F++ emits seven instructions, rebuilding
the address from scratch:

    local.get 3  local.get 13  i32.const 2  i32.add
    i32.const 4  i32.mul  i32.add  i32.load

Six extra ALU ops per read, three reads per iteration: 18. That LOOKS like
the 5.45 ns of measured overhead per iteration, about 19 cycles.

It is not. Strength reduction was then built, and took the nine multiplies in
the loop down to one — for no gain at all (175 ms without it, 172 with, and
slower on two other benchmarks). Those ops are independent, so the CPU issues
them alongside the work that matters. The gap is somewhere else, and counting
instructions will not find it.

`shapes.c` / `shapes.fpp` run the same comparison over five struct shapes at
once — a 12-byte vector, a pair of doubles, a 4-byte colour, a mixed
double+byte, and a NESTED struct of two points — reading and writing all of
them. That one is 870 ms against C's 249 ms (3.5x). The nested struct is why
it is not 2.7x: it was 20x until field chains like `e.[i].Lo.PX` were taught
to fuse, which is the shape a benchmark over one struct type never exercises.

Two things dominated before, and neither was the read.

Storing a record literal into a POD array used to materialize a GC struct and
read it straight back apart. The allocation is cheap in isolation — a million
of them against a one-element array costs 289 ms — but a live POD array is
LARGE, so a million short-lived objects make the collector trace 12 MB over
and over. Filling the array cost 3246 ms that way and 189 ms once the fields
are written straight into the image, unboxed. That is the whole difference
between 3615 ms and 919 ms here.

Reads were never the problem: 20M POD field reads cost about 100 ms, roughly
5 ns each, against ~1.7 ns for a packed primitive array. An early reading of
this benchmark blamed the reads and was wrong — the fill was being counted as
read time.

Reads are emitted INLINE rather than as a call to `$hwget`. A call is an
optimisation barrier — the engine has to assume it writes globals, so it
cannot hoist the array fetch or the surrounding casts out of a loop.

The base of every POD array a loop touches is now HOISTED out of it. Nothing
about that base — the storage and the pin pointer — can change while the loop
runs, so an access that used to be `global.get`, `ref.cast $hnd`,
`struct.get`, `ref.cast $pk`, `array.get` is now just the load. A loop that
pins is left alone, since pinning moves the storage.

    filling a 1M V3f[]      189 ms -> 51 ms
    fill + 20M reads        441 ms -> 193 ms
    the whole benchmark     656 ms -> 328 ms

Two more followed, and neither is loop-specific:

A top-level `let` bound to a literal is now the literal at its use sites. It
was a global load plus an unbox — in `while i < n`, on every iteration.

An element read no longer asks whether the array is pinned unless the program
pins that type SOMEWHERE. Nothing else can put a POD array in linear memory,
so if no `Array.pin` mentions the type, the test is dead and every read drops
a branch. That one step was 298 ms -> 191 ms.

All three are off in a debug build: hoisted bases and elided branches are
invisible in the source, and a debugger stepping through them has nothing to
point at.

    filling a 1M V3f[]      189 ms -> 50 ms
    fill + 20M reads        441 ms -> 146 ms
    the whole benchmark     656 ms -> 191 ms
    let e = v.[i]           57.6 s -> 10.0 s

`let e = v.[i]` is no longer a cliff. It used to materialise a GC struct per
element — 57.6 s — and now splits the element into unboxed locals, which is
the same value since a POD element is a value: 202 ms, level with reading the
fields directly. It only applies when every use in the body IS a field read;
anything that wants the element itself still gets one.

An offset cache for `i * stride` across the fields of one element was tried
and dropped: it made no difference, so the engine is already doing it.

`let e = v.[i]` also remains: it materializes the element and is ~60x slower
than reading its fields directly — the same allocation problem the store side
had, seen from the read side.

## perf/shapes — does it hold for structs other than the one benchmarked?

    ./tests/tooling/perf/run.sh          # one shape,  191 ms vs 71 ms
    # shapes.c / shapes.fpp              # five shapes, 870 ms vs 249 ms

Bounds checks were investigated here and turned out to be a non-yak: nothing
in the emitted code checks a bound, because `array.get` checks it itself and
wasm-GC offers no unchecked read. Pinning the array — which reads linear
memory with a plain load, no per-element check — is worth 8%, 191 ms against
175 ms. And `for i in 0 .. arr.Length - 1` already hoists its bound.

Worth keeping honest: the single-shape number (2.7x) is the best case, and
the mixed one (3.5x) is closer to what varied code sees. Every optimisation
here was written against the single shape first and then found wanting on the
mixed one — nested structs fell off the fused path entirely and cost 20x
until the field-chain flattening landed.

## perf/add and perf/read — where the gap to C actually is

Two loops, each in C and in F++, both compiled to wasm and run under wasmtime.
`add` is 20M iterations of one dependent `f64` add and nothing else. `read`
is the same loop with ONE field read from a 1M-element `V3f[]` added to it.

    add    C 39 ms    F++ 41 ms     parity
    read   C 49 ms    F++ 115 ms

So the loop, the counter, the branch and the floating-point chain are already
at C's speed. The ENTIRE gap is the per-element read: about 0.5 ns in C and
about 3 ns here, and everything else that looked like a cause was a
distraction.

What it is NOT, each ruled out by measurement rather than argument:

* not instruction count — strength reduction took nine multiplies out of the
  vertex loop for no gain at all
* not the GC array — pinning it, so reads become plain linear-memory loads
  exactly like C's, changes nothing (111 ms against 115)
* not the bounds check — worth 8%, and pinned reads have none
* not the engine — the C reference is wasm under the same wasmtime
* not unroll depth alone — going from 2x to 4x wins 14% on this loop and
  nothing on the three-read one

C unrolls this loop 5x and folds each field's offset into the load
(`f32.load offset=1740`), which keeps several independent loads in flight
against a serial add chain. That is the leading remaining hypothesis and it
is NOT yet demonstrated: 4x unrolling should have shown more of the win than
it did. The next step is a profiler on the generated code, not another round
of reading disassembly.
