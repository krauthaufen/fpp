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
