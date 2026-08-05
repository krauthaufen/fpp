# The C backend: F++ on fpprt

The march: every backend milestone gated on output parity with the wasm-GC
backend, until the ADAPTIVE SUITE runs green on the new runtime — native
first, then the same C through emcc as wasm-linear. The wasm-GC backend
stays untouched: it is the oracle every step diffs against.

## Shape

`src/Fpp.Compiler/Backend/CEmit.fs` consumes the SAME post-Link decl list
`BinDriver.emitBinaryWithPositions` does — monomorphized, stamped,
class-resolved. It emits ONE C file that links against `runtime/`
(fpprt + Whippet) and `runtime/fpprt-lang.h` (the language support layer:
tagged arithmetic, apply, structural equality/hash/compare, string ops).

Entry: `Workspace.EmitProgramC` -> `fpp build --target c -o out.c`.
Harness: `tests/tooling/cback/run.sh <prog.fpp>` builds BOTH backends,
runs both (gcc+fpprt vs wasmtime), diffs stdout. That diff is the gate for
every milestone.

## Value model (uniform, v0 — no POD specialization)

```
V = uintptr_t
scalar:  (x << 1) | 1        int32, bool, char, unit(=1), enum
ref:     bit 0 = 0, != 0     every heap object
null:    0
float:   boxed  (FPPRT scalar array tid $boxf, one f64)
int64:   boxed  (tid $boxi64, one int64) — full 64-bit range, always
string:  u8 scalar array (tid $str), length = byte count
```

The collector skips slot values with bit 0 set or 0 — the embedder and the
frame walker test `(v && !(v & 1))` before visiting an edge. A GENERIC
field can therefore hold a tagged int or a ref and trace correctly either
way; typed scalar fields simply never look like refs.

Objects: records/classes = fpprt STRUCT typeids (pointer map = every
V-typed field; fnptr slots and inline scalars stay off the map). Unions:
one typeid PER CASE (exact pointer maps); `case_of_tid[]` side table in
the generated C gives the match tag. Closures: struct { fnptr; captures }.
Interface dispatch: global (iface,member) -> slot assignment (BinDriver's
vtableSlots rule), `vtable[tid][slot]` fnptr table in the generated C.
Casts/type tests: typeid -> class-chain walk over a `parent_of_tid[]`.

Statics: top-level lets become V globals registered as GC roots
(`fpprt_add_static_roots`), initialized in decl order by `main`. String
literals are allocated into the heap at init (never C statics: the
collector must own every ref it sees).

Exceptions: setjmp/longjmp handler chain in fpprt-lang.h; every handler
frame also snapshots the shadow-stack top so unwinding restores roots.

## Runtime additions this needs (runtime/)

- tracing skips tagged scalars (embedder + frames)      [M1]
- `fpprt_add_static_roots(V *base, size_t n)` — multiple ranges  [M1]
- nothing else: weak = fpprt_weak, hash = fpprt_idhash, pin = fpprt_pin

## Milestones (tasks #21-#28)

- M1 core exprs: lit/arith/let/if/while/fn/call/print — fib parity
- M2 records/tuples/arrays/strings
- M3 unions/match (+ list), structural =/hash/compare
- M4 closures/HOFs (apply semantics = BinDriver's applyc)
- M5 classes/members/interfaces/vtables/casts
- M6 exceptions + remaining builtins/ops — corpus battery parity
- M7 whole prelude + dotnet.fpp 111-value parity vs dotnet fsi
- M8 adaptive suite PASSED 100 FAILED 0 on fpprt (native, then emcc)

## Standing rules

Every milestone: parity-diff vs the wasm-GC backend, committed green.
CEmit.fs stays F++-inferable (the dogfood gate reads it). The wasm-GC
gates keep running — nothing regresses behind this work.
