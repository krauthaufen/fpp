# The direct wasm-linear backend

Emitting wasm-linear straight from the compiler — no C compiler, no
emscripten. The wasm-GC backend already needs no C toolchain; this brings
the *linear-memory* leg to the same footing, so the whole language reaches
wasm with nothing but the compiler.

## Why a fourth emitter

Three lowerings exist: BinDriver (wasm-GC binary), CEmit (C over fpprt),
and now WasmLin (wasm-linear binary). They share the Core IR and, crucially,
WasmLin shares BinDriver's *value model* — fpprt's tagged representation —
and EmitBin's *assembly layer* (the byte encoders, the function/code
sections, the instruction emitters, `assembleWith`). What is new is only the
lowering: linear-memory loads and stores where the GC backend uses
`struct.new`/`array.get`.

## The value model

A value is a tagged `i32`. Low bit set → a 31-bit signed integer
(`(n<<1)|1`). An even value → a byte address into the module's own linear
memory. This is fpprt's model at 32 bits, so a real collector can drop in
later against the same representation.

Static memory: the fd_write iovec and a UTF-8 staging buffer live low, then
string constants (baked into an active data segment), then the bump heap
(`$hp`). Allocation is a bump with memory growth — no collection yet.

## Status: slices 1–6 (shipped) — the prelude lowers

Slice 6 crossed the milestone: the backend emits **reachable prelude code**,
not just the user program. From the user's declarations it walks the
reference graph and emits every prelude function or global reached — most of
the prelude is dropped, so a program pays only for what it uses. Lists came
with it: `[…]` and `::` are `[head][tail]` cons cells with the null pointer
for empty, `isNull` is a null test, and `PCons`/`PListLit []` patterns
destructure them. `failwith` and friends trap (no exception machinery yet;
an untaken guard never reaches it). With this, `List.map`, `List.filter`,
`List.fold`, `List.sum`, `List.length`, `List.max` and a hand-written
recursive list function all run under `--linear` and match the oracle. The
backend is no longer slice-limited to hand-picked features — it lowers the
prelude functions a program actually reaches. What a given program needs
beyond this depends on which prelude corners it touches (exceptions,
typeclass dispatch, StringBuilder, options); each is a further slice, and the
reachability report says exactly which are required.

Known gap found here: a **local recursive function** (`let rec go … = … go …`
inside a body) needs a self-referential closure — the closure must be able to
call itself before it is fully built. Top-level recursion and prelude
recursion work; a user-written local `let rec` does not yet. Options through
top-level functions and `match` work; `find` via an inner `let rec` is the
shape that waits on this.

## Status: slices 1–5



Slice 5 added **64-bit ints and floats**, boxed (an even pointer to 8 bytes):
float and int64 literals box their payload, arithmetic and comparisons unbox
/ op / re-box, and the conversions (`int`↔`int64`, `int`→`float`) cross the
representations. `printfn "%f"` is a hand-emitted `$ftoa6` — the oracle's
fixed-six-decimals routine (NaN, sign, round at 5e-7, i64 integer part, six
fractional digits) ported to the linear string layout — and it matches the
oracle byte for byte on arithmetic, division, negatives and int-to-float.
The 31-bit tag cannot hold an `int` above 2^30, same as any tagged-integer
model; such values box when the full-width int path lands with the prelude.



Slice 4 added **arrays** (boxed elements): the layout is `[len][elem…]` with
a raw length word and tagged element slots. Literals, indexing, index
assignment, `.Length`, and `Array.zeroCreate`/`Array.create` (a fill loop,
depth-indexed scratch) all match the oracle — including a build-then-mutate
and a summation loop. The oracle stores `int[]` in a packed representation
and this backend boxes it, but the integer results are identical, which is
what the diff checks. Packed/POD element layouts and pinning are a later
slice; `Array.length` (a prelude function rather than the `.Length` node)
lands when the prelude lowers.



Slice 3 added **records, unions, tuples and pattern matching**. Layouts,
static-typed so no runtime kind word is needed: a record is its fields in
declared order; a tuple is its elements; a union case is `[tag][payloads…]`
with the tag the case's index. Construction allocates and fills (nesting-safe
via a depth-indexed base/value scratch pool); field access is a load at the
declared offset; `match` compiles to a linear scan of clauses, each a block
whose pattern test branches out on mismatch and binds variables on the
matching path, with `unreachable` after an exhaustive set. Records, sum types
with mixed arities, tuple destructuring and nested patterns all match the
oracle. Lists, or-patterns and `:?` type tests await a later slice.



Slice 2 added **closures**: nested lambdas are lifted (curried to unary) to
`(env, arg) -> result` functions in the code table; a closure is a heap
object `[kind][code-index][captures…]`; free variables are captured into
that env and read back from it; indirect application is `call_indirect`
through table 0 with the closure as the environment. Higher-order
functions, capture (including a mutable captured through a closure), and
composition all match the wasm-GC oracle. The backend lowers UNOPTIMIZED
core — the optimizer shares and beta-reduces lambda nodes, which the
reference-keyed lift is not built for; speed is a later concern than
coverage. Still open in this area: a top-level function used as a
first-class VALUE (eta-expansion / `let f = someFn`) — inline lambdas cover
the common case meanwhile.

## Status: slice 1 (shipped)

`fpp build --linear -o out.wasm prog.fpp` emits a module that runs under
wasmtime with nothing but a wasm runtime. The slice:

- integers, arithmetic (`+ - * / %`) and comparisons (`< > <= >= = <>`),
  through their type-suffixed forms;
- `let` bindings and top-level mutable globals;
- top-level functions, direct calls, recursion;
- `if`, `while`, assignment, sequencing;
- string literals, int-to-string, string concatenation, `printfn`.

Gated by `tests/tooling/cback/wasmlin-gate.sh`: the direct module's output
is diffed against the wasm-GC oracle for the same program — two independent
emitters, one meaning. It runs recursion (fib, factorial), a `while`-loop
gcd, string output and a summation, and the two agree.

The backend emits only the user program's declarations; the prelude and its
startup initializers are outside slice 1, and a program that stays inside it
never needs them. A reach outside the slice is reported, never mis-emitted.

## The road to a full backend, in order

1. **Closures and indirect calls** — a closure is a heap object holding the
   code-table index and the captured environment; `call_indirect` through
   table 0, exactly as the GC backend does but with the env in linear
   memory.
2. **Records, unions, tuples** — heap objects with a kind word and fields;
   `EField`/`ECtor`/`EMatch` become loads and tag tests. The layout
   decisions are already made in CEmit; port them.
3. **Arrays** (boxed and POD), pinning — the interop story reuses the same
   linear memory the GC backend copies *into*, so pinning is free here.
4. **64-bit ints and floats** — boxed on the heap (an `i64`/`f64` payload),
   the way the GC backend boxes them, or unboxed where a local's type is
   known.
5. **The prelude** — once the above lands, the whole prelude lowers, and the
   backend runs arbitrary programs. This is the milestone where `--linear`
   stops being slice-limited.
6. **A collector** — the bump allocator gains a real GC. The value model is
   fpprt's, so the design choice is which collector to hand-emit (a
   semispace copier is the smallest honest one) versus compiling one of the
   vendored collectors to wasm once.

Each step is a self-contained addition to `Backend/WasmLin.fs` behind the
same gate, growing the diff-against-oracle program as coverage grows.
