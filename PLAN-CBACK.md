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

## State (2026-08-05 evening)

M1-M7 CORE DONE: fib, m2-data, m3-classes and stdlib/dotnet.fpp (142
values) all PARITY OK vs the wasm-GC oracle, native gcc + fpprt(semi).
Remaining: M8 — the adaptive suite (lib.fpp + Tests.fpp), then the emcc
build, then wire the gates. Micros in tests/tooling/cback/, runner is
run.sh. FPP_CBACK_DUMP=1 prints the IR as C comments. Traps name their
gap; ASan build of the generated C gives the call path.

Learned the hard way (do not re-learn): LString/LChar carry SOURCE
spellings (use BinDriver.unescape/charCode); int literals keep suffixes
(L boxes); kind letters are f/s=f32/h=f16/l/w=u32/v=u64/t=STRING/b/c and
INT IS UNSUFFIXED (bare ops dispatch at runtime like $addv); classes are
records + member fns + DClass metadata (vtables only for EIfaceCall);
stamped record clones have EMPTY field lists (inherit the base's);
fn-closure singletons must init before ALL global inits; zeroCreate seeds
by element kind (int slots are tagged 0, NEVER null); the eqv identity
fast path must exempt floats (NaN); "$str." methods are builtins; the
seq protocol is runtime enumerators wired into the program's slots.

## M8 state (2026-08-06, deep in the trap hunt)

Suite runs 86+ tests before the slow tail. Fixed on the way, in order:
canonical fn names (instance member call-site aliases); empty EApp = its
head; stamped record names fall back to the base (recBase/recTidOf);
$zero:/$sizeof: tables; stamped-class vtables complete via the canonical
chain; abstract members dispatch via (declaring-class, member) slots
(DMembers registers them); OVERRIDES WIN interface slots (nearestOwn);
$hasflag; u~~~/u- with kinds; int64/uint64 shifts unbox; uint prints;
'?'-kind (bare) ops dispatch dynamically (fpp_addv family) with NUMERIC
COERCION for representational drift (generic zeros arrive tagged);
first-class union ctors (ctorCloGlobal singletons + direct-app fold);
interface TYPE TESTS via fpp_vt_has on a representative slot; on-demand
StructTupleN registration; class layouts are CHAIN-CONCATENATED (base
prefix; ERecord `base` entry copies the base ctor's fields); classes are
FPP_TC_CLASS (identity eq — structural eqv on the cyclic adaptive graph
recursed forever); class CompareTo registers a vt slot + fpp_reg_cmp so
`compare` uses it; identity-order fallback uses IDHASH not pointers
(ASLR nondeterminism!); **fpp_try was UB** — `return setjmp(...)` from an
inline fn collapsed the longjmp path under -O1: push bookkeeping is now a
statement and generated code writes `if (!setjmp(H.jb))` directly (the
single deepest bug of the arc; handler-pop identity checks + the hlog
ring in fpprt-lang caught it).

Two more, found chasing an mmc-only segfault in test 87 (core dump →
object at the very END of the heap mapping): **ERecordExt copied the
DERIVED layout's field count from a BASE-class instance** — a class ctor
lowers as an extension over the base ctor's result, so every ctor with a
smaller base read past the base object (harmless mid-heap: the values
are immediately overwritten; SEGV when the base sat at a mapping edge).
Both copy paths now clamp to the SOURCE object's runtime field count
(fpp_tfields_). And **WeakReference / ConditionalWeakTable are really
weak on fpprt**: the prelude bodies are strong (wasm-GC has no weak
refs) and retained every test's adaptive graph — semi grew to 17 GB over
the run. Their members are now runtime intrinsics (CSt.Intrin, DClass
registration by recBase, emitIntrinFn): WeakReference's field holds a
fpprt_weak, CWT's field 0 an ephemeron table (fpp_cwt_* in fpprt-lang,
fpprt_eph_new/key/value in fpprt). TryGetTarget returns false once the
target is collected — TRUER to .NET than the oracle, so weak-dependent
divergence vs wasm-GC is expected and correct.

**M8 IS GREEN EVERYWHERE: PASSED 100 FAILED 0 native (mmc AND semi, 64-
and 32-bit -m32) and WASM-LINEAR (emcc + wasmtime).** The wasm leg's
traps, in the order they fell: emscripten setjmp needs
`-fwasm-exceptions -sSUPPORT_LONGJMP=wasm -sWASM_LEGACY_EXCEPTIONS=0`
(default SjLj imports JS trampolines; without -fwasm-exceptions the
longjmp lowers to the LEGACY EH format wasmtime 47 rejects) and wasmtime
runs it with `-W exceptions=y`; generated field offsets are emitted as
FPPOFF(slot) = slot*sizeof(V), never bytes — wasm32 slots are 4 bytes;
an int32 beyond 31 bits cannot tag on a 32-bit V, so TAGI SPILLS to an
i64 box there (Int32.MaxValue is Transaction.RunningLevel's sentinel!)
and the eqv/cmpv drift coercion keeps spilled ints equal to tagged
twins; and emscripten's DEFAULT 64KB STACK blows on the tree recursion —
`-sSTACK_SIZE=8388608`. The -m32 native build is the cheap way to debug
wasm32 layout with gdb; gate: tests/tooling/cback/adaptive-gate.sh. The
last two failures shared one root: CLASS TYPE TESTS compared exact tids,
so `:? IndexedReader<'a>` in AbstractDirtyReader.InputChangedObject was
false for every stamped/base instance and the dirty notification was
DROPPED — every CE-built alist (append-of-bind) silently stopped
updating. Type tests on classes now collapse the tested name to its
canonical base (stamps share the base's uniform repr; instances can
carry the base tid or a SIBLING stamp's) and fpp_isa walks a per-tid
parent chain (fpp_reg_parent, emitted beside fpp_reg_struct). Remaining
leg: the same C through emcc (wasm-linear, mmc single-threaded), then
wire the gates.

The "slow tail" was a BUG, not boxing cost: cmpv on MIXED tagged/boxed
numerics said "tagged is always less", so an int64 that drifts between
representations gave MapExt an INCONSISTENT ordering — inserts looped
forever ([ASet] range systematic int64 wedged 10+ min; instant after).
cmpv AND eqv now coerce the mixed case numerically (hashv already
agreed by accident). More from the same hunt: classes overriding
Equals/GetHashCode dispatch through vt slots (fpp_reg_eq/fpp_reg_hash,
same shape as CompareTo; nullary members may carry a unit param — pass
VUNIT) — Index is VALUE-keyed in dictionaries, identity hashing lost
logically-equal instances and collecti left stale elements behind;
$idhash builtin (GetHashCode with no override); op @ = fpp_append —
note bare "@" must match BEFORE the "op@Type" family case; fpp_vcall
treats a NULL receiver as the EMPTY SEQ on the GetEnumerator/MoveNext/
Dispose slots (null IS the empty list — String.concat over [] died),
slots handed over via fpp_seq_slots; DUCK-TYPED enumerator classes
(MoveNext/Current/GetEnumerator members, no interface) wire into the
IEnumerator/IEnumerable slots too — the 8525a21 nearestOwn rework had
dropped them and dotnet.fpp's gate was not rerun (it broke silently:
rerun EVERY gate after touching vtables).

Harness notes: suite stdout is block-buffered into files — run under
`stdbuf -oL` or a timeout kill eats every RUN line; micros in
tests/tooling/cback; run.sh (semi); FPP_CBACK_DUMP/FPP_CBACK_CHECK/
FPP_GC_LOG/FPP_GC_CENSUS/FPP_HEAP_MB switches.

## The allocation diet (2026-08-06, after M8)

P1 (raw-value layer, commit e10470a): kind-suffixed op chains, conversions,
float math, if-phis, seq tails, MUTABLE LOCALS and PROVEN-primitive PARAMS
compute in raw C locals (rawKindOf predicate — PURE, never emits — decides;
emitRaw emits; boxes only at uniform boundaries: calls, fields, captures,
returns). Box-heavy loop bench 0.62s -> 0.016s; the oracle runs it in
0.026s. Raw locals are plain C locals — invisible to the collector, so no
frame-slot cost either.

P2 (scalar arrays, commit 793c659): float/float32/int64/int/char+uint16/
byte+bool arrays store RAW elements (int16/sbyte stay ref arrays — the
unsigned storage would lose their sign). Typed sites go through
fpp_arr_get_f64-style accessors that never allocate; generic code uses
tid-DISPATCHING fpp_arr_get/set, so generic-created ref arrays and typed
scalar arrays interoperate without type descriptors. Scalar tids answer
the seq protocol (vt wiring + enumerators). Bycatch: float ToString now
ports the oracle's $ftoa DIGIT-FOR-DIGIT (%g printed e-notation — parity
never caught it because dotnet.fpp's floats are small), and `prints` no
longer double-newlines (it mapped to the newline-adding printer; the
suite's internal PASS check couldn't see it, byte-diff did).

P2.5 (raw direct-call ABI, commit 49f84df): FnSig/FnRet registry from the
post-mono schemes; DIRECT calls pass proven-primitive params and results
as raw C values (gcc inlines through them); the uniform (self,args)
wrappers un/box at the closure/vtable boundary; intrinsic members keep
the uniform ABI. Call-heavy float bench: 14x FASTER than the oracle.
The adaptive suite's wall time is unchanged (0.53s) — after the cmpv
fix it is not allocation-bound.

DECIDED (2026-08-06): the 32-bit int32 spill STAYS — accepted for real
32-bit ints at uniform positions (wasm32's 31-bit tag cannot hold
int32; the static alternative — always-boxing — turns every tagged
pointer-compare into a structural call). Typed locals, params, arrays
and the direct-call ABI carry int32 raw and never spill; 64-bit tagging
is branch-free everywhere.

What still boxes: f64/i64 fields of ORDINARY records/classes — the
oracle's wasm-GC layout is all-anyref for those too, so cback matches
oracle cost there; mutable class fields hold CELLS whatever their
declared type, so field rawification by declared type alone is UNSOUND —
any typed-field work must mirror BinDriver's cell rules.

STRUCTS are a SEMANTIC GAP, not a cost gap (corrected 2026-08-06: C
interop and PINNING make layout observable behaviour — the abi gate
tests/tooling/abi checks the oracle's layout against emscripten). The
spec (PLAN.md "native: direct C ABI, blittable structs" + user):
structs have FLAT memory layout and live on the STACK, copied by value.
BLITTABLE structs (all-POD fields) additionally have C-COMPATIBLE
layout (the abi gate's clang-natural-alignment rules) — locals are C
struct values, arrays of them are flat C-compatible storage, so
pinning/blit/interop are byte-correct. Structs HOLDING REFS are also
flat and stack-resident but need no C compat: scalar-replace into
locals (raw fields as C locals, ref fields as shadow-frame V slots so
the precise GC sees them); arrays of them store flat with PER-ELEMENT
pointer maps (an embedder extension: elemsize + elem ref-offsets).
This is the P3 arc, riding on the oracle's canonName/per-stamp layout
machinery, not on the uniform-stamp rule cback uses today.

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
