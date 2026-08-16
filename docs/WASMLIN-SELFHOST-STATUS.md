# WasmLin `--gc` self-host — status (2026-08-16)

Goal: the wasm-linear backend self-hosts the F++ compiler byte-exactly under
`--gc` at the **default 16 MB growable heap**, with real collections firing.
Probe: compile `module M\nlet a = 1`, run the compiled compiler to completion,
`cmp` its emit against the .NET oracle's (`/tmp/oracle.wasm`, 77860 bytes).

Standing rules: root-cause, never mask; measure, do not reason; `fixpoint.fsx
self` (the wasm-GC backend's byte-exact self-compile) must hold after every
change. F# builds need the sandbox disabled.

**Branch: `lowir-vtable-wip`** (the work had continued on a detached HEAD;
this branch now names it). Runtime repo (`~/projects/fpp`) has matching
commits — the reactor at `/tmp/bigreactor/fpprt_reactor.wasm` must be rebuilt
via `tests/tooling/gc/build-reactor.sh` after runtime changes.

---

## 1. Done — the architecture, complete and validated

The full inline-value model shipped on wasm-linear, all byte-exact-gated:

- **Nothing boxed.** `int`/`bool`/`char`/`uint32` are raw i32 at rest
  (full 32-bit — the 31-bit tagged limit and its stubs are gone).
- **.NET-parity struct layout** (`layoutOf`: size/align/refMask; the abi
  harness matches emscripten exactly on all 8 shapes).
- **Precise GC scanning** by per-type ref-offset maps (`FK_STRUCT` +
  `g_refoffs` pool) for records, arrays, tuples, unions, cells, globals,
  closure envs, cons cells.
- **Generics by value witnesses** (`{size, align, refMask}` in the immortal
  `g_witnesses` pool): hidden leading args on generic functions, forwarded
  via `EVarI.inst` (`"#N"`), captured into lifted-lambda closures, class
  type-params via receiver slots / `stampedClassWits`, witness-selected
  cons/aggregate tids (`CONS_RAW`/`CONS_REF`, per-refmask FK_STRUCT interns).
- **Collector fixes** (vendored Whippet semi-space, growable):
  `semi_space_contains` across growth, stale-forwarded-edge handling, plus
  `FPPRT_HEAP_MB`/`FPPRT_HEAP_FIXED` env controls.
- **Store-order fix** (`19b8cc0`): an `LStore` evaluates its address before
  its value; an allocating value moved the receiver and the store wrote the
  dead copy (prune's path compression did exactly this). All four store
  shapes (field, RecPod-ref field, ref-array element, cell) now root the
  receiver across the value via `evalRooted`.
- **Runtime-conditional rooting for type-lost binders** (`b123fe9` +
  runtime `c25456c`): see §3.

Long fix history with commit hashes: `git log` on this branch, task #70's
metadata trail, and the project memory. Highlights: union-case cid+tag
discrimination, `$cmpv` bounds + per-tid ref-bitmask, `List.fold`
accumulator/ActiveGen exclusion → persistent write-through slots, eta HOF
param typing, ctor-as-value eta closures, enumerator `isBuiltinSeq` tids,
class-witness (`stampedClassWits`), stamped-subclass field/construction
resolution through base.

## 2. Where the self-host stands

- **wasm-GC path (BinDriver): byte-exact throughout.** `fixpoint self`
  reproduces stage-0 byte for byte after every change on this branch.
- **`--gc` linear self-host at a large fixed heap** (`FPPRT_HEAP_FIXED=1`,
  900 MB): **runs to completion** and emits a valid module — 65219 bytes vs
  the oracle's 77860. The gap is 105 member bodies the compiled compiler
  stubs where .NET stubs none ("unbound variable" / "capture not in scope"
  in prelude enumerator members) — task #69, a capture/resolution
  divergence to bisect (shrink with `FPP_PRELUDE_TRUNC`).
- **`--gc` linear self-host at 16 MB growable** (the honest target): still
  traps. The crash class is fully understood — see §3 — and has been
  driven through many instances; each fix moves the fault to the next
  unrooted holder. Remaining instances exist.

## 3. The 16 MB crash class: values whose static type was lost

Under raw-at-rest + precise rooting, every value must be classifiable
(raw / ref / witnessed-generic). A value whose static type reaches the
backend **unresolved** (an unlinked `TVar` or the anonymous `TCon "?"`)
can be neither rooted (might be raw — a pushed even int gets mis-traced)
nor skipped (might be a pointer — unrooted it goes stale across a GC).
The mutator then walks stale-but-readable old-generation memory and
eventually dereferences garbage (deterministic fault, address moves with
any recoloring — the session's "heisenbug").

Where the types get lost (measured, WDROP/WDROP2 probes):

1. **`EMatch` pattern binders** from Lower's desugars — the pattern-lambda
   (`fun (p,_,b) -> …` → match over `_arg : ?`) and the for-in-list walk
   (match over `_rest : ?`). Exactly 4 in the whole compiler.
   **Covered** (`b123fe9`): `patCondBinders` + the reactor's
   `fpprt_tid_scans(tid, off)` ask the *scrutinee object's own scan map*
   at runtime whether the bound slot holds a pointer, and root
   conditionally through the SlottedGen machinery with a fabricated
   1-word witness. Top-level PCons/PTuple/PCtor positions.
2. **`?`-typed let binders** — Lower's desugar temps (`_rest`, `_tail`,
   `_arg`, `_arr`, slice/range temps). Refs by construction.
   **Covered** (`b123fe9`): whitelisted in `shouldSlot` (write-through
   assign path already existed).
3. **Lambda args with unresolved schemes** — `rootArg` required concrete
   `RKRef`; a `'a`-typed arg was never rooted.
   **Covered for witnessed args** (`b123fe9`): witness-conditional arg
   rooting via SlottedGen when the lambda's captured witnesses include the
   arg's tvar.
4. **Remaining instances** — the crash still fires (fault last seen
   `0x12dd5a00`-class, frames in the substVars/mapExpr walk lambdas
   `blam1145/1148/1570/1587`). Suspects, in order: lambda args whose tvar
   has **no** captured witness (case 3's residue); multi-param lambda
   chains; `?`-typed values reaching aggregates outside the covered
   binder positions. Method: same probes (add a WDROP-style counter for
   the uncovered category, enumerate, cover with the same conditional
   machinery or thread the type).

The **structural** fix that ends this class outright: make the frontend
never lose these types — record instantiated types for desugar temps and
lambda params (the lambda/desugar analogue of `EVarI.inst`). Gated by
fixpoint-self byte-exactness since Lower/Infer are shared; if bytes move,
scope to a WasmLin-only side channel (the `stampedClassWits` pattern).

## 4. NEW: pre-existing non-gc regression (must bisect)

`tests/tooling/cback/wasmlin-gate.sh` (non-gc `--linear`) **aborts** with a
NullReferenceException in `EmitBin.gg` (a global-name lookup) at emission —
at `19b8cc0` **and** at `619047b`, i.e. it predates 2026-08-16's work and
crept in somewhere in the `413eab1..619047b` fix chain, whose gate runs
must have hit stale binaries. Small programs pass; the gate's program
(unions + `for x in` + options) crashes the compiler itself. **Bisect
this** (fast: build + `fpp build --linear` on the gate program per commit)
before trusting non-gc; it is independent of the gc work above.

## 5. Recipes

- **Self-host build:** `dotnet fsi /tmp/gchost.fsx` (compiles the compiler
  sources + `/tmp/bakeddrive.fpp` via `EmitProgramWasmLinearWith true`,
  writes `/tmp/selfhost_a.mod.wasm`; ~4 min).
- **Run:** `wasm-merge -all /tmp/bigreactor/fpprt_reactor.wasm fpprt
  /tmp/selfhost_a.mod.wasm mutator -S -o /tmp/sh.wat && wasm-tools parse
  /tmp/sh.wat -o /tmp/sh.wasm && wasmtime run -W gc=y,exceptions=y
  -W max-wasm-stack=536870912 --env FPPRT_HEAP_MB=16 /tmp/sh.wasm`.
- **Post-mortem:** `wasmtime -D coredump=/tmp/core.wasm …`; parse data
  segments (zero pages skipped), scan for holders of a value, decode
  globals; scripts in the 2026-08-16 session transcript. WAT breadcrumbs:
  patch the trapping function to store locals at scratch 224 before the
  fault, re-parse, read them from the next core dump.
- **Probes:** WDROP (uncovered match binders), WDROP2 (uncovered lets),
  WCOND (conditional-rooting sites) — grep this file's history / task #70
  for the exact `eprintfn` blocks; all run .NET-side via gchost (~5 min),
  no wasm needed.
- **Name mapping:** `FPP_FUNC_DUMP=1 dotnet fsi /tmp/gchost.fsx` →
  `f<hash> = key | name`; only named mutator frames in merged backtraces
  are trustworthy.
- Gates: `fixpoint.fsx self` (must stay byte-exact), `fixpoint.fsx`,
  `tests/tooling/abi`, unit suite, `wasmlin-gate.sh` (currently red, §4).

## 6. Order of work from here

1. Bisect + fix the non-gc `wasmlin-gate` regression (§4).
2. Enumerate + cover the remaining unresolved-value instances (§3.4) until
   the 16 MB self-host runs; prefer the structural frontend fix if the
   instance count keeps growing.
3. Task #69: the 105-stub capture/resolution divergence → byte-exact cmp
   at the fixed heap.
4. Byte-exact cmp at 16 MB growable = done.
5. Then: port a curated tier of F#'s conformance tests via a differential
   harness (dotnet fsi oracle vs `fpp --gc`/`--linear`) as the hardening
   phase.
