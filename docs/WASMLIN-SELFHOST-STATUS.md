# WasmLin `--gc` self-host — status (2026-08-16, evening)

**MILESTONE: the 16 MB growable self-host RUNS TO COMPLETION** (`DONE
bytes=65219 hash=703075731`, exit 0, real collections firing). The crash
class of §3 is closed. What remains is task #69: the 65219-byte emit vs the
oracle's 77860 (the ~105 silently-stubbed member bodies), then the byte-exact
cmp. See §3.6/§3.7 for the two fixes that ended the crash hunt.

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
- **`--gc` linear self-host at 16 MB growable** (the honest target):
  **RUNS TO COMPLETION** — `DONE bytes=65219 hash=703075731`, exit 0.
  Same emit as the fixed-heap run, so the remaining work is task #69's
  divergence, not GC. NOTE: `/tmp/bakeddrive.fpp` was stale (referenced a
  stripped probe vec `wildLog`); those driver lets became CONSTANT 0.
  That IS recorded — a stubbed INIT stores 0 by design and adds a
  `stubbed` entry to `st.Warnings` — but two accounting gaps hid it:
  `EmitProgramWasmLinearWith` never copies `st.Warnings` into
  `Workspace.EmitWarnings` (BinDriver's path does), and gchost counted
  that empty list. `FPP_LINWARN=1` prints the real list. The driver now
  prints `DONE bytes=<n> hash=<djb2 & 0x3fffffff>`; to ENUMERATE task
  #69's 105 stubs from inside the wasm run, print `ws.EmitWarnings` in
  the driver (the self-host compiles the corpus with its wasm-GC
  backend, which DOES populate it).

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
4. **Eta-expansion params** (`fun $eN -> f $eN` for functions-as-values):
   peeled types left `'a` unresolved when the wrapped head carried an
   instantiation. **Covered** (`f35c67c`): `wrap` substitutes `EVarI.inst`
   into the peeled param schemes (14 uncovered args → 6).
5. ~~Remaining instances~~ — RESOLVED; they were not type-lost lambda args
   at all. The final 6 uncovered args (WDROP3: blam1350 $e501 / blam1555
   f2 / blam3961 item / blam4661/4664/4665 sch) were never in a crashing
   frame and are still uncovered — benign so far.
6. **The match SCRUTINEE across clause guards** (the actual blam1145/1148
   fault): the scrutinee register was never rooted. A clause guard can
   allocate; a FAILED guard falls to the next clause's tests, which re-read
   the stale register (mapExpr's `| P when g e -> …` chain — offset-print
   `wasm-tools print --print-offsets` showed the faulting `t2c +
   (hdr>>1)*4` load right after a guard-fail `br_if`). **Fixed**: when any
   clause pattern dereferences the scrutinee (ctor/tuple/cons/list/
   type-test/string/null patterns — then it is a pointer at runtime
   whatever its static type), the scrutinee lives in a shadow-stack slot
   for the whole match and the register is reloaded at each clause entry.
   Ref/gen/cond binders are now slotted BEFORE the guard runs (they were
   seeded from registers after it — same staleness on the matched path),
   and a failing guard pops what its clause pushed.
7. **Local cell vars (captured mutables) were never rooted** (the
   collector's edge-integrity `unreachable` after §3.6 landed): a `let
   mutable` that a closure captures becomes a heap cell, but the LOCAL
   holding the cell's pointer was excluded from every rooting category
   ("cells have their own rooting" — true only for env-RESIDENT cells,
   which read through the rooted env). A GC between cell creation and
   closure construction moved the cell; the closure captured the stale
   pointer; a LATER collection's scan hit it (coredump: a CID_CLOSURE env
   `s:3:8:2:ssrrrrrr` whose first ref slot pointed at an unforwarded
   `cell$s`). **Fixed**: cell binders go through the shouldSlot
   write-through slot like any ref binder (`lowSlotInit` builds the cell
   into the slot); the `let rec … and` closure-group cells are slotted the
   same way (their registers went stale across the SIBLING cell allocs and
   closure fills); the cell-assign path evaluates the VALUE before
   re-reading the cell pointer (store-order rule).

The **structural** fix (frontend inst-recording for desugar temps and
lambda params) was never needed — kept here as the option of record if a
new type-lost holder category ever surfaces.

## 4. RESOLVED: the non-gc regression (was: pre-existing, must bisect)

Bisected to `7c73223` (the 8-category rooting commit) and fixed in `cada6d8`:
three emission paths ran ungated by `gc` and emitted `$roots`/`$witnesses`
into non-gc `--linear` modules, which do not declare them (NRE in
`EmitBin.gg`): the `EMatch` ref-binder slot pushes (`patRefBinders`),
`genWitsOf` (generic-aggregate witness exprs), and `constWits`
(`stampedClassWits`, which Link populates for ALL linear builds via
`stampScalars`, not just gc). All non-gc gates green again (wasmlin,
lowir-typetest/exn/str), fixpoint-self + corpus byte-exact. Debug technique
that cracked it: make `EmitBin.gg` print the missing global's NAME.

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

1. ~~Bisect + fix the non-gc `wasmlin-gate` regression~~ (§4, done).
2. ~~Cover the remaining unresolved-value instances until the 16 MB
   self-host runs~~ (§3.6/§3.7, done — runs to completion).
3. Task #69: the stub divergence → byte-exact cmp. 65219 vs 77860; the
   compiled compiler stubs 105 member bodies ("unbound variable" /
   "capture not in scope") that .NET does not. Enumerate them from the
   wasm run by printing `ws.EmitWarnings` in the driver (§2), diff
   against the .NET-side list (`FPP_LINWARN=1` on gchost / the oracle
   build), then shrink the first divergent body with `FPP_PRELUDE_TRUNC`.
4. Byte-exact cmp at 16 MB growable = done. Target line:
   `DONE bytes=77860 hash=39471061` (the driver's djb2-&-0x3fffffff over
   `/tmp/oracle.wasm`; current self-host: `bytes=65219 hash=703075731`).
5. Then: port a curated tier of F#'s conformance tests via a differential
   harness (dotnet fsi oracle vs `fpp --gc`/`--linear`) as the hardening
   phase.

## 7. The 105-stub divergence: tuple hashing + tid interning (FIXED)

The self-hosted compiler stubbed 105 prelude enumerator members ("unbound
variable"/"capture not in scope") that .NET compiles clean. All were misses
in `(string, int)`-keyed dicts (VarId keys). Three independent bugs:

1. **`$hashv` predated the raw-int/tid world**: its odd-check treated raw
   ints as tagged (`hash 3 = 1`), and its CID dispatch compared `(tid<<1)|1`
   headers against CID constants — never matched, so every string hashed to
   the constant string-tid header and every heap object to its raw header.
   Rewritten on $cmpv's skeleton: raw scalars hash to themselves (agreeing
   with the witnessed fast path), known tids dispatch (string sampled-FNV,
   f64/i64 fold, array length), everything else walks payload words via the
   tid table's ref bitmask (`h = h*31 + (ref ? $hashv w : w)`). Only
   CONSISTENCY matters — dicts are insertion-ordered, hash values never
   reach output bytes.
2. **Equal tuples interned under DIFFERENT tids**: the witness-selected
   generic-aggregate path used its own `"sg:…:mask"` shape keys, so a
   `(string, int)` tuple built generically and one built concretely got two
   tids — and `$cmpv` orders differing headers as unequal. `tidForMask` now
   interns the RESOLVED shape under the concrete path's canonical
   `"s:cid:n:raw:pat"` key.
3. Repro kept: `/tmp/t5.fpp` (Dictionary), `/tmp/t7.fpp` (generic eq/hash).

## 8. §3 addenda: two more emitter rooting gaps (FIXED)

- **§3.8 Or-pattern binders**: `patRefBinders`/`patGenBinders` fell through
  `POr` to `[]` — `| TVar v, other | other, TVar v ->` left `other`
  unrooted across the arm's allocating `occurs` call (measured fault:
  prune-under-adjustLevels). Binders are identical in every alternative and
  ride registers, so collect from the first alternative.
- **§3.9 Curried-apply mid-chain reads**: every step of `f x y` allocates a
  partial closure; `rootActiveGen` reloads registers only after the WHOLE
  outer safepoint node, so the chain's later-arg register reads saw pre-GC
  addresses (measured fault: prune-under-compatible via forall2). `lowApply`
  now evaluates the closure and all args up front — slotting the closure,
  ref args, and witnessed generic args — and the chain reads through the
  GC-updated slots.

Diagnosis recipe that found all of these (fast, reusable): reproduce with
`-D coredump=`, `wasm-tools print --print-offsets` to name the faulting
instruction, breadcrumb the trapping function (store locals to scratch 224
before the fault), decode the coredump's data segments, walk the fpprt type
table (`types_ @4368`, stride 20) + `FPP_TID_DUMP=1` for tid names.
