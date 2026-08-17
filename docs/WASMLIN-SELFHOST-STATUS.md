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

## 9. The last divergence, fully traced (2 stubs, `$class:Num:One:#1524`)

The chain of custody, each link measured (probe recipes below):

1. The stubs are `RangeOps.Seq`'s template body + its inner lambda. Inside
   it, `i - One` pools `Sub<'a, 'one>` + `Num<'one>` ('one = tvar 1524,
   IDENTICAL id both sides — inference is deterministic).
2. .NET: both wanteds survive to Infer's NUMERIC DEFAULTING pass → 'one
   defaults to int → `One` resolves to the int instance → oracle emits
   `b725_2333_One` and the call. Wasm-side: at the defaulting checkpoint
   the pool no longer holds them — resolveClassUse sees `#1524` unresolved
   → marker → Link can't substitute (subst empty) → EUnknown → stub.
3. WHY the pool differs: the `Sub` constraint's first arg chain is
   `v1519 -> v1525@0` on .NET but `v1519 -> Var{Id=0,Level=1}` on wasm —
   a Var record READ THROUGH A STALE POINTER (the memory was reused after
   a semi-space flip, so the collector's edge-integrity check cannot see
   it). The declLevel filter then classifies differently and the
   defaulting never fires.
4. The stale Var pointer is written into the link chain by one of the SIX
   still-uncovered unresolved lambda args (FPP_WDROP=1 on the gchost build
   lists them): `$blam1367 $e512 (eta):512`, `$blam1572 f2
   Infer.fs:305084` (line 5103), `$blam3990 item Plugins.fs:58122`,
   `$blam4692/4695/4696 sch WasmLin.fs:2846/2864/2867` (the `keep`
   lambdas in patRefBinders/patGenBinders/patCondBinders — note the
   emitter ones cannot corrupt INFERENCE; the eta one is the live
   suspect). ETADROP silent + WDROP firing means: the param type WAS
   concrete when `wrap` built the eta lambda, and the emitted copy's
   scheme prunes to an unlinked TVar — `fresh` does NOT rename tvars, so
   the loss is in monomorphization's Canon/stamp scheme rebuild (the
   documented fpp-lowir-witness-canon hazard: stamped copies get fresh
   unlinked scheme vars). Fix there: make the stamped ELam param schemes
   keep (or re-substitute) the resolved Body, WasmLin-gated like
   stampScalars if oracle bytes move.
5. Fix directions, in order: (a) cover the eta arg — find why its
   post-`fresh` scheme prunes to TVar at emitLambdaLow when it did not at
   wrap time (the `fresh` renaming creates NEW unlinked vars — thread the
   pre-fresh resolved Body through); (b) the frontend inst-recording for
   lambda params (§3's structural option); (c) after the crash-free root
   cause is fixed, the remaining byte diff is the +37 globals/+37 data
   segments (emitted-vs-oracle objdump) and the synthetic-offset drift
   (blit_int 500000023 vs 500000020) — both expected to collapse once
   the stub pair resolves like the oracle.

Probe recipes (all were reverted; re-add as needed): ONEUSE in
Infer.resolveClassUse (print constraint head raw+pruned for name="One");
DFLT before the defaulting `while` (constraints mentioning the tvar, with
levels); GEN1524 at generalizeBinding's moved-filter printing the arg LINK
CHAINS (`v1519@1>v0@1` was the smoking gun); LINK1524 in Types.unifySeen's
TVar-other arm; SEL in Classes.select. printfn only — eprintfn STUBS under
self-host. The driver hex-dumps its emit (`HX` lines) for wasm-tools
objdump/name-section diffing against /tmp/oracle.wasm.

## 10. §9 SUPERSEDED — the real root, measured to an 8-line repro

§9's stale-Var theory was WRONG in mechanism (right in observable). The
full measured chain, each step forced by an experiment:

1. The `Id=0` Var is not GC staleness: it reproduces IDENTICALLY at 16/24/
   48 MB growable AND 900 MB fixed (no collection at all). A `prune`
   watchdog (fire on `v.Id = 0` — ids start at 1, so 0 is impossible)
   fires first at prelude decl 209 = `type IEnumerator<'a>`, right after
   fresh var 1173 (= the decl's 'a), .NET-side never.
2. `tyParams` (the decl's param vec) provably holds the REAL tv1173
   immediately after the fill (probe read it back), and provably holds an
   all-zero "Var" by the first member's end: **a wild store zeroes the vec
   slot** during `inferMember` of `MoveNext`. Canary bracketing (a global
   `canaryCheck` at unifyAt/Fresh/setScheme/recordDef) pins the clobber
   INSIDE the `setScheme` argument at prelude offset 26010 — i.e. during
   `freeVars defTy |> List.distinctBy …` + the quantifier Level-writes.
3. Minimal repros (user prelude, `run-gc.sh`, no compiler involved):
   - `/tmp/t12.fpp`: `List.ofSeq (ResizeArray<Ty> :> seq<Ty>)` returns
     **len=0** with Count=1 — silently empty.
   - `/tmp/t17.fpp` (8 lines): the same `ofSeq` result piped through
     `List.distinctBy` → **wasm trap: indirect call type mismatch**.
   The enumerator-protocol lowering for a monomorphized ResizeArray
   subclass under wasm-linear `--gc` produces a corrupt/empty list, and
   walking it makes wild indirect calls — wild stores from the same class
   are what zero the neighboring vec slot in the compiler.
4. Also fixed en route (committed): the bare-`compare` eta now routes
   through `wrap` when its peeled operand scheme is unresolved, so an
   EVarI head's instantiation types the operands ((eta):$eN WDROP entry).
   Byte-exact.
5. KNOWN PRE-EXISTING (measured, distinct): `List.sortWith compare` on
   INTS returns wrong order (`[3;1;2]` → `1,3,2`) under `--gc` while
   strings/tuples sort right — /tmp/t9.fpp; present on committed HEAD.

NEXT (the fix): debug the enumerator/`ofSeq` lowering with /tmp/t17.fpp —
it is 8 lines, crashes loudly, needs no self-host build. When it and t12
pass, rebuild the self-host: the Num defaulting should match (.NET), the
2 stubs and the ~4K byte surplus should collapse toward
`DONE bytes=77860 hash=39471061`. Probe recipes for re-instrumenting the
compiler: §9 + task #69 metadata (printfn only; `grep -c` exits 1 on zero
matches and silently kills `&&` chains — bitten twice).

## 11. ZERO STUBS — both root causes fixed (this session)

Self-host now: `DONE bytes=82356 hash=2195680, NWARN 0`, exit 0 at 16 MB.
Function sets IDENTICAL to the oracle (695/695). Two fixes:

1. **Prelude iface impls are now DCE roots** (WasmLin reachability seed):
   they are reached only through the vtable, so excluding them (an old
   "later concern" guard) dropped the stamped `ResizeArray.GetEnumerator`,
   left its vtable row 0, and every `List.ofSeq (r :> seq)` dispatched
   through index 0 — empty list at best, WILD indirect call at worst.
   Repros t12/t17/t18 all pass now. Found via FPP_VTDBG=1 (kept): prints
   each vtable row decision; the smoking line was
   `VT ResizeArray$int cid=91 slot=7 … MISS-func GetEnumerator_…`.
2. **The `(let qs = … in (for v in qs do v.Level <- 0); { … })`
   ARGUMENT-POSITION shape miscompiles under the wasm-linear self-host** —
   the loop's field write scribbled a NEIGHBORING heap object (IEnumerator's
   tyParams slot read back as an all-zero Var, which flipped Num defaulting
   and produced the last 2 stubs). Not reproducible small (t14/t15 pass);
   the three sites in Infer (member/get-accessor/property setScheme) are
   HOISTED into named lets, which compiles correctly — the same class of
   shape workaround as tests/known-issues/let-rec-and-group-self-host.fpp.
   The backend bug is still latent for this shape; a future repro should
   start from the original one-liner in a member-scheme-sized context.

REMAINING for byte-exactness (the last item): 82356 vs 77860 — the
compiled compiler keeps 37 literal top-level lets as mutable globals +
data segments (135/47 vs the oracle's 98/10) where .NET's Optimize folds
them. Diff `wasm-tools print` globals of /tmp/selfemit2.wasm vs
/tmp/oracle.wasm to name the 37, then trace the compiled Optimize's
literal-fold decision for one of them. Everything else matches.

## 12. LENGTH-EXACT: 77860 == 77860, 881 bytes of type-intern ordering left

Two more root causes fixed (this session, after §11):

1. **bootstrap `bytesString` was `unbox (box bs)`** — a byte[]→string
   representation pun, valid on wasm-GC (both packed i8) but WRONG on
   wasm-linear (strings are 16-bit units): the punned "string" read past
   its object, equal byte arrays keyed the literal-intern Dict differently,
   and 37 duplicate string globals/data segments were emitted. Now a real
   per-byte build (only the emitter's interning calls it).
2. **`int#t` (int-of-STRING) lowered to the IDENTITY in WasmLin** — the
   self-hosted BinDriver's `int (l.Substring 5)` env-slot parse emitted
   string POINTERS as slot indices (145 diverging bodies). New `$atoi`
   runtime (signed decimal over the 16-bit-unit layout), `int#t` routed
   through it; `int#`/`int#i` stay identity.

Self-host now: `DONE bytes=77860, NWARN 0` — LENGTH-IDENTICAL to the
oracle, 695/695 functions, 98/98 globals, 10/10 data segs, identical
section boundaries except code/type content. REMAINING: 881 differing
bytes in 322 ranges, ALL downstream of ONE reorder: the self-host interns
closure-arity type `$v3` at index 33 where the oracle interns `$v2`
(same SET of types, same per-function type assignments, first-USE
functions identical — b725_30159_Equals(#115) for $v2 before
b725_226739_set_Item(#212) for $v3). So something on the wasm side
interns $v3 BEFORE function #115's declFn — a pre-decl-walk intern site
whose ORDER diverges (suspects: lambda discovery through the
`refMapNew shallowLamHash` map, an emission-order dict, or a
call_indirect-use intern in a scratch pass). Probe: instrument `tyFunc`
(print name + caller tag on first intern of $v2/$v3) on both sides and
diff the two traces. That one flip should zero the cmp:
target `DONE bytes=77860 hash=39471061`.

## 13. ★ BYTE-EXACT ★ — the goal of this document is achieved

    self-host (16 MB growable, real collections): DONE bytes=77860 hash=39471061
    oracle (.NET):                                DONE bytes=77860 hash=39471061
    cmp /tmp/selfemit5.wasm /tmp/oracle_new.wasm  → CLEAN

The last 881 bytes were ONE ordering flip with a beautiful cause: the
emitter's own `vArities |> List.sort` mis-sorted INTS when the compiler ran
as wasm. `List.sort` = `sortWith compare`; a bare `compare` eta's operands
are untyped (Lower records `TCon "?"` — the known frontier), so the body
falls to the generic `$cmpv` — whose int discrimination was still the
TAGGED-era model: both-odd compared `>>1`-shifted values and any odd/even
mix was declared int-vs-pointer. Under raw full-width ints, `compare 3 2`
answered -1, and every unwitnessed int sort — including vArities — came
out wrong (v1,v3,v5,v2), reordering the type section and renumbering 881
bytes downstream.

Fix (in `$cmpv`, ordering-safe for BOTH worlds):
- both-odd compares the WORDS unshifted — for tagged pairs
  `sign((2x+1)-(2y+1)) = sign(x-y)`, so FK_TAGGED walks order identically;
  for raw ints it is simply correct.
- an odd/even mix first asks whether the even side LOOKS like a managed
  object (in-memory, odd header, tid inside the shape table — the $hashv
  discrimination): a real pointer keeps the int<pointer order, a raw even
  int gets the direct signed compare.
- the bare-compare eta also routes through `wrap` now (typed operands
  whenever the head carries an instantiation).

This also fixes the user-visible `List.sort [3;1;2] = [1;3;2]` bug (§12's
"known pre-existing"; /tmp/t23.fpp now prints 123 on all three forms).

Gate trap for posterity: a `printfn` probe in EmitBin/BinDriver pollutes
STDOUT, which carries the fixpoint compiledrive protocol — fixpoint-self
then "DIFFERS at byte 0". Probe with stderr-free care or not at all there.

Status: wasm-linear `--gc` self-host is BYTE-EXACT vs the .NET oracle at
the default heap with real collections. §6 items 1–4 all done. Next phase
(§6 item 5): the F# conformance differential harness.

## 14. Conformance phase — the differential harness is live

`tests/conformance/` (see its README): curated ports of dotnet/fsharp's
`tests/fsharp/core` suites, gated as `dotnet fsi` (real F#) vs
`fpp build --gc` + wasmtime, stdout byte-diffed, test COUNT part of the
contract (a stubbed init shows as a count mismatch). First tier — smoke,
letrec, apporder, int32 — all green, and the ports drove NINE language
fixes in one sitting:

- `!` deref and `:=` on plain ref cells (never wired outside byref params;
  `!x` lowered to the CELL POINTER). Parser still needs parens for `!x` in
  argument position (`g (!x)`).
- `let rec … and` VALUE members now evaluate in dependency order (stable
  topo sort in Lower over value-member references; acyclic groups match
  F#'s initialization graph, true cycles remain unsupported).
- record literals evaluate effectful fields in WRITTEN order (typed temps
  in Lower; backends store by slot order unaffected).
- `absl` (int64) and `absf` (f64, new AbsF LowIR op) implemented.
- uint32 ops honour unsignedness: `/w` `%w` `>>>w` and `<w >w <=w >=w`
  route to the i32 *_u forms (new DivUW/RemUW/GtUW/LeUW LowIR ops).
- conversions: `byte#f/l`, `int64#f/l`, `uint32#f/l/-`, `uint64#f/l/-`,
  `int#w` (identity), and `u~~~` complement (i32 + i64 forms).

Known next chunks: byte/sbyte(/int16/uint16) arithmetic WRAP needs kind
letters through Lower + both backends (dropped tests marked in int32.fpp);
cyclic value recursion (delayed refs) is a feature decision. Suite ports
to continue: patterns, map, seq (subset), comprehensions (subset), innerpoly,
subtype (subset), syntax, longnames.

## 15. Patterns, records and all — the pattern surface is complete

The `patterns` suite port drove a full-stack pattern upgrade, all diffed
against real F# and green (5/5 conformance suites):

- **Record patterns end-to-end** (new): `RecordPat` parse node
  (`{ F1 = p; F2 = q }` in any pattern position), Infer typing (owner
  resolved from the written labels — a pattern may name a SUBSET of the
  fields — sub-patterns typed at field types), and a Lower desugar with NO
  Core/backend changes: the record binds whole to a fresh binder;
  refutable field sub-patterns fold into the clause GUARD (mismatch falls
  to the next clause), all binding fields wrap the guard and body as
  nested field-read matches. Works in match clauses (literals, guards
  reading record binders, fallthrough), local and TOP-LEVEL destructures,
  and nests.
- **Top-level destructure lets** (new): `let a, b = …`, `let [v] = …`,
  `let (Some v) = …`, `let (This a | That a) = …`, and binder-free
  asserts (`let (1, 2, 3) = …`) — bind the RHS once, one global per
  binder re-matching it; zero binders keep just the match (trap =
  MatchFailureException analogue).
- Bare list/cons patterns in ANY let now destructure (they bound the
  whole list before); `isDestructure` synced between Lower and Infer.
- Or-alternation in let parens no longer flattens to a PTuple.
- `null` in pattern position is a keyword, not a literal — it lowered to
  PWild and the null arm matched EVERYTHING (bug438 tests).
- Remaining parser gaps: NONE — see §16.

Self-host still byte-exact (77930 == 77930 with the regenerated oracle).

## 16. Full let-pattern parity and let-polymorphism (innerpoly)

"i want full parity here. even on senseless things like let 1 = 1."

- **Every top-level let-pattern spelling** now works: `let () = ()`,
  `let 1 = 1`, `let (1) = (1)`, unparenthesised `let 1, 2, 3 = …`,
  `let (None) = None`, `let _ = e` at module level. The parser always
  accepted them — `isDestructure` (both copies) had to learn that empty
  parens are the unit pattern, a literal asserts, and a parenthesised
  ident that RESOLVES to a union case matches rather than binds. An empty
  flat-extraction (`let () = …`) now keeps the paren pattern itself.
- **Assert-lets actually assert**: `let 2 = 1` must trap
  (MatchFailureException), and it silently passed — Link's dead-code
  effect analysis judged a refutable match pure, so the unread assert
  global was eliminated. A match with no unguarded irrefutable arm now
  counts as an effect. (`tests/tooling/gc` parity matrix: ok/trap in all
  eight directions.)
- **Local `let … in` generalizes before its continuation** (innerpoly
  suite): both inferLet arms typed the continuation INSIDE the binding's
  level, so `let f x y = () in f 1 "a"; f 1 1` pinned f to its first
  use — inner lets effectively never generalized. The continuation now
  types after setScheme. Destructure binders also generalize
  (`let (R2 (a, b)) = R2 ([], [[]])` leaves a and b polymorphic), under
  the value restriction: a computed RHS stays monomorphic, constructor
  applications (`Some 1`, `R2 (…)`) and literals/tuples/records of them
  generalize.

- **`for i = lo to hi do` / `downto`** (map suite): the parser produced
  the three-expression ForExpr but Infer routed the first bound into the
  enumerator protocol and Lower had no arm for it — both now recognise
  the `to`/`downto` keyword and desugar to the counted while loop.

Suites now: smoke, letrec, apporder, int32, patterns, lift, nested,
innerpoly, map, tlr — all diffed byte-for-byte against dotnet fsi.

## 17. Array comprehensions, array ranges, string for-in (forexpression, array)

Three more wrong-CODE bugs the differential suites flushed out — all
compiled cleanly and produced wrong values:

- **`[| for … |]` array comprehensions**: Infer unified the ForExpr's
  unit type with the element (every array comprehension froze to
  `array<unit>`), and Lower's `EArray` compiled the loop as ONE
  unit-valued element. Infer now mirrors ListExpr's addItems; Lower
  builds the LIST with the existing comprehension machinery (same node
  retagged) and converts through `listToArrayInline` — count, seed
  `Array.create` with the head, fill by cons walk; plain Core constructs
  only, so every backend lowers it.
- **`[| a .. b |]` array ranges**: same shape — the range spliced in a
  list but stored its CONS CELL as the single array element. Both sides
  now treat it as a splice and convert.
- **`for c in s` over a string (wasm-linear)**: the loop's receiver is an
  anon-typed temp, so WasmLin's ShStr shape test missed it and the read
  used the 4-byte ref-array stride — two UTF-16 units packed per "char"
  (0x00620061 from "ab"). The "$str" KIND now selects the load16_u read.
- The conformance runner gives ported originals a 128 MB fpprt heap: the
  .NET-scale allocations (forexpression holds ~500k cons cells live) are
  a runtime knob, not a language limit; the 16 MB default is a self-host
  tuning choice.
- Prelude additions for parity: `Array.get`/`Array.set` (they were
  silently stubbed), `Array.mapi2` raises on length mismatch as F# does.

Suites after this batch: + forexpression, recordres, array — 13 total.
