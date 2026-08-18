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

## 18. Given-match by unification; float/char ranges; access modifiers

- **Given-match by unification: built, gated, then DISABLED** (the
  guarded code stays in Infer behind `elif false`, ready). The journey:
  equality-only matching let `x - One` default One's type to int behind
  a `Num<'a>` given, so float stamps unboxed an int One and trapped —
  matching by unification fixes that. Unrestricted, it also let a fully
  concrete given (`Ordered<string>`) capture an underdetermined wanted
  (`Ordered<?v>`) — 14 wrong string-vs-int bindings in the corpus — so
  it is gated to givens SHARING a variable with the wanted. With the
  gate it types correctly everywhere, but the changed emission shape
  surfaces a latent wasm-linear hazard (a ref TEMP across an allocating
  subexpression is un-rooted — named locals are Slotted, temporaries
  are not) and the 16 MB self-host traps in ToString→concat→str_cat.
  Re-enable together with temp rooting. History of the finding:
  `Num<'a>` entails `Sub<'a,'a> = 'a`; the wanted from `x - One` is
  `Sub<'a, ?v>`, and the equality-only match let ?v numeric-default to
  int behind the given's back — the float stamp then unboxed an int One
  and trapped in $tof. Rigid variables stay rigid in the matching trial,
  so a given never grounds the binding's own parameter. This also cured
  the pre-existing wasm-linear range traps (int64/float ranges).
- **Char ranges** (`[ 'a' .. 'c' ]`) work: char is ordinal and takes
  the inline raw-scalar builder, no instances needed. **Float ranges
  stay a compile error** (Integral demand kept): with given-match off,
  a float One wrongly defaults to int and the stamp traps — refusing
  the program beats trapping. Flip to Num+Ordered when given-match
  returns.
- **Access modifiers are enforced** ("make the compiler understand and
  respect these"):
  - `let private` / `type private` (cases included): resolvable inside
    the declaring module and its nested modules, an access error
    elsewhere in the file, and never exported across files.
  - `member private` (static and instance, properties included): visible
    from source positions inside the declaring type's own declaration
    spans (extensions add their spans) — judged by USE offset, so
    deferred retry-loop resolution judges the original site. Definition
    and FieldInfo both carry an Access field.
  - `internal`: assembly-wide today, recorded so the package boundary
    can exclude it later. `public` is the default, accepted everywhere.
  - New diagnostic: a dotted use whose PREFIX names a module but whose
    full path resolves to nothing is "module X does not export 'y'" —
    before, the use silently lowered to ZERO (this is also how a
    cross-file use of a private binding used to vanish).
    Two exemptions, learned the hard way: emission-owned names
    (doubleBits & co — the backend resolves them by NAME under the
    self-host, where bootstrap.fpp never declares them), and PRELUDE
    modules entirely (Array.empty, String.Format — lowering owns extras
    the prelude source never declares). User modules stay strict.
  - `type EmptySet<'T> private() = ...` marks the CONSTRUCTOR private,
    not the type — the type-level access scan is positional (before the
    name only); the adaptive port's three private-ctor singletons caught
    the conflation.
  - access.fpp ported (14th suite); negative tests in WorkspaceTests.
- A stub whose first error is a SYMBOLIC class marker ("$class:...#N")
  is an unstamped template, not a porting gap — the warning is now
  quiet on both backends (the trap on reaching it stays loud). Before
  the given-match fix these templates emitted a wrongly-defaulted int
  One instead of stubbing, which is why they never warned.
- KNOWN ISSUE (latent): the wasm-hosted compiler TRAPS in $str_cat while
  printing a WARN line (seen when the self-host briefly emitted two stub
  warnings; masked again now that they are quiet). The warn-printing
  path on wasm-linear needs a look before warnings become routine there.
- The list->array conversion now routes through a stamped prelude
  generic (`ArrayOps.OfList`) for POD elements — the hand-built IR
  stored anyref into POD arrays and failed wasm-GC VALIDATION
  (`[| a .. b |]` never worked on the wasm-GC backend; only the
  wasm-linear path was gated). Reference elements keep the inline walk.
- KNOWN ISSUE (pre-existing at 34d022a): NESTED array comprehensions
  (`[| for i in … -> [| … |] |]`) trap at runtime on the wasm-GC
  backend (the inline ref-element conversion). wasm-linear is correct
  and conformance-gated; the wasm-GC side needs its own gate.
- Known issue found while testing (pre-existing, unchanged): a
  member-only `type C = member ...` with no constructor accepts `C ()`
  and stubs; write `type C() = ...`.

## 19. The 16 MB self-host trap: multi-cycle stale edges in DEAD data

The givenMatch/float-range work was blocked by a heap-size-dependent trap
(§18). Root-caused and FIXED — the journey mattered as much as the fix:

- Debug tooling built along the way (all kept): a debug reactor recipe
  (`-O1 -g -DGC_DEBUG=1`, plus `fpprt_dbg_live` → semi.c `gc_dbg_live`,
  which rejects exactly the idle semispace half — `gc_heap_contains`
  answers the TRACER's question, not the mutator's, and a header-parity
  test misses multi-cycle staleness); `FPP_TIDDUMP=1` (tid → shape key),
  `FPP_GENCONS=1` (which functions build witness-selected conses), and
  `FPP_CONSCHECK=1` — runtime liveness checks emitted at every generic
  cons (head twice, tail once) and at the store funnels (EFieldSet,
  $cellset, Slotted assign).
- With ALL checks armed, the ENTIRE self-host compile passes clean and
  still traps later: the stale pointer never flows through a cons operand
  or a store. The tracer diagnostic showed the crash object is a
  `cons$ref` cell whose HEAD points outside both semispace halves with no
  forwarding — MULTI-cycle stale, in a heap that had GROWN (region
  growth REPLACES the mapping and leaks the old one, so there is nothing
  left to chase).
- The decisive experiment: null such edges instead of tracing through
  them — the compile then completes BYTE-EXACT at 16 MB with 55 nulled
  edges. Every one sits in data the program never reads again:
  GC-reachable rot in long-lived structures, semantically dead.
- THE FIX (vendored semi.c, production): extend the existing one-cycle
  stale-edge tolerance (the forwarding chase a prior session added) to
  the multi-cycle case — an edge outside both halves, unforwarded, not a
  large object, nulls out. Nothing legitimate lands there: static tables
  are not heap-traced and this embedding has no true extern objects.
  After the fix the self-host passes at EVERY heap size tried
  (16/20/24/32/48/64 MB), byte-exact against the oracle, with givenMatch
  and float ranges ACTIVE.
- The deeper cleanliness question — WHICH long-lived roots hold dead data
  long enough to rot (55 instances) — stays open as a quality issue, not
  a correctness one. FPP_CONSCHECK + the debug reactor are the tools when
  someone picks it up.

## 20. Ranges done right; two pre-existing gaps recorded

Porting the `ranges` suite (16th) against real F# flushed three more:

- **RangeOps.Seq now counts UP from lo**, as F# does. Down-counting from
  hi was wrong when hi - lo is not a whole number of steps
  (`[1.0 .. 2.5]` gave [1.5; 2.5] instead of [1.0; 2.0]) and `i - One`
  underflows an unsigned lo of zero into an infinite loop. One extra
  reversal per materialised range.
- **`for x in 1.0 .. 10.0` HUNG**: the for-in range fast path stepped the
  float's word as an i32. The inline count loop is now gated to ordinal
  elements (rangeInline); everything else materialises through
  RangeOps.Seq and cons-walks.
- KNOWN ISSUE (pre-existing): uint32/uint64 RANGES produce garbage — the
  RangeOps stamps at unsigned kinds mis-handle the boxed-vs-raw ABI.
- KNOWN ISSUE (pre-existing): packed float/int64 ARRAY equality traps on
  wasm-linear — $cmpv has no scalar-array branch, so the compound walk
  reads f64 payload words as refs (faults at the double's bit pattern).
  Int arrays ride the uniform representation and compare fine.
- Probe discipline, learned twice in one session: an env-var read at TOP
  LEVEL becomes a value INIT that BinDriver stubs with unreachable — the
  wasm-GC-hosted compiler then traps at _start; and an env read inside a
  function BinDriver EXECUTES under self-host stubs that whole function
  (the linear backend answers unresolved externs with null, BinDriver
  does not — that asymmetry is why the linear self-host tolerated the
  same lines). Probes go in function position, and never in BinDriver's
  own emit paths.
- `int u` on uint64 (`int#v`) was an unported linear conversion — the
  whole init containing it stubbed SILENTLY (stored 0, printed nothing).
  Wraps to the low 32 bits now, as .NET does.
- KNOWN ISSUE (pre-existing, investigated): UNSIGNED GENERICS on
  wasm-linear. `when Num<'a>` members at uint32 run the Canon template's
  class-instance ops with raw semantics on TAGGED operands (garbage);
  at uint64 the stamp exists but traps downstream. Note for the next
  session: these members stamp through the member-constraint machinery,
  NOT Link.classify — adding uint32 to classify's scalar list changed
  nothing. FPP_LINWARN=1 surfaces the silent stub inits.

## 21. Operator members, `lazy`, `:=` through fields; ops/lazy/ctree suites

Three more fsc suites ported (18 green): `ops` (members/ops — operator
members, overloading, the generic-vector dictionary pattern), `lazy`, and
`ctree` (explicit-field generic classes with several constructors). Porting
them surfaced and fixed a chain of real compiler gaps:

- **`static member (+)` is now the designed sugar** (DESIGN.md): it
  registers a free-standing instance of the operator's class whose body IS
  the member — `deriveOperators`, the same move `deriveOrdered` makes for
  CompareTo. Heterogeneous spellings register the head they wrote
  (`(x : C, y : float)` → `Add<C, float>`). The head/result types are
  CLONED with fresh declaration-level variables — holding the member's
  live inference vars broke selection later (pruning moved them, the
  substitution missed, the instantiation came out empty).
- **F# op members are tupled where class-syntax instance members curry** —
  `InstMember.MTupled` carries that to every call site (Lower's operator
  arm, Link's stamped-op `asCall`), which builds the tuple.
- **Custom operator members (`>>>>`) resolve now.** They are neither
  bindings nor class symbols; inference finds `(op)` on an operand's head
  type, types the use as that member call, and parks the owner in
  memberSites for lowering. Before, the use typed FRESH and lowered to a
  stubbed prim that recursed at runtime.
- **Generic heads keep their arguments in op suffixes**: `+@GV$<#39>`
  instead of `+@GV`, so stamping substitutes the element per copy and the
  stamped operator resolves the STAMPED member (Link falls back to the
  stripped constructor key exactly like the $class resolver; asCall
  stampRefs a layout-dependent member at the head's own arguments).
- **Overloaded ctor calls kept losing their instantiation**: the
  ctor-overload arm in Infer had its specialization demand DISABLED
  (`&& false`) and Lower's overloaded arm emitted a bare EVar. Enabled and
  EVarI'd — `new ctree<int>(42)` now stamps the ctor, so a Some payload
  stored by the shared generic body no longer disagrees with the concrete
  reader (ct2/ct7 were exactly this).
- **`lazy e` is `Lazy (fun () -> e)`**, rewritten POST-parse in Desugar
  (Workspace.ParseRaw applies it) — the parse stays lossless for the
  round-trip tests; a first in-parser attempt failed exactly that gate.
  Memoization, IsValueCreated, nesting all behave.
- **`x.field := v` silently VANISHED** — the general `<-`/`:=` arm treated
  the ref-cell store as a field assignment (or a $cellset of the field),
  so the write replaced the FIELD instead of going through the cell. `:=`
  now always stores into the cell the target evaluates to. This affected
  EVERY ref held in a record/class field.
- **`type R = { ... } with member ...`** (same-line or standalone `with`,
  optional `end`) now parses — the record-with-members spelling fsc tests
  use everywhere.
- KNOWN ISSUE (pre-existing): type EXTENSIONS on a GENERIC type
  miscompile — a named static member traps with runtime recursion, an
  operator member dies at "cannot specialize" (the ops suite declares the
  augmentation's member with the type instead, see its comment).
- KNOWN ISSUE (pre-existing): `member val P = init` never runs `init`
  (reads default 0/null); `with get, set` on it does not parse.
- KNOWN ISSUE (pre-existing): `%A` printing is a silent stub on wasm-GC —
  the whole statement's init vanishes (no output, exit 0).
- Debug lesson: a probe type named `box` collides with the boxing builtin
  — `new box<int>(42)` lowers to the IDENTITY on its argument and every
  "field read" then faults. Half this session's ghost bugs were that name.
- FIXED (was: adaptive C-backend legs red since f1e3680, found by
  re-running the long-dormant gate, bisected automatically): f1e3680's
  class-member stamping cloned members whose CANONICAL def the C backend
  replaces with runtime intrinsics keyed by def identity (CEmit st.Intrin)
  — the stamped WeakReference.TryGetTarget missed the intrinsic and
  emitted the prelude's STRONG source body, handing the fpprt weak
  WRAPPER out as the target; the first transact then dispatched
  InputChanged on it (`no vtable entry (tid 0 slot 742)`). Fix:
  classMemberDef skips WeakReference/ConditionalWeakTable — backend-owned
  members, never layout-dependent (the payload is a ref). Both adaptive
  legs PASSED 100 FAILED 0 again. Debug recipe that found it: gcc -O0
  repro (~5 min/cycle), gdb on the Commit frame, reading the outputs
  buffer element's header, then comparing the stamped
  `TryGetTarget_IAdaptiveObject` body against the canonical intrinsic.

## 22. Lazy own-member stamping: the depth-cap chain was speculative code

The `instantiation depth capped (StructTuple2$<StructTuple2$<...` warning
was POLYMORPHIC RECURSION, not a poisoned scheme: `IndexList<'T>.PairwiseV`
returns `IndexList<struct('T,'T)>`, and a stamped subclass eagerly stamped
its WHOLE member set — whose PairwiseV stamp demands the next ctor, whose
subclass stamps the set again, five dead levels deep until the cap cut the
name to `$ref`. Nothing ever called past level 0.

Fix: a stamped subclass eagerly stamps only the own members that DISPATCH
can reach — its interface impls (own chain), names the program actually
EIfaceCalls anywhere (one scan; abstract-through-class dispatch lowers to
EIfaceCall too), and the by-name protocols (CompareTo, the duck-typed seq
protocol, ToString/GetHashCode/Equals). Every other own member is only
ever called directly, and the call site stamps it itself — same mangled
name, deduplicated. `DMembers` names are NO signal: Lower registers every
class's member set there too (that false signal absorbed the first
version of this gate).

Effects: the cap warning is gone on the adaptive build; the mini repro's
generated C shrank 20.4 MB → 3.4 MB and the full adaptive suite.c
19 → 13.8 MB (the eager sets were mostly dead weight program-wide); the
full battery dropped ~18.5 → ~12 min wall on the smaller gcc inputs.
Battery 28/28 green, both fixpoints byte-exact, wasm-linear self-host
byte-exact (bytes=78531 hash=971705526).

Trap re-confirmed the hard way AGAIN: a `GetEnvironmentVariable` probe
inside capInst made stage-1 trap (BinDriver stubs it, the self-hosted
compiler executes capInst) and masqueraded as a wasm-GC regression of the
gate for one whole cycle. Probes NEVER go in code the fixpoint executes.

## 23. NEGATIVE conformance: programs F# rejects must be rejected

New gate: `tests/conformance/neg.sh` over `tests/conformance/neg/*.fpp` —
31 illegal programs in the common subset, modeled on the fsc
ComponentTests `E_*.fs` cases. Each file carries its expectations inline
(`//! <line> <substring>` against OUR diagnostics — fsc's wording cannot
be the oracle, per DIVERGENCES.md rule 1); `./neg.sh --oracle` separately
proves `dotnet fsi` rejects every case (`//? fsc-accepts` marks a chosen
divergence). Wired into run-gates.sh.

Building the suite found ELEVEN silent-acceptance holes — programs that
compiled cleanly and ran as garbage — all fixed:

- record literal with an UNKNOWN field (built a phantom record) and one
  MISSING a required field (the bare-name owner rule accepted `{ a = 1 }`
  for a two-field record; the field ran as null)
- `x <- 2` on an immutable let, and `r.a <- 2` on a non-`mutable` field
  (the write vanished or misrouted; mutability now rides the project-wide
  fields table under `$mut:`-prefix keys — a SUFFIX key read as a real
  field and broke the cback struct layouts, a per-file dict lost
  cross-file declarations)
- an or-pattern binding different names per alternative (`Some v | None
  -> v` read an unwritten local)
- a duplicate union case name (last silently won)
- `inherit` from a union/record (the "subclass" ran baseless)
- an interface implementation leaving a member out (empty vtable slot —
  this one immediately caught tests/tooling/genericenum.fpp omitting the
  Dispose that prelude IEnumerator declares)
- `while 1 do` (condition never tied to bool)
- `s.[true]` AND `a.[true]` (index types never tied to int)
- an unbound identifier (`nosuchthing + 1` printed 0). Reported through
  Resolve's Missing channel with the FreshIdents cross-check, so bare
  single-file inference stays quiet; the emission-owned print/fail
  families are exempt by name.
- unknown case in a pattern (`| C ->` matched everything) — a chosen
  DIVERGENCE: F# binds it with warning FS0049, F++'s uppercase-never-
  binds rule makes it an error (new DIVERGENCES.md entry).

Lesson from wiring it up: marker keys in the shared `fields` table must
be PREFIX-shaped (`$mut:R.f`) — every layout consumer scans by
`TypeName + "."` prefix, so a suffix marker (`R.f$mut`) surfaced as a
phantom field in zero-init records and aborted the C backend.

## 24. casts suite; abstract-class dispatch and type tests fixed on linear

New suite: `casts` (18 assertions) — up/downcasts, `:?` patterns, boxing,
abstract base classes, object expressions over classes AND interfaces,
subclass-aware class tests, over USER types (the fsc subtype suite itself
is BCL-bound). Writing it surfaced and fixed THREE linear-side bugs:

- **abstract-through-class dispatch trapped on wasm-linear** (`(sq :>
  Shape).Area()` — wasm-GC was fine): a missing vtable slot silently
  dispatched through SLOT 0. WasmLin now allocates class-keyed slots from
  DMembers (as CEmit does), answers them from the nearest own member in
  the base chain, and the casts suite pins the behaviour.
- **`:? AbstractBase` answered false for every subclass on linear**: an
  abstract class is both a DClass and a DInterface, and the interface
  TestIds loop OVERWROTE the class loop's subclass set with the (empty)
  impl-clause set. The sets now merge.
- **a ctor'd class whose members are ALL abstract lost its constructor**:
  Lower's isInterface test (`every member abstract`) claimed it, no ctor
  DLet was emitted, and every subclass's `inherit Shape()` stubbed to an
  unreachable that trapped at construction — on BOTH backends. A
  constructor now makes it a class regardless of member abstractness.

KNOWN ISSUE (recorded, both backends): a TYPE TEST on a boxed SCALAR
(`match box 1 with :? int`) answers false — F++ scalars share one boxed
representation, so the exact scalar type is not testable at runtime.
Distinguishing them needs typed boxes (a representation decision, not a
patch); the suite tests reference types only.

Also answered this session: dropping the wasm-GC backend would NOT lose
the conformance suites (they run on `--gc` = wasm-linear + reactor, fsi
as oracle) — but wasm-GC is the DEFAULT build, the browser/JS-interop
target, the second emitter of every differential gate, and the definition
of the fixpoint gates. Removing it is a migration, not a deletion.

## 25. Negative batch 3: the class/member surface (44 must-reject cases)

Thirteen more negative cases; EIGHT were silent-acceptance holes, fixed:

- instantiating an [<AbstractClass>] (the attribute was entirely unread)
  or an INTERFACE (`IThing()` compiled and trapped at first dispatch)
- `inherit` of an interface from a CLASS (interfaces inheriting
  interfaces stay legal)
- `override` with nothing to override (base chain + iface search,
  object-override names exempt)
- duplicate member signatures IN ONE DECLARATION BLOCK — scoped that
  narrowly on purpose: `type X with` extensions may re-spell an intrinsic
  member (F# prefers the intrinsic), abstract/default pairs coexist, and
  F++ overloads may differ by `when`-CONSTRAINTS alone, so the signature
  key includes the constraint set. This check found REAL duplicates the
  adaptive port was generating: rewriting OptimizedClosures.FSharpFunc
  parameters to plain functions collapsed each perf-adapter overload into
  an exact copy of the implementation it wrapped — port-adaptive.py now
  drops the degenerate self-delegating adapters.
- a record PATTERN naming an unknown field (the scrutinee's type names
  the record when the labels cannot)
- a STATIC member called through a value (`c.S()` — trapped at runtime;
  properties exempt, their value entry does not carry IsStatic), and an
  INSTANCE member called through the type (`C.M()`)

The remaining five (ctor arity, literal-pattern type, type-arg count,
loop-counter assignment, unknown type via usage) already errored through
existing checks. All 44 fsi-oracle-verified (1 divergence skip). One
observation parked with a repro: the ad-hoc mini adaptive driver
(cval→map→transact) recurses on the wasm-linear+reactor leg under
wasmtime while the emcc linear leg, the C legs and wasm-GC are all green.
PINNED SINCE: it is PRE-EXISTING — an old-compiler worktree with the old
port reproduces it identically; minimal repro = ported lib + `cval 1 |>
AVal.map ((*) 2) |> AVal.force` (blam0 self-recursion, no output). A
leg-specific codegen/runtime interaction, not a recent regression; no
gate covers this lib+leg pair today.

## 26. incremental suite; class-slot targets keep the uniform signature

New suite: `incremental` (15 assertions) — the members/incremental class
family: primary-ctor classes with computed let-fields, generic classes
with annotated fields, mutable listener lists (both `ref` and
`let mutable` spellings), the abstract Wire with its object-expression
factory, and mutable-record-field writes. Adaptations: IEvent dropped
(no event surface), WinForms modules dropped, `!listeners` in argument
position parenthesized (known parser gap).

It caught a fresh linear bug on first run: "indirect call type mismatch"
— the class-keyed dispatch targets added in §24 (abstract-through-class,
object-expression overrides) escaped the uniform-vtable-signature rule,
so a specialized-signature member landed in a slot whose call_indirect
expected the uniform type. WasmLin's vtImpls now includes every function
a class-keyed slot can resolve to (the same closure BinDriver's
ifaceImplKeys computes).

The wasm-linear+reactor adaptive recursion (§25) is confirmed
PRE-EXISTING via an old-compiler worktree; minimal repro recorded.

## 27. printf suite: uint64 arithmetic, int64 printing, and a self-host save

New suite: `printf` (49 assertions) from the fsc printf tests — %o/%x/%X
across 32 and 64 bits with two's-complement negatives, %d/%i/%u to the
Int64/UInt64 extremes, width/zero/left flags, %s %c %b %%, %f, partial
application. Porting it unearthed a STACK of wrongness on the
wasm-linear leg (the conformance backend):

- **`255UL % 16UL` was garbage**: every uint64 ('v'-kind) arithmetic,
  comparison, bitwise and shift prim fell through to the int32 path and
  operated on tagged word halves. LowIR grew DivUL/RemUL/LtUL/GtUL/
  LeUL/GeUL and the WasmLin arms accept 'v' with unsigned selections.
- **`%d` of an int64 printed the BOX POINTER** — always had, on linear;
  no suite ever printed one (only compared). Rendering now routes
  through prelude FormatOps (Int64Str/UInt64Str), ONE implementation for
  every backend; %x/%X/%o and width padding likewise (Radix/Radix64/
  Pad) — cback and linear previously had NO radix/pad helpers at all
  (silent stubs), wasm-GC had its own.
- Int64Str is SIGNED arithmetic throughout with the MinValue hardcase:
  the uint64-of-int64 reinterpret resolves by KIND at emission and
  misdetects inside the generic prelude context on wasm-GC (truncated
  through 32 bits) — recorded as a known issue.
- **The gchost byte-exact check caught a real self-host bug**: the first
  i64 literals in the prelude (FormatOps') made the SELF-HOSTED
  compiler's `i64.const`s come out as STRING POINTERS — BinDriver's
  int64-literal arm used `int64 digits`, and int64-of-STRING is unported
  on wasm-linear. Fixed with parseInt64In + explicit sign, the same
  lesson the adjacent comment already recorded for i32.
- KNOWN ISSUE: user-level `int64 "123"` on wasm-linear still yields the
  pointer (int64#t unimplemented — $atoi is 32-bit); same for uint64.

## §28 numbers + mutrec suites (2026-08-18)

Two more fsc ports: `numbers` (11 asserts — 2^n boundary tables for
int32/int64 both signs, naive pow recomputation via comprehensions, wrap
edges MinValue/MaxValue mul/div/rem) and `mutrec` (12 asserts — the
portable core of letrec-mutrec: inner rec groups closing over a captured
ref, partially-TLR odd/even, recursion through ref cells, polymorphic
inner letrec). Dropped from mutrec, documented: `module rec` (unsupported,
errors via the Missing hint) and cyclic VALUE recursion (`let rec x = {
f2 = x }` — FS0040-style delayed init not implemented).

Compiler fix the port forced: Lower's ListExpr statement-form
comprehension required EXACTLY ONE ForExpr/WhileExpr child, so
`[ for i in .. do yield e; yield a; yield b ]` (a loop plus trailing
yields) fell to "not lowerable: list comprehension". Any yield-bearing
non-arrow body is now the statement form: all exprish children lower in
sequence under the accumulator. The eager plain-element lowering was also
moved AFTER form detection — it used to lower every yield's inner
expression a first, discarded time (side-effect-table pollution risk).

Battery: 29/29 gates, conformance 23 suites / 1307 positive asserts,
44 neg, fixpoint self byte-exact, gchost DONE bytes=81368 hash=853970823.

## §29 longnames + comprehensions suites (2026-08-18)

Two more fsc ports. `longnames` (16 asserts): long-path access to values,
constructors, fields and members through nested modules; qualified pattern
matches; the bug-1218 shapes (union static member vs case on one head;
value-vs-type precedence) and bug-4379 ctor shadowing. All passed first
try. One NEG case added (shadowctor, 45 total): a later `type foo()`
shadows an earlier value `foo` ENTIRELY — F# rejects `foo 1` with FS0501,
F++ rejects via ctor-arity unification.

`comprehensions` (25 asserts): list/array comprehension bodies — nested
for, filters, if/else double-yield, match-with-yield, tuple binders, the
while form, stepped ranges. Compiler haul: the stepped range VALUE form
`[ a .. s .. b ]` had NO lowering anywhere — it fell through as a
one-element list holding a raw `..` prim (garbage on linear, `toi` cast
trap on wasm-GC). Prelude grew RangeOps.Step (direction = step's sign at
run time; zero step yields [] where F# raises); Lower materializes the
stepped shape in list and array literals — checked BEFORE the two-part
pattern, which also matches the nested prim — and the for-loop stepped
inline arm is now guarded to ordinal elements, with non-ordinal stepped
sources (float steps) cons-walking RangeOps.Step.

Suite-authoring traps: array `=` is reference equality (chosen
divergence) — compare via Array.toList; fsi refuses a continuation line
starting with `=` after a multi-line comprehension (FS0010) — bind first.

Battery: 29/29, conformance 25 suites / 1348 positive, 45 neg, fixpoint
self byte-exact, gchost byte-exact at the new prelude (bytes=82064
hash=451751650, oracle identical).

## §30 autoprops suite + three known issues fixed (2026-08-18)

Three open known issues closed, exercised by the 26th suite (`autoprops`,
20 asserts) and NEG case 46 (`noctor`).

* **`member val P = init [with get, set]`** now parses and works: the
  parser accepts accessor NAMES after an auto-property initializer, and a
  post-parse desugar (Desugar.desugarMemberVal, hooked in ParseRaw beside
  the lazy rewrite) expands the declaration into a `let mutable __mv_P =
  init` backing field plus a get/set accessor property — shapes that
  already carried the semantics. Init runs ONCE at construction, bare form
  is get-only. `static member val` get-only drops the `val` (re-evaluating
  a pure init per read); a static SETTER is left alone (needs static
  state).
* **`int64 "s"` / `uint64 "s"` on wasm-linear** parse instead of handing
  the string pointer out widened: WasmLin grew `$atol` ($atoi's i64 twin)
  and `int64#t`/`uint64#t` arms ahead of the widening catchalls. The
  second half of the bug was in INFER: `uint64` was absent from the
  conversion result-type table (a duplicate `int64` arm sat in its place),
  so `uint64 s` typed as a fresh variable and a later `int64 b`
  kind-detected "" and widened the box pointer.
* **`C()` on a member-only class** errors ("no constructors are available
  for the type 'C'", F#'s FS1133) instead of building a ghost object whose
  members read zero. The site is REMEMBERED during the walk and judged
  after it — a struct-block type's `new` members register only when the
  walk reaches them, so a use inside an earlier member body sees an empty
  candidate set transiently (AdaptiveToken does exactly this). Guards:
  abstract/iface (own diags), unions, records, aliases, arity variants.

Trap relearned the expensive way: a `dotnet build ... -v q | grep -c` that
prints 0 on a FAILED build leaves the old binary in place — the "still
failing" adaptive gate was a stale compiler, not the fix.

Battery: 29/29, conformance 26 suites / 1368 positive, 46 neg, fixpoint
self byte-exact, gchost byte-exact (bytes=82064 hash=451751650).

## §31 syntax suite + two parser conformance fixes (2026-08-18)

27th suite: `syntax` (58 asserts) — the portable core of fsc's syntax
test as self-checking asserts: bit operators across int/int64/uint64/byte
(17-hex-digit literals wrap mod 2^64 exactly as F#), Failure raise/catch,
for-to/downto/nested/while-over-ref loops, prefix-sum and letter-count
array samples, tuple plumbing, the List/Option samples, generic
comparison over tuples/lists/strings, records, unions, escape chars,
negative-sign precedence.

Two parser fixes it forced:

* **Prefix minus binds LOOSER than application**, as in F#: `-R 3` is
  `-(R 3)`. The prefix-position operand was parsePostfix, so `-idf 3`
  parsed as `(-idf) 3` and errored `no instance Neg<int -> int>`.
  Leading-position `-`/`+` now take a whole application; argument-position
  minus (`f -x`) keeps the tight postfix operand.
* **Only `[<` opens an attribute list** at declaration position: a bare
  `[` is a list-literal statement. `[ ... ] |> List.iter ...` at top
  level used to die as "unexpected token at top level".

Known gap noted: `max`/`min` (MinMax) have no tuple instances — F# allows
max over any comparable; the suite dropped that assert.

Battery: 29/29 on the settled tree, conformance 27 suites / 1426
positive, 46 neg, fixpoint self byte-exact, gchost byte-exact
(bytes=82064 hash=451751650).

## §32 clear-cut known issues fixed; boxtests suite (2026-08-18)

The "fix everything with a clear right or wrong" sweep. 28th suite:
`boxtests` (26 asserts); autoprops grew to 24.

* **Boxed-scalar `:?` / `:?>` work on every backend.** wasm-GC
  (BinDriver): int tests i31-or-$boxi, float tests $boxf, int64/uint64
  test i31-or-$boxl, both at the pattern-test and the checked-downcast
  sites. wasm-linear: an odd word IS a tagged int; float/int64/string
  test by class-id — and the scalar-box tids (str/f64/i64) are now
  MAPPED in $t2c (unmapped tids read cid 0 under the reactor, so every
  scalar test answered false). Shared representations stay divergences
  (DIVERGENCES.md): bool/char/byte ride the int; wasm-GC keeps small
  int64s in the i31.
* **`!x` in argument position parses** (`max !cell 3`): a gap-before,
  adjacent `!` is a deref argument, the same adjacency rule as `f -x`.
* **`int64 "s"` parses on the remaining backends too**: BinDriver's
  uint64-of-string arm (was "cannot convert"), and fpp_to_i64 in the C
  runtime grew the string arm fpp_to_int already had (returned 0).
* **`static member val P = init [with get, set]`**: the backing field
  hoists to MODULE level (state is per type), the member becomes a
  static accessor property; init runs once at module init. Get-only
  statics stopped re-evaluating per read.
* **Get accessors register `get_P`** like setters register `set_P`: the
  static-through-type check exempts properties via those entries, so a
  get-only static accessor property was flagged "instance member".

Verified fixed, notes retired: generic-class `'a[]` field Length=0
(tests/known-issues file removed), wasm-GC nested array comprehensions,
extensions on generic types (named static + operator members both work).

Still open by DESIGN (not clear-cut): typed boxes for bool/char/int64
sharing; MinMax tuple instances (componentwise vs lexicographic, user
call pending). Still open as its OWN ARC: `%A` structural formatting —
the right design is static-type-driven expansion in Lower (the hole's
Type threaded from Infer), not a runtime walker; both backends' showv
print "?" for structures today.

Battery: 29/29, conformance 28 suites / 1478 positive, 46 neg, fixpoint
self byte-exact, gchost byte-exact (bytes=82064 hash=451751650).

## §33 linear fixpoint arc, part 1 (2026-08-18)

Goal: THE fixpoint on the linear backend — the compiler compiled to
linear (reactor mode) re-emits itself byte-exactly. Harness and a large
bug-tail chunk shipped; the last blocker is an open GC-staleness hunt.

Shipped:
* **WASI file reads on wasm-linear**: path_open/fd_read/fd_close/
  fd_filestat_get imports, $readfile (reads into the fresh string's own
  data area, widens back-to-front — one alloc, nothing rooted across
  it), $fexists. The readTextRaw/existsRaw/canonicalizeRaw externs are
  REAL now (`wasmtime --dir srv::.`), which makes the self-hosted
  compiler able to load actual sources.
* **eprintf/eprintfn work under self-host**: Lower expands them through
  the printf machinery to `eprints`; WasmLin emits $eprints (the
  $prints body parameterized by fd); C runtime grew fpp_eprints;
  BinDriver evaluates-and-drops. stderr debugging inside stage-1 works.
* **fixpoint.fsx `linear` mode** (composes with `self`): stage-0 emits
  via the new Workspace.EmitProgramWasmReactor (gc<-true + LowIR — ONE
  method so driver and harness cannot disagree); corpus served as real
  files; wasm-merge with the fpprt reactor; compiledrive-lin.fpp.
* **The silently-stubbed emitter**: WasmLin/CEmit/parts of Workspace —
  14 functions including emitLinearImpl and emitLowE — were trap-stubs
  under self-host, killed by their own debug env probes (GetEnvironment-
  Variable → whole-function gap) and eprintfn. Env reads now answer
  null on linear; probes live. Also: `List.map string` in gcTidRef, the
  `Fpp.Prelude.doubleBits`/`Fpp.Core.Link.stampedClassWits` qualified
  paths (backend-owned/unresolvable under self-host — now bare + open).
* **Three GC rooting holes fixed** (the class: values in unscanned wasm
  locals/operand stack across allocating siblings; every semi-space
  collection in the window corrupts them): (1) refKindOfExprC classifies
  concrete non-scalar FIELD reads RKRef (was RKGen = never rooted);
  (2) lowRootedArgs roots ALL W-lane args (uniform words are tagged-or-
  pointer, always scan-safe — the isRef gate was the hole); (3)
  EIfaceCall roots the receiver and every argument across each other's
  evaluations (the old shape read a stale receiver register after
  allocating args, and args off the unscanned operand stack).
* **Hardening**: a lowered tree naming a register the function never
  allocated is now a loud ERROR with a tree dump (corrupt-lowering
  sanity walk in emitFuncLow); localIdx failures carry the local's name;
  FPP_TREE_DUMP=<fn> dumps a function's lowered tree.
* The deployed fpprt reactor (/tmp/bigreactor) was STALE — predated the
  gc-stale-edge fix (fpp runtime 46e037d); rebuilt and redeployed.
  TODO: the reactor build should be a repo make target, not a /tmp
  artifact.

OPEN (the blocker): stage-1 still corrupts one lowering deterministically
(fn $f2029100283, a conditional witness-slot push naming register 609 of
22). Deterministic ≠ not-GC: the corpus's allocation schedule is
deterministic, so stale windows repeat exactly. The debug loop, tree
dumps, and suspect list (lowApply infos slotWitness path, EMatch arm
slotting, freshTmp-through-stale-ctx) are in the fpp-linear-fixpoint
memory. Battery stays 29/29 and gchost byte-exact (bytes=82064
hash=451751650, 0 stubs — the stub fixes also cleaned the wasm-GC leg).

## §34 linear fixpoint arc, part 2 (2026-08-18)

* **lowCallR**: the `+t` operand bracket generalized — a runtime call
  roots every operand across the LATER operands' (possibly allocating)
  evaluations. Applied to `@`/$lappend and the string-method family
  (StartsWith/EndsWith/IndexOf/Contains/trims/Insert/Replace), which all
  had ref operands waiting un-rooted on the wasm value stack.
* **$printraw on linear**: each UTF-16 unit becomes ONE byte (the
  Latin-1 inverse), flushing when the 256KB window fills. printRaw used
  to route to $prints, whose UTF-8 encoding DOUBLED every byte >= 0x80 —
  the fixpoint's stage-1 module came out mojibake'd.

Linear fixpoint state after part 2: the self-hosted linear compiler
compiles the FULL fixcorpus and emits ~48KB of VALID wasm; stage-0 and
stage-1 agree byte-for-byte through the type/import sections; the gap is
~20 function bodies that stage-1 quiet-stubs because the corrupt-lowering
sanity check catches garbage register ids in their fresh trees (the
match-arm gen-binder slot machinery). The FPP_CONSCHECK + debug-reactor
run (fpprt_dbg_live must be in EXPORTED_FUNCTIONS) passes every checked
store funnel — the stale edge enters through an unchecked path; the
resume plan is in the fpp-linear-fixpoint memory.

Battery: 29/29, gchost byte-exact (bytes=82064 hash=451751650, 0 stubs).

## §35 linear fixpoint arc, part 3 (2026-08-18/19)

The corruption is SOLVED; the corpus fixpoint is 404 bytes from closing.

* **Read-side conscheck** (FPP_CONSCHECK=1): every Slotted/register/env
  variable read validates ref-looking values against fpprt_dbg_live
  (numeric site ids; the emit prints a CCHKSITE side table on stderr),
  plus a per-function shadow-$sp balance check. This pinned each hole in
  minutes where tree-diffing took hours.
* **Kind-aware operand rooting (lowRootedArgsK)** replaces both the old
  isRef gate AND part-2's root-everything: a REF operand roots
  unconditionally; a GENERIC operand with a witness roots CONDITIONALLY
  on its refMask; a GENERIC without a witness is on the canonical tagged
  form and roots unconditionally; RAW never roots. Root-everything was
  UNSOUND: W lanes DO carry raw evens in stamped code (dictSlotH's hash
  argument), and scanning them let the stale-edge tolerance NULL live
  ints. rootParams follows the same rule (gen-with-witness stays on
  ActiveGen).
* **The Dictionary INDEXER is miscompiled under the linear self-host**:
  `ctx.Regs.[key v]` returned garbage register ids at the EMatch
  arm-binder/gen-binder/ActiveGen sites while dictTryFind at the same
  keys answered correctly — every WasmLin-internal read now goes through
  `regOf` (dictTryFind + loud failure). Standalone repros (string and
  int keys, closures, fresh contexts) do NOT trigger it — the miscompile
  needs its original context and is STILL OPEN as its own bug; regOf is
  the workaround and the emitter is clean of the indexer.

Corpus fixpoint state: stage-1 emits 55150 vs stage-0's 55554 — ZERO
stubs, zero errors; 4 functions differ only in their witness-conditional
slot blocks (stage-1's patGenBinders sees CONCRETE schemes and an empty
ctx.Witness where .NET sees TVar-with-witness — a deterministic
stamp-vs-canonical classification divergence in the self-hosted front
half, the next session's target).

Battery: 29/29; gchost byte-exact (82064/451751650, 0 stubs).

## §36 THE LINEAR FIXPOINT IS GREEN (2026-08-19)

**`fixpoint.fsx linear self`: stage-1 reproduces stage-0 byte for byte
(11,093,143 bytes).** The compiler, compiled to wasm-linear (LowIR +
Whippet reactor), running under wasmtime, reads its own sources over
WASI and re-emits ITSELF byte-exactly. The corpus mode
(`fixpoint.fsx linear`) is equally exact (55,554 bytes). Wired into the
battery as `fixpoint-linself` — 30 gates now.

The last two defects:

* **patGenBinders' keep/witOf pair disagreed under self-host**: two
  textually-identical prune+lookup passes over the same scheme — the
  second (witOf) answered 0 where the first hit, pairing every generic
  match binder with witness register 0 (a 4-byte diff; runtime-correct
  only by accident when the witnesses agreed). Rewritten as ONE lookup
  (`pick`) deciding both keep and witness. The same session replaced
  every `.Value` in WasmLin with a matched `optGet` — Option.get_Value
  is the same stamped-generic member-access family as the Dictionary
  indexer, both still OPEN as a self-host miscompile to hunt (regOf and
  optGet are the workarounds; the emitter no longer uses either member).
* **bytesString at 11MB**: building the whole emitted module as one
  string overflowed the string machinery under self-host (OOB in
  StringBuilder/concat) — the driver now prints 64K slices.

Housekeeping: the fpprt reactor is a REPO artifact now
(tests/tooling/gc/fpprt_reactor.wasm, built from ~/projects/fpp/runtime
@46e037d by tests/tooling/gc/build-reactor.sh; FPPRT_REACTOR overrides);
the driver's debug catch/W-dump removed.

wasm-GC's remaining roles after this: default `fpp build`, the
browser/jsinterop target, and the fsi-oracle gates that run through it.
The linear backend now carries its own self-host proof — the interop
arc is what remains before the default flips and wasm-GC can be dropped
wholesale.

Battery: 30/30 (fixpoint-linself included), both wasm-GC fixpoints
byte-exact, gchost byte-exact, conformance 28 suites / 46 neg.
