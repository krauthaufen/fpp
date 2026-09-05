# Witness completeness → full moving GC

GOAL: every generic context knows ref-vs-raw for its type params (a WITNESS
per param, everywhere), so nothing is traced conservatively; then evacuation
comes back on and pinning is per-object (`fpprt_pin`), temporary — movement
resumes when nothing is pinned. Needed because long-running apps (CAD, hours)
fragment, and Immix-without-defrag (today's mode) never compacts.

## Why compaction is OFF today (the thing we are removing)

Int-stamping put RAW ints (untagged even words, bit-identical to pointers) in
some scanned slots. To stay sound, under mmc the uniform-word forms (FK_TAGGED
bodies, ref arrays, RANGE roots) are traced CONSERVATIVELY — validated, marked
in place, raw ints skipped, never rewritten. A conservatively-reached object
can't be moved, and Whippet's `ambiguous-edges` mode disables evacuation
GLOBALLY when ANY conservative tracing happens. So one unwitnessed site keeps
the whole heap non-moving. The fix is to make EVERY slot precise (witnessed),
remove the conservative mode, re-enable evacuation.

## The measurement that justifies the project

`FPP_WITSCAN=1 fpp build …` counts conservative-dependent sites (an object
body with an unwitnessed RKGen slot, or an unwitnessed generic cell), grouped
by category and function. It is the scoping + progress tool.

    baseline (before witness work)   851 obj sites (adaptive test HARNESS)
    after Phase 1 (leaf classes)     652
    after Phase 1b (base classes)    471
    + member-accessor/$cellget/etc   458   <- CURRENT (adaptive harness)

REAL-CODE surface is FAR lower: the battery (real HashMap/HashSet) is **30
obj + 7 cell sites**, and those are property-test GENERATORS (`.Draw`) and
cells, NOT the collections — the data structures are essentially fully
witnessed. The adaptive harness's 458 is dominated by ONE function (`go`, the
100-tests-inlined runner, ~277 sites) building `constant<int, #153699>`-style
objects where `#153699` is an UNRESOLVED/phantom stamping marker. Those are an
inference/monomorphization artifact of the harness, not representative.

Perf note: compaction-off costs NOTHING measurable on the benchmark suite
(all 9 within 1.5x of the compaction-ON baseline, warm). The justification is
long-running fragmentation, which the benchmarks do not exercise — so the
payoff is real for CAD-class workloads but will not show on `regress.sh`.

## Mechanism: witnesses as trailing object slots

A witnessed generic class carries one trailing witness pointer per type param,
stored AFTER all fields. A member recovers 'a's runtime GC nature by reading
`self`'s j-th witness. The ctor fills them from its hidden `FuncWitness`
params. All of this machinery pre-existed (`WitnessedClasses`, `witVal`,
`selfWits`, `ClassCtorWits`) but was never populated; the work is populating
it correctly and closing the interactions it exposes.

Witnesses are keyed by BOTH raw id and pruned representative (`FuncWitness :
(int*int) list`), because a scheme's Quantified var and the body's binder can
be different ids that unify (the `equals<'T>` case — 91373 vs 163931).

## Phases and status

- **Phase 1 — leaf generic classes** (no subclasses). DONE, committed, green.
  `WitnessedClasses[n]=k`, static offset `HDR+4*nf+4*j`, ctor appends in
  ERecord. 851→652. Battery/adaptive/conformance/self-host all green.
- **Phase 2 — member-accessor witness mapping** (`node.Key`/`.Value`). DONE,
  committed, green. `slotWitness` maps an accessor result var through the
  receiver's instantiation to a class arg already in `ctx.Witness`.
- **Phase 1b — base classes (inheritance)**. IN PROGRESS, RED.
  A base member reads self's witness where a DERIVED object holds a derived
  field, so a static offset cannot work — a runtime `cid → witness-offset`
  table (`WitOff`, root slot `WitOffSlot`) gives the per-type offset; the
  inherit ctor (`ERecordExt`) appends the derived's witnesses. 652→471.
  KNOWN BREAKS being fixed:
  1. **Runtime `selfPreamble` read** regressed even leaf classes in a bisect
     (leaf+runtime-table = battery 12) — the `WitOff` table read returns a
     wrong offset. Suspect the fill or the address arithmetic; instrument the
     runtime `wbReg` value.
  2. **Structural walkers include witness slots**. `$eqv`/`$cmpv`/`$hashv`
     walk the object by its tid SIZE, which now includes the trailing witness
     slots — so two equal witnessed objects can compare unequal (the
     `hashset delta round-trip falsified by (hashSet [], hashSet [])`
     regression). Fix: the CmpTbl `nwords` for a witnessed tid must be the
     FIELD count (exclude the k witness slots); alloc size and GC-scan stay
     nf+k (witnesses RKRaw, excluded from refoffs already).
  3. Inheritance param mapping assumes base params are a PREFIX of derived
     params in order (holds for the tree hierarchies; verify `classBaseInstOf`
     for reorders like `MapLeaf<'k,'v>:SetLeaf<'k>`).

## Remaining after Phase 1b (to reach FP_WITSCAN=0)

- **Phase 3 — object-expression / interface-impl members** (the adaptive
  `GetValue`/`State` readers — the reactive machinery). They must store the
  ENCLOSING witnesses like classes do. ~99 `noW` sites live here.
- Generic arrays (`'a[]` at a raw stamp — runtime tid select, like cons/cells).
- Closure-returning-generic results (`EApp(EField "add"/"mapping", …)`).
- The var-identity tail (`hasW:EVar` where the value's var is a let-bound
  generic, not a param/class var).
- **Phase 4 — shadow-stack precision** (push-site audit): RANGE roots must
  carry no raw ints, or the range roots stay conservative → global flag stays.

## RESULT: moving GC PROVEN for witnessed code (2026-09-05)

The flip switch is `FPPRT_MOVING=1` (runtime env, default off — mmc.c gates the
trace_one conservative branch and the ambiguous-edges init on it). With it on,
uniform-word bodies AND range roots are traced PRECISELY and evacuation runs.

Experiment (battery, 15 real HashMap/HashSet property tests, small heap to
force GC + evacuation): **7/15 pass under MOVING** — ofList/Map agreement,
add→tryFind, remove→absent, count, union, intersect, difference, each 200
randomised cases = **1400 cases with evacuation active, correct**. The
witnessed real collections move. The 8th traps.

The trap is `BADROOT ... val=0x0000000a` — a raw int (10) on the SHADOW STACK.
It is NOT a separate problem: it is the TRANSIENT push of an unwitnessed
aggregate's raw slot (lowObjR pushes ref slots across its alloc; an unresolved
RKGen slot holding a raw int gets pushed). So witnessing the object closes both
its body AND its shadow-stack push. `lowGenericCons` already gates its push on
the element witness — the model is right, it just needs every site witnessed.

"No conservative retention" REQUIRES this route (Route A). Route B (pinning +
conservative marking) inherently RETAINS: conservative marking must follow an
ambiguous edge to avoid freeing a live object reachable only through it. So the
only sound path to zero-retention moving is zero conservative sites.

## Remaining to reach FP_WITSCAN=0 (the real work-list, by mass)

Measured on the adaptive harness (real-code battery is only ~15 obj sites):
- **generic RECORDS** (Gen, ElementOperation payload, ...): a record with type
  params is a DRecord with NO DClass, so the population loop skips it, and its
  construction has no type-arg thread to fill witness slots. `Gen.Draw` (8
  battery sites) is here: `g.Draw rng : 'a` where g : Gen<'a> — the result is
  Gen's param 0, but Gen isn't witnessed. BLOCKER: the ERecord construction
  needs its concrete type args (buried in function-typed fields like
  `Draw : PropRng -> 'a`, so not recoverable from field VALUES) — thread them
  from inference, or witness records via ClassCtorWits where the enclosing fn
  is generic and add a concrete-witness path for `Gen.int`-style sites.
- **ValueOption / Option / ElementOperation unions** (~105 adaptive sites):
  ECtor already witnesses via genWitsOf — these are unresolved only where no
  witness reaches the site (the `go` harness).
- **the `go` harness phantom markers** (`$g…`, 171 sites): inlined generic
  tests left at `#153699`-style unresolved type vars — a monomorphization
  completeness gap (stamp the inlined test, or thread a witness through the
  phantom). This is the single biggest count but is TEST infrastructure; a
  real app has no equivalent.
- obj@ DONE (this session), cells DONE, member-accessors DONE.

## The flip: two routes, and the ordering problem (analysed 2026-09-05)

`nofl_space_should_evacuate` already respects a per-object `NOFL_METADATA_BYTE_
PINNED` bit — so evacuating some objects while pinning others is POSSIBLE in
the collector. Two routes to turn moving back on:

- **Route A — FP_WITSCAN=0 everywhere, then remove the global flag.** Clean.
  Blocked by: (a) the harness phantom-var sites (`#153699` — need the
  monomorphizer to concretise or drop the unused param); (b) obj-expr /
  interface-impl members (no tyParams — must capture ENCLOSING witnesses as
  fields); (c) genuinely-unconstrained type vars, where defaulting the slot to
  "ref" is UNSOUND if it could ever hold a raw int. (c) may be irreducible.
- **Route B — per-object pinning (partial moving), keep the conservative net.**
  Pin FK_TAGGED objects + everything reached via a conservative edge; evacuate
  the precise (FK_STRUCT) rest. THE ORDERING PROBLEM: a precise edge can
  evacuate an object BEFORE a conservative FK_TAGGED-body edge reaches it, and
  the conservative slot (which can't be updated) then dangles. `mark_conservative_
  ref` only marks, does not pin. Single-pass tracing can't guarantee
  "pin-before-evacuate" for heap edges — which is exactly why Whippet's
  ambiguous-edges mode is GLOBAL. Fixing it needs a conservative-first pass:
  enumerate FK_TAGGED objects (a remembered set at alloc, or a heap walk at GC
  start), trace them conservatively (pinning referents) in the pinned-roots
  phase, THEN the evacuating precise trace. That is real vendored-Whippet work.

Recommendation: Route A for real programs is close (the collections are done);
the harness artifacts and obj-expr are the remaining compiler work. Route B is
the robust fallback if the phantom-var/unconstrained cases prove irreducible,
but it is a careful GC-internals change, not a quick flip.

## The flip (Phase 5)

When `FPP_WITSCAN`=0 across adaptive + self-host + shader + fpp.base AND no raw
`$spush`: remove `FPPRT_UNIFORM_CONSERVATIVE` (the trace_one conservative
branch, the pinned-roots range routing, `nofl_space_set_heap_has_ambiguous_edges`
at gc_init). Evacuation resumes. Verify `gc_pin_object` sets the nofl PINNED
bit and `nofl_space_should_evacuate` skips pinned objects; check EArrayPin/
Unpin clears it so movement RESUMES for unpinned objects. New gate: pin,
collect, unpin, collect, assert the object MOVED.

## Debug tooling (all committed, env-gated)

- `FPP_WITSCAN=1` — surface count by category|fn; `FPP_WITDET=1` adds the
  type var vs available witnesses per unresolved slot.
- `FPP_WCLS=1` — which classes get witnessed (name, k, nf).
- `FPP_NOWITCLS=1` — disable witness population (bisect).
- `FPP_FNWIT=<dbgName>` — dump a function's witnessVars/paramVars/selfWits.
- Battery (`/tmp/battery.fpp`, 15 property tests) is the sharpest regression
  detector here — it structurally compares HashMap/HashSet, which is exactly
  what the witness slots perturb.
