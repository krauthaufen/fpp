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

## MOVING-GC WORKS FOR ALL COLLECTION TYPES + SAFE ROBUST AT ALL SCALES (2026-09-05, done)

The witnessed-node construction is now correct end to end. Under FPPRT_MOVING,
ALL HashMap/HashSet type combos (int→int, string→int, int→string,
string→string) and HashSet EVACUATE correctly — verified at small heaps that
force compaction, with correct values after eviction. The five fixes:

1. `selfWits` reads the receiver from the first PARAM (`ps[0]`), not `sch.Body`
   (abstract-override methods carry the abstract signature, no receiver).
2. `ERecordExt` computes per-slot witnesses from its update exprs (inherited
   classes lower here, and had none).
3. `copiedKind` marks a concrete scalar field RKRaw unconditionally (a scalar
   is never a pointer; the old `intStamped` gate was never set).
4. `WitOff` uses the FULL inherited field count (chainFields), fixing the
   off-by-one for no-own-field derived classes (HashEmpty) whose base `count`
   made selfWits read the 2nd param's witness one slot early.
5. UNKNOWN-witness sentinel (refMask 2): a witness the compiler can't resolve
   forces the CONSERVATIVE tagged tid instead of a wrong `ref` default; and —
   the keystone — under the conservative collector FK_STRUCT bodies are traced
   CONSERVATIVELY too (gc_object_conservative_body), so a mis-resolved witness
   is VALIDATED, not chased. This fixed a PRE-EXISTING large-map SAFE trap
   (>~30k elems trapped before; now correct at 100k+), and kept moving precise.

STATE: SAFE (default) is robust at every scale; FPPRT_MOVING gives precise,
compacting GC with zero conservative tracing for fully-witnessed code (real
collections). Real per-object pinning works under both. What still blocks
FLIPPING moving to the DEFAULT: the test harnesses (Gen property generators,
the adaptive `go` phantom-var constructions) still have unresolved-witness
sites that become tagged-conservative — safe in SAFE mode, but chased under
moving (the residual). Real app code without those generators moves cleanly.

## MOVING-GC NODE CONSTRUCTION FIXED — 3 of 4 type combos move (2026-09-05, superseded)

Root-caused why witnessed generic CLASSES (the HashMap/HashSet node machinery)
were traced conservatively, and fixed three layers so their constructions are
PRECISE under evacuation:

1. **`selfWits` read the receiver from `sch.Body`** — but an ABSTRACT-OVERRIDE
   method (`HashInner.AddWith`) carries the abstract signature `int -> 'k -> 'v
   -> …` with NO receiver, so `recv` was `int` and every node it built fell to
   the tagged fallback. Fixed: read the receiver from the first PARAM's type
   (`ps[0]`), gated to methods with no FuncWitness (the vtable impls).
2. **`ERecordExt` passed `genWits = []`** — a witnessed class' ctor `inherit`s
   its base, so it lowers through ERecordExt, which never resolved its generic
   slots. Fixed: compute per-slot witnesses from the update exprs.
3. **`copiedKind` gated concrete scalars on the never-set `intStamped`** — a
   copied `int` base field (`count`) stayed RKGen, dragging the WHOLE object to
   the tagged fallback (scanning even the raw `hash`). Fixed: a concrete scalar
   field is never a pointer → RKRaw unconditionally.

RESULT under FPPRT_MOVING + forced GC (3000-5000 elems, aggressive collection):
- **int→string, string→string, hashset<int>, generic Pair<int,int>: MOVE
  correctly** (verified, correct values after eviction).
- int→int, string→int (raw-scalar VALUE): still trap.

REMAINING BUG (precisely localized): the VALUE (2nd type param) witness of a
HashMap gets a REF default while the KEY (1st) resolves — so a raw-scalar VALUE
is scanned and chased. The asymmetry is real and confirmed: `key=int` works
(int→string moves), `value=int` fails (int→int, string→int). `HashMap.empty` is
a generic VALUE (`let empty : HashNode<'k,'v> = hmEmpty ()`) referenced with NO
instantiation in Core (`m = (empty)`), so no witnesses flow to it; HashSet's
`empty : HashNode<'k,int>` has a CONCRETE value type and hashset MOVES. The fix
is in the value-witness propagation for the generic `empty` value / the 2nd
type param — a generic-VALUE witnessing gap, not the class construction (which
is now precise). All safe-mode gates green, self-host byte-exact.

## REAL per-object pinning SHIPPED (2026-09-05)

`Array.pin`/`Array.unpin` are real temporary pinning under mmc: `fpprt_pin` sets
the nofl PINNED bit (`should_evacuate` skips it), `fpprt_unpin` clears it so the
object moves again at the next collection. `pin-gate.sh` proves it under
FPPRT_MOVING: a pinned array keeps its address across a compacting GC while
everything else evacuates, then MOVES after unpin — data intact throughout.
"Stop moving while pinned, resume when unpinned" — done. Inert (no-op) in the
default conservative mode, where nothing moves anyway.

## The surface count OVERCOUNTS the moving blockers

`FP_WITSCAN obj` counts every RKGen slot with no witness — but a bare-`'p`
record field gets a REF witness (`ofName "'p"`), which is SAFE and MOVABLE: a
tagged int in a ref slot is odd, so the tracer skips it, and the object stays
precise/evacuable. Witnessing all records to "fix" these BROKE safe-mode
correctness (battery 15→7) because it changed the layout of every record across
construction paths (literal/copy-update/zero-init/subclass) that don't append
the slots — REVERTED. The real blockers are only the sites that hold RAW
stamped ints; the empirical ground truth is the actual FPPRT_MOVING traps, not
the count.

## ROOT CAUSE of the real-code moving bug: canonical-vtable ↔ stamped raw/tagged boundary (2026-09-05)

Narrowed empirically. Under FPPRT_MOVING, at a small heap (forcing evacuation):
- direct `HashMap.add` of 5000 int values: WORKS.
- `HashMap.fold (+)` sum: WORKS (reads values fine).
- `HashMap.filter (fun k v -> k%2=0)` (rebuilds ~2500): WORKS.
- `HashMap.filter (fun _ _ -> true)` (rebuilds 5001): TRAPS.
- `HashMap.map (fun k v -> v)` (rebuilds 5001): TRAPS.
- `BADROOT val=0x3988` — a raw int VALUE on the shadow stack.

So it is NOT map-vs-filter and NOT the `'w` output var — it is the REBUILD
path (`fold (fun acc k v -> add k v acc) (hmEmpty()) n`) once it does enough
allocation to evacuate. The value is read through the CANONICAL vtable
`FoldWith` (all-anyref → uniform/tagged), threaded through a stamped fold
lambda, and re-added through stamped `add_…$int$int`, which dispatches to
CANONICAL `AddWith` (uniform) and stores the value in a uniform leaf slot. A
raw int ends up in that uniform slot and the evacuator chases it.

The boundary: generic-class VTABLE methods (`AddWith`, `FoldWith`) keep the
canonical all-anyref (uniform/tagged) signature and are NEVER stamped
(CLAUDE.md "A generic class that implements an interface is monomorphized"),
while `add`/`map`/`filter` module functions and their lambdas ARE stamped
(raw int ABI). A value crossing canonical→stamped needs untag, stamped→
canonical needs tag; one of those conversions is missing on the rebuild path,
so a raw int reaches a uniform (scanned, movable) slot. Under the conservative
default it is harmless (validated + skipped); under evacuation it is chased.

THE FIX is on that ABI boundary — ensure a scalar entering a canonical
(uniform) vtable slot is tagged, and one leaving it is untagged — not in the
witness machinery. This is the real blocker for moving-by-default on rebuild-
heavy real code (map/filter/collect over persistent collections). Real pinning
and non-rebuild real code already move correctly.

## Earlier lead (superseded by the boundary finding above)

`BADROOT val=0xa` — a raw int key pushed to the shadow stack from inside
`filter$int$int`'s fold lambda calling `add k v acc` (HashMap.filter, prelude
5027). HashMap's DIRECT add works under moving (tests 1-7 green); the failure is
a LIFTED fold-lambda inside a stamped clone losing the stamped-int witness, so
`add`'s node construction is unwitnessed and pushes the raw int. Fix is in the
stamped-clone/lambda-lift/witness interaction (does a lambda lifted out of
`filter$int$int` get int constWits / stampedClassWits?) — systematic, not
per-site: it would close every stamped-fn-calls-generic-helper-via-lifted-lambda
site at once. THIS is the highest-leverage next step for real-code moving.

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

# The residue: every site that still answers `obj`, and what each needs

Written 2026-09-07, against the 1 MB FSharp.Data.Adaptive port. Reproduce with:

    python3 tests/port-adaptive.py ~/projects/FSharp.Data.Adaptive/src/FSharp.Data.Adaptive lib.fpp
    cat lib.fpp tests/adaptive-suite/Tests.fpp > adaptive.fpp
    FPP_WITSCAN=1  fpp build -o adaptive.wasm adaptive.fpp     # the two totals
    FPP_WITSTRICT=1 fpp build -o adaptive.wasm adaptive.fpp    # one line per site
    FPP_WITSTRICT=1 FPP_FUNC_DUMP=1 ...                        # join to map $fNNN -> source name

`-o` must come BEFORE the input or the CLI prints usage.

    WITUNKNOWN emitted = 0 (uniform fallbacks = 210 of 12839 witness arguments)
    WITTYPES 630 witnesses, 627 carry a type id, 3 do not

## THE INVARIANT: the program is grounded, so `obj` is never a fact

Top level is monomorphic and nothing introduces a type variable, so by
induction every type argument at every call is determined — statically at the
site, or by a witness the caller was handed, which is itself ground one frame
up, all the way to `_start`. **A uniform fallback therefore always marks
information the compiler dropped, never a property of the program.** Do not
"resolve" one by assuming; find where the name was lost.

## THE CHANNEL THAT MADE THIS FIXABLE

`EVarI.inst` meant two things at once — *what types this call passes* and
*please build me a specialized copy* — so every attempt to give a call its type
arguments changed which stamps exist, and something downstream broke. A leading
`Ir.witnessOnly` (`"$witonly"`) marker separates them: Link strips it, keeps the
names, classifies the call Canon, and no later pass sees the marker. Supplying
names is now safe. **Use it for anything added below.**

## The sites

`FPP_WITSTRICT` tags each fallback `kind=<what the enclosing is> why=<what failed>`.

| count | kind | why | what it is |
|---|---|---|---|
| 111 | stamp | call-unnamed | a call inside a stamped clone that carries no instantiation |
| 38 | has-params | call-unnamed | same, from a function that does take witness params |
| 17 | vtable-impl | call-nochannel | the enclosing IS generic in it; the vtable slot has k=0 |
| 14 | lambda | call-unnamed | same, from a lifted lambda |
| 10 | stamp | slot-unnamed | slot-witness pad positions |
| 8 | generic-value | call-nochannel | a generic value has no witness channel at all |
| 4 | vtable-impl | slot-freevar | slot witness whose name the enclosing cannot bind |
| 4+4 | monomorphic, lambda | stamparg | `stampWitness` with no stamp arguments |

By callee, the `call-unnamed` bulk is: **`empty` 101, `monoid` 30**, then
`checkTag` 12, `trace` 6, `shallowEquals` 5, `min` 5, `max` 3, `shallowHash` 1.

### 163 `call-unnamed` — inference records no instantiation

`empty` and `monoid` dominate, and their shape is:

    static member Empty = empty          // adaptive.fpp 10013 / 10125 / 10419
    static member Instance = monoid      //              13722 / 13736 / 13750

A static member whose body is a bare reference to a generic binding **of the
same type**, used before it generalizes. `instantiateFor` freshens nothing
there, so no `instRaw` is recorded; 18 such template sites, each cloned ~12
times, produce the 163.

**What is needed:** inference must record the instantiation at these uses. The
identity (`sc.Quantified` as `#id`) is NOT it — parked and measured, it gives
exactly zero reduction, which proves these uses do not reach the
forward-reference arm the parking hooks. Find which arm types
`static member Empty = empty` and why it records nothing. `FPP_QUAL` shows the
qualified arm recording 359 times for `empty` alone, so it is not that one.

### 25 `call-nochannel` — the ABI has no slot

The enclosing definition IS generic in the variable and the backend owes it a
parameter it has not got.

* **17 vtable-impl.** Slots where `SlotWitN` came out 0 — the impls disagreed on
  their method-level count, or the receiver was not a shape `selfWits` reads.
  `FPP_SLOTWIT=1` prints each slot's k and its impls. Extending the slot ABI to
  cover them is the fix; the machinery is already there.
* **8 generic-value.** A generic value is initialised once and serves every
  instantiation. Link already thunks the EXPANSIVE ones (`let v = e` becomes
  `let v () = e`) so they can take `FuncWitness`; these are the non-expansive
  ones, which are not thunked because doing so re-evaluates a lazy or recursive
  value per use and hung the `patterns` suite.

### 22 pads and stamp arguments

`slot-unnamed` (10) are pad positions the impl never reads — filling them with a
named `obj` is provably safe (tried; it works, and is currently not landed only
because it was bundled with a change that was not). `stamparg` (8) is
`stampWitness` reached with no `curStampArgs`, i.e. the enclosing is not a stamp.

### 3 witnesses with no type id

`witnessPtrRM` (the unnamed constructor) at the builtin-conversion, operator and
tid-scan sites. Naming them was TRIED AND REVERTED: those paths intern type
names from a LATE lowering phase, past where the type-NAME table is sized from
`TypeIds`, so the id lands out of range and `typeName<string>` answers empty.
Fix the table first — size it from `TypeIdNext` and bounds-check the read — then
the names are free.

## What was tried and must not be retried without new information

* **Naming the residue `obj` in Lower** (at a use whose instantiation was never
  recorded). Takes 210 -> 61 and is WRONG: it overwrites the sites where the
  backend's variable-id fallback was already resolving correctly. `uint32`
  becomes `obj`, its compare kind goes from unsigned to the structural walker,
  4000000000 orders as negative and a map lookup raises KeyNotFound
  (`suites/unsigned.fpp` traps). Isolated to ONE site — the plain-identifier arm;
  with that arm excluded everything is green and the count is 214, i.e. WORSE
  than leaving it alone. The whole gain lives in the unsound site.
* **Naming it by the callee's own variable (`#id`) instead** — same suite, same
  trap. Neither keeping it symbolic through Link (rather than collapsing on
  `ownerQuantifies`, which is narrower than the backend's real scope) nor
  guarding the positional match by length rescues it.
* **Parking forward references** and recording the definition's quantified
  variables once it generalizes: zero reduction, +7000 witness arguments.
* **An `ExpectTy` channel** (the binder's type threaded to the call, consumed
  once, matched against the callee's result): measured exactly zero.
* **`resolved-vars=0 / free-vars=1308`** as evidence that the arguments are
  unconstrained: a TAUTOLOGY. It pruned the definition's scheme's `Quantified`,
  and a scheme's quantified variables are unbound by construction in every
  program.

## Diagnostics

`FPP_WITSCAN` (totals), `FPP_WITSTRICT` (per site, with `kind` and `why`),
`FPP_SLOTWIT` (each vtable slot's k and impls), `FPP_FNWIT=$fNNN`
(witnessVars/paramVars/selfWits for one function), `FPP_FUNC_DUMP` (map `$fNNN`
to a source name — join it with WITSTRICT), `FPP_CORE_DUMP`/`FPP_CORE_FN`,
`FPP_KEYCHECK` (Core key collisions), `FPP_VTDBG` (every vtable row, with the
impl's hidden-param count against the slot's).

**A diagnostic must never call `err`.** `err` STUBS the offending function, so
the module then fails somewhere else entirely — a consistency check added that
way cost hours, with the trap deep inside `$eqv` and nothing pointing at the
check. Warn with `eprintfn`.
