# Working in this repo

F++ is a compiler that compiles itself. That single fact sets almost every
rule below: a change that looks fine and passes the unit tests can still be
wrong, because the compiler has to be able to build *its own source* and get
the same bytes twice.

## The gates

Run all three before claiming anything works. They take about twelve minutes
together, and they have each caught things review did not.

```bash
dotnet build -c Release                      # ~30 s
dotnet run  -c Release --project tests/Fpp.Tests      # ~4 min, 692 tests
dotnet fsi  tests/bootstrap/fixpoint.fsx              # ~2 min, corpus
dotnet fsi  tests/bootstrap/fixpoint.fsx self         # ~7 min, THE gate
./tests/run-gates.sh --full                           # ~6 min, all 30, parallel
```

There is ONE backend: wasm-linear over the fpprt/Whippet reactor (the C
backend shares its middle end). The wasm-GC backend — `BinDriver.fs`, the
`--wasmgc` flag, and the source maps that only it could emit — was deleted
once every gate ran on the linear one. `fixpoint.fsx` still accepts the
`linear` argument and ignores it.

`fixpoint.fsx self` is the real one: the compiler compiles its own sources,
and stage-1's output must equal stage-0's **byte for byte**. It has caught
bugs the 578 tests missed — a `List.init` that counted down, an equality that
compared tree shape instead of contents. If you change the backend and only
the unit tests pass, you have not tested your change.

**A `let rec ... and` group inside `lower` miscompiled under SELF-HOST**
while the .NET build and every unit test passed. It looked for a long time
like the group's SHAPE — its size, its position among the surrounding
`let`s — and it was not. The cause was a FORWARD reference: the first
binding of a group calling a later one got a throwaway type variable, so
`(payload k).IsSome` written above `and payload ... : int option` never
learned its receiver was an option. The member stayed unresolved, Lower
emitted a bare field, and the backend answered `unreachable` — silent under
every diagnostic, `--strict` included. Fixed in Infer (`forwardVars`), and
`tests/conformance/suites/letrecand.fpp` covers the shapes.

The lesson that outlives it: a program that compiles clean and traps is an
inference gap reaching emission, not a backend bug. Dump the Core
(`FPP_CORE_DUMP=1`) and look for an access that did not lower — a `.M` still
sitting in the tree is a member the type never resolved.

Three details that will bite:

* **The prelude is an embedded resource.** Editing `stdlib/prelude.fpp` does
  nothing until you rebuild. A "green" run against a stale prelude is the
  oldest trap here — and a FAILED build leaves the old binary in place, so
  `dotnet run --no-build` afterwards happily runs the previous prelude. Read
  the build's error count, do not just pipe it to `grep -c`.
* **F# builds SIGSEGV (exit 139) under the sandbox.** Run with sandboxing
  disabled.
* **The dogfooding gate infers every `*.fs` in the repo with an empty
  prelude** and demands zero diagnostics. So compiler source has to be
  F++-inferable with NOTHING resolved — no prelude, no union cases. That is
  harsh on purpose: it is how a false positive in inference gets caught. It
  found the pattern-binder bug below.

## An application types its argument ONCE

The member path takes a `dotDemand` before typing the head, and that needs the
argument's type. It used to type the argument again in the argument loop, so
every member application did the work twice. A computation expression nests
once per `yield` and each level's argument IS the whole remaining tail, so it
doubled per level: eight yields took 8 s, and the adaptive port's own CE test
module never finished inferring. The demand's result is kept and reused —
eight yields now take 34 ms, thirty-two take 180 ms.

Do not "fix" this by taking the demand only for overloaded members. That was
tried: it scales the same and breaks the OUT-PARAMETER view, which is built
from the demand too (`real.TryGetTarget()` stops typing). The duplication was
the bug, not the demand.

## Measure, do not reason

Almost every performance intuition recorded in this repo's history was wrong,
including several in a row. The vertex benchmark went from 3615 ms to 149 ms
against C's ~62 ms, and the causes were never where they looked:

* "the field read is slow" — reads were ~5 ns; the *fill* loop was being
  counted as read time
* "it is the boxing" — the peephole already cancelled it
* "it is `ref.cast`" — measured at ~2 ns in isolation
* the thing that actually cost 3 seconds was a GC struct allocated per
  element *while a 12 MB array was live*, which neither ingredient shows on
  its own (allocating against a small array: 289 ms; writing without
  allocating: 210 ms; both: 3246 ms)

What worked, every time, was replicating the loop in hand-written wasm
(`wasm-tools parse`) and bisecting there. If a hand-written replica of the
same instructions runs 12x faster, the instructions are not the problem.

**Always print the program's result next to the timing.** A module that fails
to compile exits in milliseconds and looks like a spectacular win. That
mistake was made three times in one session, once reported as a 27x speedup
that was really a validation error with stderr piped to `/dev/null`.

Benchmarks that compare against C live in `tests/tooling/perf/`;
`tests/tooling/abi/` checks struct layout against emscripten.

**Every twin manages memory, and there is a Rust column.** The C twins for
`avl` and `trees` used to be bump ARENAS — one never freed, the other
dropped a whole tree by resetting a pointer — and against that the collector
looked 2.9x slow while measuring something no real program can do. They
malloc/free now, with refcounts for `avl` because the tree is persistent and
each insert shares most of its nodes with the version before it.

Rust builds to the same `wasm32-wasip1` under the same engine, with bounds
checks ON, which makes it the useful third point: C says what UNCHECKED
manual memory costs, Rust what CHECKED manual memory costs, F++ what a
collector costs on top. Read as of this writing:

    allocation   avl    F++ 1827  Rust 1796   — within 2%
                 trees  F++ 900   Rust 1137   — F++ ahead by 26%
    bounds       sort   F++ 1501  Rust 1472   — within 2%, and Rust cannot
                                                elide the partition scans
                                                either
    streaming    read/vertices/shapes         — F++ ~1.25x Rust
    float        nbody  F++ 389   Rust 305    — 1.28x, the widest gap left

So the collector is not the problem it looked like, and the bounds checks
cost what Rust's cost. What is left is array streaming and float-heavy code.

A Go twin was tried as "a mature GC" and dropped: `GOOS=wasip1` works and
answers correctly, but Go's wasm port runs ~10x its native speed (trees
8902ms against 1409), so the column measured the port. For the record its
NATIVE numbers against the old arena C were avl 2.51x and trees 4.45x, both
worse than F++ manages inside a sandbox.

**Measure WARM.** wasmtime caches module compilation on disk: the first run
of a fresh binary pays the whole Cranelift compile and reads 3-6x slower
than every run after it. A 433 ms "regression" on the read benchmark was a
cold cache; warm, the same binary beat C. Best-of-three, never first-of-one.

The 2026-08 pass found three real wastes, each visible only in a profile
(`perf record -k 1` + `--profile jitdump` + `perf inject -j`):
`Array.zeroCreate` of a POD struct spent a quarter of the benchmark seeding
zero fields into an `array.new_default` that was already zero (the seeding
is for CLASS-shaped elements, which need instances in the slots); every
statement answered with a boxed unit that its context immediately dropped
(`pushUnit`/`dropU` cancel the pair positionally, like the box/unbox
peephole); and a store into a hoisted-base POD array still called the
`$hwset` runtime helper whenever ANYTHING in the program pinned that
element kind — float formatting does — so the pin test is now inlined on
the hoisted storage, mirroring the read path. After all three: vertices
149 ms vs C 62, add 65 vs 67, read 88 vs 103 (both now BEAT C), shapes 686
vs 248. What remains on vertices/shapes is per-access bounds checks and no
SIMD — wasm-GC array.get has no unchecked or vector form, so that gap
belongs to the engine and the spec, not to emitted-code waste.

## Optimisations, and the switch that turns them off

`St.Opt` is false for debug builds (`mapUrl <> ""`), because hoisted bases
and elided branches have nothing in the source for a debugger to point at.
Anything that changes the shape of emitted code belongs behind it.

Currently: POD array bases are hoisted out of loops; a literal-valued
top-level `let` is emitted as its literal; the pinned/unpinned test is
dropped for types the program never pins; a record literal stored into a POD
array is written field-by-field instead of via a materialised struct; and
`let v = arr.[i]` splits the element into unboxed locals. The last two are
the same fix from opposite sides — never materialise a GC struct for a POD
element.

Innermost counted loops are unrolled twice: `while i < bound` whose body
advances `i` by exactly one, where `bound` cannot move and the body is small
(<= 60 nodes) and contains no other loop. The guard is the condition with
`i + 1` in place of `i`, so two iterations run only when two are left and the
remainder loop catches the last — no trip count, no arithmetic that could
overflow where the original would not, and no reassociation.

INNERMOST matters: unrolling a loop that contains another copies the inner
one too, and copies multiply as 3^depth. A two-deep loop turned three element
reads into twenty-seven before that condition went in. It buys 7% on a tight
loop (191 ms -> 177 ms) and nothing on a loop whose body is already big
enough to fall outside the size cap, for +3.2% module size.

### One-instruction wrappers cost three times over

A class member that IS a machine instruction — `sqrt`, `abs`, `truncate` on
a float — has no body in its instance, so Link generates one
(`fun x -> sqrtf x`). Calling that wrapper costs the call, a 16-byte GC BOX
for the result (the uniform ABI has no other way to return a float), and —
because a call is a SAFEPOINT — the loop-invariant hoist for the entire
enclosing loop, so every array base around it goes back to being re-read
from its root slot per access. nbody called `sqrt` 30 million times and paid
all three: it was the worst F++/C ratio in the suite at 3.0x, and inlining
the wrappers at their call sites took it to 1.4x (836 ms to 388).

The wrapper is still emitted — `List.map sqrt xs` needs a function — it is
just not what a direct call reaches (`inlinePrimWrappers`, WasmLin).

The lesson generalises past this one case: a call in a hot loop is never
just a call here, because it also switches hoisting off for everything
around it. When a benchmark is slow for no visible reason, look for what is
a CALL that should not be.

### Strength reduction: written, measured, worth NOTHING

Induction-variable strength reduction for POD element offsets — one multiply
before the loop per stride, an add where the counter is bumped — was built and
verified to fire: `i32.mul` in the vertex loop went from nine to one. Measured
against the same binaries, best of three:

    b1r20   116 ms without it, 120 with
    whole   175 ms without it, 181 with
    vertex  175 ms without it, 172 with

Nothing, and slower on two of the three. It also hung the compiler on one
program in a way that survived disabling the registration, so it is not
shipped — but do not resurrect it expecting speed. It has none to give here.

That is the lesson, and it cost a detour to learn: nine independent multiplies
per iteration are free, because the CPU issues them alongside everything else.
Counting instructions predicted ~19 cycles of savings and delivered zero.
Instruction count is not the gap to C — do not reason from it again.

Two were tried, measured, and **reverted** for not paying: inlining `$toi`
everywhere, and caching `i * stride` across an element's fields (the engine
already does that one). Do not re-add them without a number.

### Bounds checks: emitted, then proven away

Every element access carries one — a single UNSIGNED compare against the
length word, which rejects a negative index in the same test — and it
raises rather than traps, so a program can catch it. What keeps that from
costing anything is the proof pass (`provenWalk`, WasmLin), which runs over
the Core body BEFORE lowering and marks the accesses it can show are in
range. Six sources of proof, and they compose:

* a counted loop's own guard — `for i in 0 .. a.Length - 1`, `for v in a`,
  and the hand-written `while i < n` where `n` is the length `a` was
  CREATED with (module-level `Array.zeroCreate n`, literal or binding);
* a DERIVED index inside such a loop: `a.[i - k]` appeals to the same fact
  as `a.[i]` when the counter starts at k or above, which is the sliding-
  window idiom. The other direction does NOT hold — `a.[i + k]` needs an
  upper bound tighter than the loop's, so it stays checked;
* a check that already ran on the same (array, index) pair earlier in the
  same straight-line region;
* a PRECONDITION on a parameter, established by the function's CALLERS —
  see below;
* a FLATTENED 2D index — `m.[i * cols + j]` over `Array.zeroCreate (rows *
  cols)`, in range when i is under ROWS and j under COLS. Neither bound is
  the array's own length, so the length is kept as a PRODUCT of its factors
  and the index checked against them. Worth 2x on matmul: 218 ms to 103,
  which is C's 100;
* a guard the PROGRAM wrote. `&&` short-circuits, so the right operand runs
  only where the left holds: `while i < n && a.[i] < p do ...` proves its
  own access, and does not then pay for a check as well;
* nothing crosses a branch join or a lambda boundary, and a loop's guard is
  read with only what survives the body's own writes. That last one matters:
  walking the guard with the richer pre-loop state "proved"
  `while a.[i] < p do i <- i + 1`, which is exactly the access nothing can
  prove — i's upper bound is gone the moment it is incremented.

### Preconditions: what the CALLERS establish

`a.[lo + (hi - lo) / 2]` inside a recursive partition cannot be proven from
the function's own body: `lo` and `hi` are whatever the callers passed. The
fixpoint assumes every (parameter, array) pair is in range, then drops the
ones a call site fails to support, and repeats. The assumption is discharged
by induction on the execution trace — a call is supported by its caller's
facts, which held when the caller's activation began.

For quicksort that closes: `qsort 0 (n - 1)` is the base (n is a literal, so
the array is known non-empty), `qsort lo j` has j <= hi because j only FALLS
from hi, and `qsort i hi` has i >= lo because i only RISES from lo. Which is
why the domain tracks the two halves separately — a counter that only
decrements keeps its upper bound while losing its lower one, and collapsing
them into one "in range" fact loses exactly the half that survives.

Facts key on the PARAMETER, not its position: the bodies the fixpoint walks
are pre-transform, the ones emission lowers are not, and node identity does
not survive lifting and stamping. A callee named but not applied (passed as
a value) loses every precondition, since nothing constrains what reaches it.

Three shadowed match arms cost hours here, all the same mistake: `x < y`
must apply BOTH the "x inherits y's bounds" reading and the "y is some
array's length" one; `n - 1` must try both "offset from an in-range index"
and "last index of a non-empty array". Written as alternatives, the first
arm silently swallowed the case the second existed for.

The pass is compiler SOURCE, so it lives in the self-hosting subset like
everything else here. A nested `[ for x in xs do for y in ys -> ... ]` in
it built and passed every unit test, then died at the CORPUS fixpoint with
"not lowerable: list comprehension" — stage-1 compiling this very file.
`List.collect` instead. The tell that it was not the bounds work at all:
`FPP_NO_BOUNDS=1` failed the same way.

An access that is proven emits EXACTLY the code it did before checks
existed, register bindings included: binding the base defeats the hoist
that lifts it out of a loop, and that cost is real whether or not a check
is there to pay for it. That is why each site branches on
`boundsGuardPeek` rather than always taking the guarded shape.

Measured, best-of-five interleaved, checks on against `FPP_NO_BOUNDS=1`:
add, read, shapes, vertices are FREE (fully proven), and every benchmark
sits at the same prelude floor of emitted checks except `sort`, which keeps
exactly the two its partition scans need. `sort` pays 18% (1493 ms against
1258), all of it in that scan —
`while a.[i] < p do i <- i + 1` — which is in range because `p` is an
ELEMENT of the array, so the scan stops at it. That is a property of the
array's CONTENTS, not of any guard or arithmetic, and no compiler proves
it. `a.[lo + (hi - lo) / 2]` beside it IS derivable, and now is — see the
precondition section below.

Writing that guard yourself is NOT worth it, which is worth knowing before
anyone reaches for it. Guarding both quicksort scans elides every check in
qsort — measured, sg_on 1656 ms against sg_off 1661, so the checks really
do cost nothing there — and the whole benchmark still runs SLOWER than the
unguarded one with its checks left in (1656 against 1490). The guard is not
a comparison saved, it is a comparison MOVED: same test, but `&&` makes it
a second control-flow diamond in the tightest loop, and the engine handles
the check's shape better. Leave the check in.

A WARNING about reading these numbers. The stronger analysis emits 124
checks against the weaker one's 135 and does strictly less work at run
time, yet measures 1493 ms against 1410. The emitted qsort is
instruction-identical between the two; only the local NUMBERING differs,
because eliding an access skips its temporaries. That 6% is Cranelift
allocating differently, not work. Compare check COUNTS when judging the
analysis, and treat a single benchmark's milliseconds as the noisy signal
they are here.

### The check's real cost was the HOIST, not the compare

Worth knowing before optimising the compare. Measured on sort, the check
overhead split almost evenly: 238 ms for the compare and its loads, 271 ms
for the throw. But the two were not independent — the inline throw
ALLOCATES, `hoistStmts` refused to hoist loop-invariant global loads out of
any loop containing a safepoint, and so the array pointer was re-read from
its GC root slot (four instructions) on every single access.

The fix is a refinement to the hoist, not to the check: a safepoint on a
branch that always THROWS, traps or returns cannot make a hoisted pointer
stale for a later iteration, because there is no later iteration
(`escapesS`/`hasSafepointH`). That took sort from 1771 ms to 1407, and it
helps any loop with a `failwith` branch, not just bounds checks.

Two shapes measured WORSE and are recorded so they are not retried. Calling
one shared thrower instead of inlining: 1771 -> 2132 ms, because an untaken
call still makes the engine spill live registers around it every iteration.
Branching to one throw per function: wrong, not just slow — it leaves an
enclosing `try`'s scope before throwing, so the handler never sees it.

`FPP_BOUNDS_STATS=1` prints how many checks a build emitted and elided.
Read the EMITTED count, not the percentage: a proven access takes the fast
path and never reaches the counter, so "0% elided" with the emitted count
at the prelude floor means everything of yours was proven.

`for i in 0 .. arr.Length - 1` already evaluates the bound once: the loop
body contains zero `array.len`. That one was checked, not assumed.

## Emitting wasm

* **Declaration order must match body order.** The function section and the
  code section are positional; declaring `$hlen` third and emitting it fifth
  produces "unknown local" errors far from the cause.
* **Bodies are emitted twice** — a scratch pass then a replay — and both must
  allocate locals identically. Any cache that makes the second pass skip a
  `freshLocal` will desynchronise them.
* `wasm-tools validate -f all out.wasm` gives a far better message than the
  runtime does.

## The .NET collections, and the two rules that shaped them

`ResizeArray`, `Dictionary`, `MutableHashSet` and `StringBuilder` live in
the prelude and are gated by `stdlib/dotnet.fpp`, which runs under F++ AND under `dotnet fsi`
and must print the same 111 values. Two limits decided their shape, and both
will bite anyone extending them:

* **A generic class that implements an interface is monomorphized.** A
  vtable member keeps the canonical all-anyref signature, so it is never
  specialized and would read a packed `int[]` field as uniform. Each
  instantiation is therefore a SUBCLASS carrying its own vtable, and the
  class' constructor is forced into stamping so there is somewhere to hang
  it. Two traps if you touch this: an instantiated subclass must not claim
  ownership of its base's field names, and a member's quantified variables
  are NOT the class' — find the class' parameters positionally, through the
  receiver type.
* **A user type whose name matches a prelude type MERGES with it.** That is
  why the mutable set is `MutableHashSet`: the acceptance corpus ports a
  `HashSet` of its own.

Extra members exist that .NET does not have (`Reserve`, `SlotOf`, `Rehash`,
`KeyArray`) because there is no working `member private` convention here.
They are implementation, not surface.

## Qualification, and the first-identifier trap

`Impl.Node(k, v)` must mean what `Node(k, v)` means. It did not: constructor
overload selection searched the head for the FIRST identifier, which on a
dotted name is the MODULE, so a qualified call never reached selection and
took the primary constructor whatever its arity — and the mismatch surfaced
far from the call.

The rule: a dotted head is named by its LAST segment. Infer and Lower must
agree on which token they key by, or inference chooses one constructor and
emission calls another.

The same mistake hid in two places, and the second needed BOTH sides fixed:
a static member through a qualified type (`Inner.Box.Make`) bound in
inference but emission still built a closure over it, so it type-checked and
trapped. If you change one side, change the other.

**A type name declared at several ARITIES is now split** the way .NET splits
it: `IOpReader<'D>` and `IOpReader<'S,'D>` are `IOpReader` and `IOpReader`2`.
The first arity seen keeps the plain name; a use's WRITTEN type arguments
pick the variant, a bare constructor call chooses by argument fit across all
variants, and Lower learns a decl's decorated name via a `$tyname:` marker.
Same-name-same-arity across MODULES still merges — the port renames those
when private (see DIVERGENCES.md).

**A constructor scheme quantifies its DECLARED parameters first.** freeVars
order is encounter order, and `H<'S, 'D>(x : voption<W<'D>>, ...)` meets 'D
first — while the explicit application `H<'S, 'D>(...)` pins positionally
against scheme order. Crossed pins collapsed 'S into 'D, every History
constructor read Traceable<'a, 'a>, and NOTHING errored at the declaration —
it surfaced as "no constructor accepts these arguments" at every call.

**Types are keyed by BARE NAME**, so `IVal` and `IVal<'T>` share one entry.
`and IVal<'T> = inherit IVal` therefore recorded a type as its own base, and
the member walk never ended — a SHALLOW stack at 100% CPU, because the
recursion is a tail call. Both the record and the walk now refuse a cycle.
The same conflation still merges a nested private `Traceable<'T>` with a
global `Traceable<'S,'D>`; keying by name AND arity is the real fix.

**The extension-on-an-alias remap must not fire for the abbreviation's own
declaration.** Abbreviations are pre-registered before declarations are
walked, so `type MultiSetMap<'k,'v> = HashMap<'k, HashSet<'v>>` found ITSELF
in the alias table, took the name `HashMap`, and re-registered the alias
under it — after which every `HashMap<K, V>` in the project expanded with a
HashSet around its value type. Sixty-five diagnostics from one poisoned
entry, and none of them pointed anywhere near it. The tell was a HOVER on a
parameter disagreeing with its own written annotation — when those disagree,
suspect the alias table first.

The remaining 35 `List.tryFind (fun t -> t.Kind = Ident)` lookups in Infer
and Lower were audited as a group: all safe. Each is a binder/declaration
head (unqualifiable), an IdentExpr-guarded site (a dotted head parses as
DotExpr and takes a tryLast path), or a TypeDecl name. Two invariants carry
that conclusion, so guard them: `tokensOf` reads DIRECT children only —
switching a site to the recursive `Green.tokens` re-opens the trap — and
the parser collapses a dotted type-declaration name
(`type System.Threading.Interlocked with`) to its last segment, which is
the single point protecting every TypeDecl site.

## Overload resolution, and why it cannot be approximated

Selection unifies each candidate against what the call asks for and UNDOES
the attempt (`Types.unifyTrial`). Two things make that answer correctly, and
both were missing while two rounds of heuristics were tried in their place:

* the undo log is **threaded through the unifier**, never module state. Two
  workspaces type check at once under Expecto, and a trial that recorded —
  then undid — another thread's ordinary unifications corrupted both. It
  presented as five unrelated tests failing differently on every run, and as
  passing when reproduced alone.
* a type parameter a binding WRITES is **rigid** inside its body. The body
  must work for every instantiation, so a candidate may not decide that `'K`
  is `Cmp<'K>` to make itself fit. The flag is consulted only inside a trial.

An overloaded MEMBER is chosen at the application, with the arguments typed
first: that is the only moment the caller's parameters are still rigid, and
by the time an application has constrained the result the binding has been
generalized. The demand informs the CHOICE only — the chosen member is still
unified through the path that widens arguments, or `hs.UnionWith [ 5; 6 ]`
stops accepting a list where a seq is declared.

If you are tempted to approximate this again: the test is a call whose
argument types are still VARIABLES. Every candidate looks equally good there,
and that is the whole problem.

## Pattern identifiers

An identifier in a CASE pattern that starts with an uppercase letter names a
union case; it never binds. F# technically binds it (with warning FS0049) if
no case resolves, and this compiler's own source did exactly that once — a
list pattern `[ inner; GNodePat ]`. That is the shape to avoid: name pattern
binders in lowercase.

The strict rule applies only in match/try clauses. A `let`, a parameter or a
`for` still binds whatever name it is given, uppercase included.

## F# shape that keeps biting

`| None -> <rest>` swallows everything after it. Twice this silently moved
shared tail code into one branch — once skipping a type conversion, once
failing to advance a loop and hanging the compiler. Parenthesise a `match`
whose arms are statements and whose result continues below.

`if c then match ... with ... else e` is the same trap wearing a hat: the
`else` lands inside the last arm. The .NET build accepts it and the SELF-HOST
traps, which is a long way to travel for a missing bracket. Write the match
LAST — `if not c then e else match ...` — rather than parenthesising it.

**A builtin conversion is emitted at its APPLICATION.** `string` and `int`
are not functions in the emitted code, so `List.map string xs` used to leave
the bare name for the backend to stub — green build, trap when reached. It
now eta-expands: inference records the SOURCE kind at the bare identifier
(the same channel an application uses) and Lower wraps it in a lambda. If
you add a conversion name, add it to BOTH lists or the old trap returns.

## Conventions

Commit subjects are one line, ≤ 80 chars, no AI attribution. Release notes in
`RELEASE_NOTES.md` are append-only — nothing ever rolls off.

Comments explain *why*, and are worth their space when they record a fact
someone would otherwise have to rediscover — a measurement, a trap, the
reason a slower-looking path is the correct one. They are not narration of
the code below them.
