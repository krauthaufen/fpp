# Working in this repo

## Never ship a silently wrong answer

Documentation is for MISSING things. A construct this compiler accepts and
then answers incorrectly is not a known issue to write down — it is a defect
to FIX, or a construct to REJECT with a diagnostic. `tests/known-issues/`
may hold the first kind and never the second.

Three went out under that rule the day it was written:

* `decimal`. The `m` suffix was accepted and computed in binary, so
  `0.1m + 0.2m` answered 0.30000000000000004. There is no base-ten type
  here, so the suffix is a compile error now.
* units of measure. `[<Measure>]` declared an ordinary empty type and the
  `<m>` on a literal was PARSED AND DISCARDED — no part of the compiler
  ever knew the word — so `1.0<m> + 2.0<s>` answered 3 where F# rejects it,
  and `5.0<zzz>` was fine with zzz declared nowhere. Both halves are errors
  now, at the attribute and at the literal.
* integer `/` and `%` by zero. wasm's `div_s` TRAPS, and a trap is not
  catchable, so `try 1/0 with _ -> ...` ran its handler in F# and killed the
  program here. Guarded and raised now, like a bounds failure, so the same
  `with` sees it. A non-zero literal divisor skips the guard.

The shape to watch for is syntax that PARSES and is then ignored. It reads
as support, and the wrong answer arrives with no diagnostic anywhere. When
adding a feature, prefer rejecting the surface you have not implemented over
accepting it and doing something approximate.

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
tests/conformance/run.sh                              # 76 suites, fsi oracle
dotnet fsi  tests/bootstrap/fixpoint.fsx              # ~2 min, corpus
dotnet fsi  tests/bootstrap/fixpoint.fsx self         # ~7 min, THE gate
./tests/run-gates.sh --full                           # ~9 min, all 32, parallel
tests/tooling/perf/regress.sh --timing                # perf, on a QUIET box
```

There is ONE backend: wasm-linear over the fpprt/Whippet reactor (the C
backend shares its middle end). The wasm-GC backend — `BinDriver.fs`, the
`--wasmgc` flag, and the source maps that only it could emit — was deleted
once every gate ran on the linear one. `fixpoint.fsx` still accepts the
`linear` argument and ignores it.

`fixpoint.fsx self` is the real one: the compiler compiles its own sources,
and stage-1's output must equal stage-0's **byte for byte**. It has caught
bugs the unit suite missed — a `List.init` that counted down, an equality that
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

## The let-pattern classification lives in TWO files

Whether `let <pat> = e` is a simple binding or a DESTRUCTURE is decided by a
list of pattern kinds — and that list exists twice, once in Infer and once in
Lower. `ArrayPat` was in neither, so `let [| a; b |] = arr` typed as a simple
binding (a := the whole array) while lowering destructured it. The two
disagreed, and the symptom depended on the arity: one element gave a wrong
VALUE, two gave a type error at the next USE, nowhere near the binding.

Fixing one side alone is worse than fixing neither — that is the state where
inference and emission disagree. The comment above each list names the shapes
it covers; keep them identical.

## A qualified case pattern was a WILDCARD

`match c with Colour.Red -> .. | Colour.Green -> ..` took the FIRST arm for
every value. The type-qualified lookup in `recordQualifiedCase` was gated on
`idents.Length > 2` — written for `Inner.Colour.Green`, it never saw the
two-segment `Colour.Green`, where the type IS the whole prefix. Nothing was
recorded, so lowering found neither a binder nor a case and emitted `PWild`:
an irrefutable pattern. Every value took the first clause, silently.

The unknown-case diagnostic had the same hole — it covered the BARE
uppercase name only, so `Colour.Purple` on a type with no such case was
accepted and swallowed everything. It now reports through the same `missing`
channel whenever the prefix names a type that declares cases.

Worth generalising: this file's "Qualification, and the first-identifier
trap" section is about the same family, and the pattern side had been missed.
When a lookup for a dotted name is guarded by a SEGMENT COUNT, check the
smallest case — two segments is the common one, and it is the one an
arity-style guard tends to exclude.

## null is not the empty string, and the compare knew it was

String `=` lowers to `$str_cmp` (`ShStr` in structEqW), and both it and
`$streq` — which string PATTERNS compile to — began by loading the length
word from `ptr + 4`. For a null pointer that reads address 4, where a 0
happens to sit, so a null matched the EMPTY string: `("" = null)` answered
true and a null fell into a `| "" ->` clause. Both now test for null before
any load, and order null below the empty string the way .NET does.

`$eqv`, the generic structural walker, had it right all along — "a tagged
scalar, a null, or anything not addressable is equal only to itself". Only
the string-specialized paths skipped the check. When a specialization and a
general walker disagree, the specialization is usually the one that forgot
something.

`Unchecked.defaultof<string>` was a related miss: the `defaultof` token keys
`memberSites`, but there the entry is the TARGET type, not an owner — so the
string-member router turned it into a `$str.defaultof` primitive that does
not exist. Its own branch already answered null correctly; it just never ran.

And `isNull` used as a VALUE (`List.filter isNull`) hit the trap CLAUDE.md
already describes for `string`/`int`: emitted at its APPLICATION, so a bare
name reached the backend as an unknown and trapped. It eta-expands now, in
both Infer and Lower — the same two lists that note warns about.

## The seq widening compares NAMES, so check the arguments

`isSupertypeOf` answers on constructor names alone: `list` widens to `seq`
whatever the element types are. `unifyArg` then unified the arguments only
when they already fit, and DROPPED the mismatch otherwise — so
`String.concat "," [ 1; 2; 3 ]` type-checked and rendered three EMPTY
strings where F# rejects the call.

The mismatch is now a diagnostic, but only for the built-in container
widenings (`list`/`array`/`seq` into `seq`), where the element passes
straight through and so MUST pair. Two things it must NOT catch, both found
by the gates rather than by reasoning:

* a class widening to an interface — the `IOpReader` shape, where the class'
  own parameter is the ELEMENT and the interface's is the DELTA. They cannot
  pair, and the declared instantiation carries the real mapping.
* a NESTED widening — `array<array<string>>` reaching `seq<seq<'a>>` needs
  the inner array to widen too, which plain unification refuses. That case
  now recurses through `unifyArg` instead of erroring.

Report it directly with `vecAdd diags`, not by unifying the two whole types:
that path re-enters the same name-based widening and succeeds, so it says
nothing.

## A chosen constructor may live in ANOTHER file

Inference picks a constructor project-wide and records the WINNER'S OFFSET
(`ctorSites`). Lower resolved that offset through `defsAt`, which covers only
the file being lowered — so a prelude class' secondary constructor resolved
to nothing and the call quietly fell back to the primary. `ResizeArray<int>
([1;2;3])` type-checked, ran, and answered an EMPTY list: the argument was
simply dropped, with no diagnostic and no trap.

`foreignCtors` (Lower) indexes the project-wide member table by the `new`
keyword's offset — Resolve already keys an explicit constructor as
`Owner.new@<offset>` — and the lookup falls back to it.

The shape to remember: an OFFSET is only meaningful together with its file.
Any table keyed by a bare offset and consulted from another file's lowering
has this bug latent in it. The tell here was that the same class worked
verbatim in user code and failed in the prelude — when that happens, suspect
a cross-file table before suspecting the feature.

`new (args) as x = <delegate> then <body>` is what exposed it. That form now
DESUGARS in the parser to `new (args) = let x = <delegate> in (<body>; x)`,
which every later stage already handled — Resolve binds the let, Infer types
x from the delegate, Lower emits an `ELet`. Nothing downstream knows the form
existed. Parser-level desugaring is the cheap route for a construct that is
only sugar; the synthesized tree follows `apChain`'s conventions, including
`<bigconstant> + realOffset` for synthetic tokens, and the binder's
DEFINITION keeps the real token so hovers still point at the source.

## An inherited interface needs its OWN vtable row

A vtable row is keyed by interface NAME. F# requires a class implementing
`IDer` (which inherits `IBase`) to implement every inherited member in that
one `interface IDer with` block, so the functions were all there — but
nothing was filed under `IBase`, and a cast to it dispatched through table
index 0, which is `$novt`. The cast type-checked and the trap named only the
helper.

Two halves, and both were needed:

* `isSupertypeOf` checked a class' implemented interfaces with a flat
  `List.contains`, so it never stepped into an interface's own bases. An
  interface's `inherit` is recorded in `bases`, so recursing into each
  implemented interface reaches it.
* `ifaceRowsFor` (Lower) now expands one block into a row per inherited
  interface, sharing the same lifted functions — a table slot, not a copy.
  Both producers of rows have to call it: explicit `interface ... with`
  blocks AND object expressions, which build their own synthetic class. The
  class half alone left `{ new INamedShape with ... } :> IShape` trapping.

`use` had a related hole. An interface implementation is not an ordinary
member — `r.Dispose ()` on a class that merely implements IDisposable is a
compile error in F#, and lookup here agrees — but `use` is exactly the
construct that reaches through the interface anyway. It looked up Dispose as
a plain member, found nothing, and lowering quietly emitted a plain `let`.
The resource was never disposed and nothing was said, `--strict` included.

Both are the same lesson as the parked queues below: when a lookup fails,
check what the fallback DOES. Silently emitting the unadorned construct is
how these stay invisible.

## The two parked queues must advance TOGETHER

Inference parks what it cannot yet place: `pendingDots` for a member whose
receiver has no type, `pendingIndex` for an index whose receiver is not yet
known to be an array. They used to drain one after the other, dots first,
because an index's receiver often takes shape through a parked dot.

The dependency runs BOTH ways, and the other direction had no path. Adding a
second `string.Split` overload was enough to expose it: overloaded, the call
parks, so `lines` has no type, so `lines.[0]` parks, so the `.Trim()` on it
finds no receiver — and by the time the index pass ran, every dot retry was
already behind it. The member reached emission unlowered and the backend
answered `unreachable`. **`--strict` said nothing**, because nothing was
recorded as missing; the tell was a Core dump still showing
`(lines.[0].Trim ())` as a bare member instead of `$str.Trim`.

They now advance to a joint fixpoint (`indexProgress`, called inside the dot
loop). The final index pass still owns the diagnostics for receivers that
genuinely cannot be indexed, and skips what the fixpoint already named —
naming a site twice would file a second `arrKindsRaw` entry for it.

Worth remembering as a shape, not just a bug: adding an OVERLOAD to an
existing member is never local. It moves that member from the eager path to
the parked one, and anything downstream that needed its result type
immediately now needs it later. The regression showed up in `.TrimEnd`,
whose overloads nobody had touched.

A related trap from the same change: intercepting a member BY NAME in Lower
(`String.Join`) also grabbed the prelude's own list-taking `String.Join` and
forced its argument to an array. Only the `System.`-qualified spelling needs
the interception — that is the one whose `System` never resolves.

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

**The benchmarks gate, but only their stable half.** `perf-regress` checks
every benchmark's ANSWER against a recorded checksum and the number of
bounds checks it still emits — both load-independent. It does NOT check the
clock: the gate suite runs eight jobs at once and under that load these
numbers trebled (avl 1990ms -> 6553). Timing is `regress.sh --timing`, run
by hand on a quiet machine, with a 1.5x ceiling. `--record` rewrites
`baseline.txt`.

The static half is not a consolation prize — a checksum change means the
program stopped computing what it computed, and a rise in the emitted-check
count means the proof pass lost a rule, which is the failure most likely to
creep in unnoticed.

Read the SHAPE of a count rise before chasing it. The count is a floor plus
the program's own checks, so linking one more prelude function raises EVERY
benchmark by the same amount — adding `List.toArray` to a `StringOps` member
put all nine up by exactly one, via `Array.ofList`, whose `r.[i] <- x` is
in range only if two separate `for _ in xs` traversals of the same list
agree in count. Nothing in the domain expresses that, and `Array.ofList` is
in no hot loop, so the answer there is `--record`, not a new rule. A rise on
ONE or TWO benchmarks is the real signal.

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

## Optimisations, and what they are worth

There is no global optimisation switch. `St.Opt` does not exist — that was
the deleted wasm-GC driver, and the paragraph describing it outlived the
backend it described. Treat a claim in this file as suspect until you have
grepped for the thing it names; several were stale by a whole backend.

On by default: POD array bases are hoisted out of loops (`hoistE`); a
literal-valued top-level `let` is emitted as its literal; the
pinned/unpinned test is dropped for types the program never pins; a record
literal stored into a POD array is written field-by-field rather than via a
materialised struct; `let v = arr.[i]` splits the element into unboxed
locals (the last two are the same fix from opposite sides — never
materialise a GC struct for a POD element); one-instruction class wrappers
are inlined at their call sites; and a loop's exit test is the guard
NEGATED rather than `cond; i32.eqz`, which is worth 8-10% on a tight
streaming loop (read 49 -> 45 ms, vertices 58 -> 52).

## Unrolling and strength reduction: BOTH implemented, BOTH off

`FPP_UNROLL=1` and `FPP_STRENGTH=1`, in WasmLin over LowIR. They are off
because they were measured, not because nobody got to them:

    bench      base   unroll  strength   both
    read       43ms     44ms     43ms     42ms
    vertices   52ms     52ms     53ms     54ms
    shapes    247ms    239ms    240ms    241ms
    matmul    103ms    131ms    103ms    101ms     <- unroll 27% WORSE
    nbody     392ms    397ms    389ms    390ms
    sort     1495ms   1494ms   1495ms   1538ms
    avl      1812ms   1812ms   1815ms   1801ms
    trees     897ms    898ms    898ms    898ms

Nothing outside the noise, and unrolling costs matmul 27%. Strength
reduction is a wash for a reason the emitted code shows plainly: the
multiply it takes out of the address (`i*12` — get, const, mul, add) is
replaced by a bump beside the counter (get, const, add, set), so the body
gets LONGER by two instructions. Wasm has no addressing mode to fold an
index into, which is why the trick pays on a native target and not here.

Unrolling is innermost-only and capped at 60 nodes for a reason worth
keeping: unrolling a loop that contains another copies the inner one too,
and copies multiply as 3^depth.

THE FIXPOINT CANNOT VALIDATE EITHER FLAG. `GetEnvironmentVariable` answers
null inside the wasm-hosted compiler (`System` is one of the roots that
reach the backend unresolved), so with `FPP_UNROLL=1` stage-0 unrolls and
stage-1 does not, and the fixpoint reports a byte mismatch that means
nothing. Check these passes with the CONFORMANCE suite instead — all 76 are
green under unroll, strength and both.

VERIFY THE PASS FIRES BEFORE BELIEVING A NULL RESULT. The first measurement
of both showed "no change" because the wiring matched only a top-level
`LDo`, which a function body rarely is — the passes ran over nothing and
still reported a clean build, which looks exactly like an honest zero. Check
the emitted wat (loop count for unrolling, the address shape for strength
reduction), not the wall clock.

### Two more that were measured and REVERTED

Inlining `$toi` everywhere, and caching `i * stride` across an element's
fields (the engine already does that one). Do not re-add either without a
number.

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
the prelude and are exercised by `stdlib/dotnet.fpp`. That file is a MANUAL
check, not a gate: nothing in `run-gates.sh` runs it, and running it under
`dotnet fsi` needs shims for `print` and for `MutableHashSet` (F# spells
that one `HashSet`). It prints 142 lines as of this writing — an earlier
version of this paragraph said 111 and asserted a gate that does not exist. Two limits decided their shape, and both
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
