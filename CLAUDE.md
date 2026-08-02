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
dotnet run  -c Release --project tests/Fpp.Tests      # ~2 min, 645 tests
dotnet fsi  tests/bootstrap/fixpoint.fsx              # ~2 min, corpus
dotnet fsi  tests/bootstrap/fixpoint.fsx self         # ~7 min, THE gate
```

`fixpoint.fsx self` is the real one: the compiler compiles its own sources,
and stage-1's output must equal stage-0's **byte for byte**. It has caught
bugs the 578 tests missed — a `List.init` that counted down, an equality that
compared tree shape instead of contents. If you change the backend and only
the unit tests pass, you have not tested your change.

**A `let rec ... and` group inside `lower` miscompiled under SELF-HOST**
while the .NET build and all 637 tests passed. The symptom was an
`unreachable` deep inside an unrelated lambda, and the branch the group
existed for was never even reached during the failing compile. Two ordinary
bindings in place of the group fixed it with no other change. If something is
green everywhere and the fixpoint dies, suspect the SHAPE of what you wrote
rather than its logic — `tests/known-issues/let-rec-and-group-self-host.fpp`
records what was ruled out.

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

## Measure, do not reason

Almost every performance intuition recorded in this repo's history was wrong,
including several in a row. The vertex benchmark went from 3615 ms to 191 ms
against C's 71 ms, and the causes were never where they looked:

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

### Bounds checks: there is nothing to eliminate

Worth knowing before someone sets out to write the pass. The compiler emits
NO bounds check of its own — the check lives inside `array.get`, and wasm-GC
has no unchecked variant to emit instead. The only path without a per-element
check is a PINNED array, which reads linear memory with a plain load, and
that is worth about 8% (191 ms against 175 ms on the vertex benchmark). It is
not the gap to C.

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

There are ~30 more `List.tryFind (fun t -> t.Kind = Ident)` lookups in Infer
and Lower. Each one is this question — first or last — and each is right
only if its head cannot be qualified. Worth auditing as a group.

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

## Conventions

Commit subjects are one line, ≤ 80 chars, no AI attribution. Release notes in
`RELEASE_NOTES.md` are append-only — nothing ever rolls off.

Comments explain *why*, and are worth their space when they record a fact
someone would otherwise have to rediscover — a measurement, a trap, the
reason a slower-looking path is the correct one. They are not narration of
the code below them.
