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
dotnet run  -c Release --project tests/Fpp.Tests      # ~2 min, 534 tests
dotnet fsi  tests/bootstrap/fixpoint.fsx              # ~2 min, corpus
dotnet fsi  tests/bootstrap/fixpoint.fsx self         # ~7 min, THE gate
```

`fixpoint.fsx self` is the real one: the compiler compiles its own sources,
and stage-1's output must equal stage-0's **byte for byte**. It has caught
bugs the 534 tests missed — a `List.init` that counted down, an equality that
compared tree shape instead of contents. If you change the backend and only
the unit tests pass, you have not tested your change.

Three details that will bite:

* **The prelude is an embedded resource.** Editing `stdlib/prelude.fpp` does
  nothing until you rebuild. A "green" run against a stale prelude is the
  oldest trap here.
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

Two were tried, measured, and **reverted** for not paying: inlining `$toi`
everywhere, and caching `i * stride` across an element's fields (the engine
already does that one). Do not re-add them without a number.

## Emitting wasm

* **Declaration order must match body order.** The function section and the
  code section are positional; declaring `$hlen` third and emitting it fifth
  produces "unknown local" errors far from the cause.
* **Bodies are emitted twice** — a scratch pass then a replay — and both must
  allocate locals identically. Any cache that makes the second pass skip a
  `freshLocal` will desynchronise them.
* `wasm-tools validate -f all out.wasm` gives a far better message than the
  runtime does.

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
