# Where F++ stands

A handover. What is built, what it is being built towards, and what is known
to be wrong — written so the next session can start without re-deriving any
of it.

Gates at the time of writing (all green, `main` at `53703ff`):

```
571 tests
corpus fixpoint    46699 bytes, byte-identical
self-host fixpoint 1513464 bytes, byte-identical
```

## What we are working towards

**FSharp.Data.Adaptive compiles as F++, whole.** All 41 files, 24,792 lines,
with the heart untouched: the algorithms, the data structures and the
adaptive machinery stay the library's. What may be replaced is what depends
on a runtime service F++ does not have, and each replacement must be a real
construct rather than a stub that lies.

It is a means, not the end. The library is a hard, real, self-consistent
body of F# — everything it needs, a hundred other projects need too. Each
gap it exposes gets closed in the COMPILER, generally, not worked around in
the port. Nothing so far has needed a FSharp.Data.Adaptive-specific hack.

`PORT-ADAPTIVE.md` has the port's own detail: the driver, what is replaced
and why, and the work list.

## How much is left — measured

The first-error frontier (line ~8,027 of 22,635 in the concatenated port) is
a pessimistic number: it stops at the first problem and says nothing about
the rest. Parsing each file ON ITS OWN is the honest measure, because a
parse error is a missing syntax feature while a type error mostly needs
cross-file context:

```
27 of 40 files parse clean standalone
13 have a parse error, every count a cascade from one construct
```

Re-run it with the loop in `PORT-ADAPTIVE.md`. The single biggest blocker
found this way was not a language feature at all — `#nowarn "7331"` stopped
six files outright.

## What was closed, and what it cost

Each of these was a general F# feature, not a port workaround. Sizes are the
real ones: most were 10–60 lines.

| | |
| --- | --- |
| the .NET collections | `ResizeArray`, `Dictionary`, `MutableHashSet`, `StringBuilder`, `System.Math`, the numeric statics |
| `.[ ]` indexers | `Item` / `set_Item`, and an ERROR instead of a trap when a type has neither |
| per-instantiation vtables | a generic class implementing an interface is monomorphized — the reason the collections can be seqs AND hold packed arrays |
| intrinsic type extensions | `type X with`, including on interfaces and on dotted names |
| multi-case active patterns | `let (|Add|Rem|) x` |
| the verbose class syntax | `type X = class ... end`, with `val` fields |
| `uint64`, `int16`, `uint16` | and the rest of `byte`/`sbyte`'s tower |
| F#'s adjacent-prefix rule | `f -x` is application of a negated argument |
| byref | declaration, forwarding, and `&x` copy-in/copy-out on locals and fields |
| type-level constraints | they BIND — `Box<Opaque>` is rejected — and F#'s spellings map onto classes |
| weak references | strong, honestly documented |
| compiler directives | `#nowarn` and friends |
| qualified construction | a dotted head is named by its LAST segment |

## Known problematic

### Qualification is not uniformly sound

**This is the live one.** `Impl.Node(k, v)` used to take the primary
constructor whatever its arity, because overload selection searched the head
for the FIRST identifier — which on a dotted name is the module. Fixed for
constructors, and `CLAUDE.md` carries the rule: a dotted head is named by
its LAST segment, and Infer and Lower must agree on which token they key by,
or inference chooses one thing and emission calls another.

What is still broken, found by qualifying everything in one program:

```fsharp
let d = Inner.Box.Make 3        // "unknown field Make"
```

A STATIC member reached through a qualified type. Everything else in that
program works — qualified functions, values, constructors, union cases in
expressions AND patterns, record-literal field labels, type annotations,
generic type applications.

There are ~30 more `List.tryFind (fun t -> t.Kind = Ident)` lookups in
`Infer.fs` and `Lower.fs`. Each is the same question — first segment or
last — and each is right only if its head cannot be qualified. They want
reading one at a time, not a blind sweep: some genuinely mean the first.

### Still missing for the port

* **computation expressions** — `ComputationExpressions.fs` and `seq { }`.
  The only remaining item that is a real feature rather than a small gap.
* **`use` / `IDisposable`** — 25 uses.
* **`lock` / `Monitor` (90) and `Interlocked` (13)** — real types in the
  prelude. A single-threaded runtime genuinely enters and exits every lock;
  that is an implementation, not a stub.
* **reflection outside ShallowEquality** — ~30 `typeof<>` sites in
  AdaptiveValue, HashSet, HashMap, IndexList, History, Cache. Read each:
  most are a cache key or a null test, which a class or a constrained
  function answers.

### Reproducible defects, with diagnoses

In `tests/known-issues/`, one file each, smallest program that shows it:

* **a generic class constructed inside another generic class' member** —
  the .NET `Enumerator<'a>` shape — canonicalizes the inner instantiation
  and traps. The member's own quantified variable is not the one the class
  is generic in, so the demand carries a variable the substitution does not
  know. Making those one variable is probably the whole fix.
* **`print` of a class-polymorphic expression** converts as though it were
  an int. `printfn "%f"` is unaffected; an annotated `let` fixes it.
* **a user type whose name matches a prelude type MERGES with it** rather
  than shadowing. This costs real surface: it is why the mutable set is
  called `MutableHashSet`.

### Deliberate divergences that will surprise someone

All in `DIVERGENCES.md`; these are the ones with teeth.

* **`WeakReference` is strong.** wasm-GC has no weak references and no
  finalizers. Reading through one is identical; what changes is that a graph
  relying on weakness to drop its dead half keeps it.
* **byref is not an ALIAS.** `&x` copies in and out around the call, so a
  callee reaching the same location another way does not see the write until
  the call returns.
* **`'a : struct` / `not struct` / `null` / `new`** have no counterpart —
  they describe a CLR representation. `comparison` and `unmanaged` DO map to
  classes.
* **`Unmanaged<'a>` has instances for every primitive**, but a struct needs
  its own. That is a job for a deriving plugin, and the compiler already
  computes the property when it lays out POD arrays.
* **Every program is ~2.5 KB larger** since the .NET collections landed — a
  fixed cost from the class declarations, not proportional.

## Working here

`CLAUDE.md` is the operating manual — the three gates and what they cost,
the traps, and the "measure, don't reason" rule with the specific wrong
intuitions that earned it. Two things worth repeating:

* **The gates earn their keep.** In this session the lossless-parse gate
  caught a constraint being dropped, the acceptance test caught a vtable
  regression, and the dogfooding gate caught a diagnostic that was too
  eager. None of those would have been found by the unit tests.
* **A failed build leaves the old binary in place.** `dotnet run --no-build`
  afterwards happily runs the previous prelude, and a "green" run against a
  stale prelude is the oldest trap in the repo.

Throughput, measured over this session: a feature plus its gate run is about
twelve minutes, so four or five an hour, and that is the ceiling worth
planning around.
