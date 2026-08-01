# Where F++ stands

A handover. What is built, what it is being built towards, and what is known
to be wrong — written so the next session can start without re-deriving any
of it.

Gates at the time of writing, all green (the numbers move; the shape does not):

```
589 tests
corpus fixpoint    53463 bytes, byte-identical
self-host fixpoint 1555145 bytes, byte-identical
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
| qualification | a dotted head is named by its LAST segment — constructors, static members, base classes, and cases through their type |
| `System.Threading` | `lock`, `Monitor`, `Interlocked` — real, on one thread |
| `use` and `try`/`finally` | disposal at end of scope, on the normal path and the raising one; `IDisposable` in the prelude and on `IEnumerator<'a>`, as .NET has it |
| computation expressions | `seq { }` and any builder — rewritten into method calls BEFORE resolution, so one tree serves resolve, infer and lower |

## Known problematic

### Qualification

Four holes were found by writing programs that qualify everything, and all
four are fixed:

* a qualified CONSTRUCTOR took the primary overload whatever its arity
* a STATIC member through a qualified type did not resolve at all
  (`Inner.Box.Make`)
* a qualified BASE class did not parse (`inherit Inner.Base(s)`)
* a union case named through its module AND its type
  (`Inner.Colour.Green`) resolved in neither expression nor pattern
  position — no value carries that whole path, so the lookup has to go
  through the TYPE, which is the second-to-last segment

Both were the same mistake in two places: searching a head for its FIRST
identifier, which on a dotted name is the module. The rule, now in
`CLAUDE.md`: **a dotted head is named by its LAST segment**, and Infer and
Lower must agree on which token they key by — the static-member fix needed
BOTH sides, because inference bound the member while emission still built a
closure over it.

The base-class fix carries its own lesson: the qualified spine has to STAY
in the tree — the resolver binds the path through it, and dropping it broke
losslessness — while the readers take the last segment. And the name is the
last segment of the NamedType NODE, not the last token of the inherit:
`inherit HashNode<'k, 'v>(0)` ends in a type ARGUMENT, so reading tokens
blindly renamed the base to `'v`.

Verified working: qualified functions, values, constructors (with and
without explicit type arguments), static members, base classes (generic
ones too), interface implementations, union cases in expressions AND in
patterns, record-literal field labels, type annotations, generic type
applications, union cases through module AND type in expressions and
patterns, and modules nested two deep.

There are ~30 more `List.tryFind (fun t -> t.Kind = Ident)` lookups in
`Infer.fs` and `Lower.fs`. Each is the same question, and each is right only
if its head cannot be qualified. The two that mattered are done; the rest
want reading one at a time rather than a blind sweep, since some genuinely
mean the first.

### Still missing for the port

Expression and pattern position resolve SEPARATELY — the case-through-type
fix needed both — which is worth remembering for anything else qualified.

~~computation expressions~~ and ~~`use` / `IDisposable`~~ are done. What the
40-file standalone parse still stops on, measured rather than guessed —
**27 of 40 parse clean**, unchanged by the CE work because the blockers were
never CEs:

* **flexible types in a member's parameters** — `member x.For(elements :
  aval<#seq<'T1>>, ...)`. `#T` parses in some positions and not this one,
  and it stops `ComputationExpressions.fs` itself.
* **`do base.M()` in a class body** — `AdaptiveObject.fs`, `Core.fs`,
  `Transaction.fs`, `Callbacks.fs`.
* **`member x.Invoke(a : T, b : U, ...)` mangled by the port harness** into
  `member (x (a : T) (b : U)) =`. That one is the DRIVER's bug, not the
  compiler's — `port_closures` rewrites a tupled member and loses the name.
* **reflection outside ShallowEquality** — ~30 `typeof<>` sites in
  AdaptiveValue, HashSet, HashMap, IndexList, History, Cache. Read each:
  most are a cache key or a null test, which a class or a constrained
  function answers.

The type-checked frontier moved from line 8027 to **8156 of 22,635**, and
what it stops on now is `IndexList`/`MapExt` typing, not syntax.

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

* **`Monitor` never blocks.** A single-threaded runtime genuinely enters and
  exits every lock and an increment genuinely is atomic, so `lock`,
  `Monitor` and `Interlocked` do exactly what .NET's do under the assumption
  the platform enforces. What is absent is any way to WAIT: `Monitor.Enter`
  on a lock someone else holds cannot happen.

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
