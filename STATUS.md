# Where F++ stands

A handover. What is built, what it is being built towards, and what is known
to be wrong — written so the next session can start without re-deriving any
of it.

Gates at the time of writing, all green (the numbers move; the shape does not):

```
638 tests
corpus fixpoint    53463 bytes, byte-identical
self-host fixpoint 1606039 bytes, byte-identical
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
| computation expressions | `seq { }` and any builder. The rewrite is F#'s, read off the F# compiler by quoting and printing the desugared AST, and gated by an oracle suite that diffs the CALL TRACE. `Run` and `Delay` appear exactly when the builder declares them, which needs the builder's type — so a probe pass types it first |

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

~~computation expressions~~ and ~~`use` / `IDisposable`~~ are done, and so
are twelve syntax blockers the 40-file standalone parse was stuck on. That
is **39 of 40 parsing clean**, up from 27:

| | |
| --- | --- |
| `#seq<'T>` and `^T` inside a generic argument | both were LEXED into the angle bracket — `<#` and `<^` came out as ONE operator, so the argument list was never entered |
| `assert` | a real check, not F#'s elided one: a wasm module has no debugger to notice the difference |
| `not` as a value | `f >> not`, where the keyword has nothing to negate |
| `instance` | F++ had reserved it and F# had not, and `static let instance = ...` is how a type holds a singleton of itself. Contextual now |
| `base.M()` | the base's OWN implementation, called directly however virtual it is. An `abstract` slot and the `default` that fills it are both recorded under the type, and reading the first was calling a function with no body |
| `abstract member P : t with get, set` | the accessors are named, never bodied |
| `exception E of label : int` | a labelled payload |
| `type C(args) as this` | parsed; what the name MEANS is still open |
| `x <- <block>` | an assignment may take a whole block, and only an assignment may |
| `{ new Base(args) with ... }` | an object expression over a class passes base constructor arguments |
| a clause list undented inside brackets | `f (x, function` puts its clauses left of the keyword — the bracket delimits the group, so the offside line is the enclosing statement's. What it may not undent past is a clause list or block that ENCLOSES it |
| `function` | parsed all along and never lowered. It is the lambda whose body matches on its own argument, and nothing else |

**Overload resolution is real now**, and the two heuristics that stood in
for it are gone. What was there tested candidates STRUCTURALLY — deliberately,
to avoid a trial unification corrupting the losers — and a structural test
has to call every unresolved type a wildcard. So a three-parameter member fit
a one-argument call, and two constructors of the same arity both fit
everything, and in each case the overload declared FIRST won. Two rounds of
patching that (arity first, then a specificity score) fixed the symptoms in
front of me and would have gone on doing so.

What it takes to ask the question properly is two mechanisms:

* **A trial that can be undone.** `unifyTrial` unifies for real and puts back
  every link and level it changed, so one candidate's attempt cannot narrow
  the types the next one is judged against. The undo log is threaded through
  the unifier rather than kept in module state — two workspaces type check at
  once in the test harness, and a trial that recorded, then undid, another
  thread's ordinary unifications corrupted both. That failure was flaky and
  looked nothing like its cause.
* **Rigid type variables.** A type parameter a binding WRITES is not the
  candidate's to choose: inside `let singleton (key : 'K) (value : 'V)` the
  body must work for every instantiation, so `Cmp<'K>` does not accept `'K`.
  This is why F# rejects the constructor F++ was picking, and the flag is
  consulted ONLY inside a trial — ordinary unification is untouched.

And one ordering fix: an overloaded member is now chosen at the APPLICATION,
with the arguments typed first, because that is the only moment the caller's
parameters are still rigid. Waiting for the application to constrain the
result afterwards was too late — the binding had been generalized by then,
and the member's result came out quantified and empty, which is why
`MapExt.slice` used to return something with no members.

Two rules survive as second and third word, and both are F#'s: widening gets
a second chance when nothing fits exactly (`Equals : obj -> bool` takes
anything once obj widens), and declaration order breaks a genuine ambiguity.

**A type that declares `CompareTo` is ordered**, decided by the compiler
rather than by a shim. F#'s `'a : comparison` is satisfied by IComparable and
`Ordered<'a>` is how that constraint is spelled here, so a library
implementing comparison the .NET way must not also have to declare an
instance it never wrote — the goal is the library compiling with its
REFLECTION replaced and nothing else. The member lifts to a function of the
receiver and the argument, which is exactly `compare`'s shape, so the
instance points straight at it and no code is synthesized. An explicit
instance still wins.

Two things that cost a debug cycle each and are worth knowing: the instance
has to exist by the time the DECLARATION finishes, because a body typed
later asks for it and asking is the only chance it gets; and its member must
be named `compare`, not `CompareTo`, because that name is also what tells
lowering to wrap the result — `a < b` is `compare a b < 0` only for a member
by that name, and without it the raw int stood in for the boolean and both
directions came out true.

**A comma pattern takes apart whichever tuple it is matched against.** It
says nothing about which kind it is, and F# reads that from the scrutinee:
`ValueSome (a, b)` over a struct-tuple payload is allowed, the same pattern
in a `let` is not. Both were measured before either was implemented.

Typing a pattern is bidirectional now — the scrutinee flows in, a union case
ties its RESULT to it before its payload pattern is typed, and a comma
pattern that finds a struct tuple waiting marks itself in the owner channel
so lowering binds the payload whole and reads the fields out. The `let` form
stays an error, and it is one for the first time: the mismatch was being
computed and then DISCARDED, so the binding compiled and trapped, which is
the worst of the three outcomes available.

The frontier has moved **8155 → 10857**. `MapExt.fs` and `IndexList.fs` up to
that line type check whole, and IndexList's diagnostics are down from 60 to
14.

**An explicitly generic value is generic.** The value restriction exists to
withhold generality from a binding that made no promise; `let empty<'k, 'v> :
MapExt<'k, 'v> = ...` makes exactly that promise, and F# reads it the same
way. Without the exemption every use of `MapExt.empty` shared ONE type, so a
map bound empty before a loop was tied to the map the loop read from, and
storing a pair into it asked `'T` to become `'T * 'T`.

That is worth remembering for its SHAPE: it surfaced as an occurs check on a
tuple expression, in a member, several lines from the binding responsible —
and reducing it made it vanish, because every ingredient except the shared
`empty` was incidental. The cause was two files away, in a `let` with no
loop, no tuple and no pattern in it.

With it, `IndexList.fs` goes from 14 diagnostics to **2**, both on one line.

Then, still measured:

* **optional parameters** — `static member F(path : string, ?retries : int)`,
  the last file that does not parse (`AdaptiveFileSystem.fs`). Parsing them
  is small; what is not is that a caller may OMIT one, which changes how a
  call's arity is resolved — the same machinery the overload bug above wants.
* **a 22k-line file with parse errors in it makes inference crawl.** The
  whole-library `check` ran past ten minutes; parsing the same text takes
  200ms. Error-recovery nodes are the difference, and nothing bounds what
  inference does with them.
* **a class-body `do` has no `this`** — the constructor runs its `do` blocks
  BEFORE it allocates, so `do base.M()` and `do this.M()` have no receiver.
  Reordering is what F# does, and it would change where a `do` block's writes
  to a class `let` land.
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

## A paren tuple builds the struct it is asked for

The mirror of the pattern rule, measured the same way: F# builds a STRUCT
tuple from `(a, b)` when a struct tuple is what the context asks for.
`PairwiseCyclicV` writes `struct(v0, v1)` in its loop and `(v0, initial)`
after it, into the same map, and that is verbatim library code.

The expectation has to reach the tuple from a LATER argument — in
`add k (a, b) m` the parameter is still a variable when the tuple is typed,
and only `m` says it is a struct — so an application ties its RESULT to its
context before typing arguments. Tying EVERY application that way is a much
bigger change than this question needs (it takes the result away from the
widening the argument path does, and it turned 45 tests red), so the tie is
made only when an argument is a tuple literal, and only when a trial says it
cannot fail.

The expectation is consumed once, at the top of `exprTypeOf`, by whichever
node is being typed. Left standing it leaks into a NESTED expression: it
reached a constructor inside `ValueSome struct(v, HashMap(...))` and tied its
result to the tuple. Parentheses pass it through deliberately, because
`(a, b)` as an argument is a ParenExpr wrapping the tuple.

With that, `IndexList.fs` is clean, and so are `HashSetDelta.fs`,
`Deltas.fs`, `MultiSetMap.fs` and `Utilities.fs` behind it.

## Three more, from PriorityQueue and Utilities

**`List<'a>` is what .NET calls `ResizeArray`**, and F# code means it once
`System.Collections.Generic` is open. The `List` MODULE is a different thing
under the same name, exactly as in F#.

**An extension on an abbreviation extends what it abbreviates.** `type
List<'T> with` adds members to ResizeArray. Resolution is per file and cannot
know that — the abbreviation is usually in another one — so the member key is
aligned in the workspace, where the project's aliases are known.

**A let-bound operator is a call.** `let (+++) a b = ...` binds a name that
FUSES, the way `(+)` does everywhere else; parsed as a pattern it came out as
a parenthesised section and the binding had no name at all. Its uses resolve
like any other name and lower to calls.

The line that took two attempts: a symbol the CLASS layer owns keeps its
dispatch. `/` is `Div.(/)`, chosen by the operand type, and a class declares
it exactly as a binding does — so filtering on "is it let-bound" was not
enough, and the prelude's own arithmetic started calling declarations with no
body. The filter is the class layer's own operator set.

## Reading a byref is reading what it holds

F# dereferences a byref read silently — `let mutable initial = location`
copies the value — and F++ required `location.Contents`, which no F# code
writes. Reads dereference now. Two positions want the CELL and say so: the
operand of `&`, which forwards it, and the left of an assignment, which
writes through it.

The prelude's `Interlocked` was written in the explicit idiom and is now
written the way F# writes it, which is the point: `location <- location + 1`.

Three tests changed with it, and that is a contract change worth naming.
They passed a hand-built `{ Contents = 0 }` as a byref argument and read
`cell.Contents` back — neither is expressible in F#, where a byref value can
only be made with `&`. They now say `let mutable cell = 0`, `&cell` and
`cell`.

## A struct payload inside a tuple pattern

`| ValueSome(_, l), ValueNone ->` matches a TUPLE, so the expectation has to
reach the ELEMENTS of the clause's pattern before either case can know its
payload is a struct. Lowering then binds each payload whole and reads its
fields out, at whatever depth the case sits.

**And a self-host trap that cost an hour.** The lowering half was written as
a `let rec hasStructPayload ... and structPayloadOf ...` group. Every test
passed, the .NET build was clean, and the CORPUS gate died with an
`unreachable` deep inside an unrelated lambda. Bisecting showed the nested
branch was never reached during the failing compile — it was the SHAPE, not
the logic. Splitting the group into two ordinary bindings fixed it with no
other change. Banked as
`tests/known-issues/let-rec-and-group-self-host.fpp`, which is honest that
it does not reproduce in isolation.

That is the gate earning its keep again: 637 tests and a clean .NET build
said yes, and the compiler could not compile itself.

## A lambda's parameters are tied before its body

The last of the struct-tuple chain. A lambda's parameters were fresh
variables while its body was typed, so `(fun left self right -> match left,
right with | ValueSome(_, l), ...)` had nothing to read the struct-ness
from. The expected type reaches the parameters first now, and
`PriorityQueue.fs` is clean.

The frontier is **11177** — every file through `Utilities/PriorityQueue.fs`
type checks whole.

## Where it stops now

`Utilities/Cache.fs`, two diagnostics, and both are new KINDS of gap rather
than more of the same:

* **block comments inside an array literal.** `[| (* prime no. *) 7 ... |]`
  reports `int vs int -> 'a`, which is what `(*)` applied to `7` would say —
  so the comment is being read as a multiplication section somewhere the
  lexer's block-comment rule does not reach.
* **object initializers.** `new TransactQueueEntry<_>(Hash = h, Slot = s,
  ...)` sets properties in a constructor call; the `Prop = v` pairs are being
  read as equality comparisons, which is why the type comes out as a tuple of
  bools.
