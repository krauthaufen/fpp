# Where F++ stands

A handover. What is built, what it is being built towards, and what is known
to be wrong — written so the next session can start without re-deriving any
of it.

Gates at the time of writing, all green (the numbers move; the shape does not):

```
653 tests
corpus fixpoint    53463 bytes, byte-identical
self-host fixpoint 1622242 bytes, byte-identical
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

## Cache.fs: three, and each one under the last

* **Array elements are ELEMENTS.** `[| 7 \n 13 |]` parsed each element
  against the enclosing context, so the next line became an ARGUMENT of the
  one before. It had been invisible because elements usually sit left of the
  outer column; a leading block comment moves them right, and
  `(* prime no. *) 7` is what exposed it. Each element parses at its own
  column now.
* **A type whose storage is DECLARED gets a primary constructor.**
  `type E() = val mutable X : int` had none — `E()` named a constructor
  nothing emitted, and the type could only be built by an explicit `new`.
  F# zero-initializes; so does this.
* **Object initializers.** `new T<_>(Hash = h, Slot = s)` sets fields on what
  the constructor made. Read as an application, each pair is an equality test
  and the call comes out as a tuple of bools.

Two things the initializer needed that are worth knowing. The head must name
a TYPE: `LBool (b = "1")` applies a union CASE to a comparison and is
otherwise identical — that one was caught by the dogfooding gate, in the
compiler's own `Serialize.fs`. And with `new T<_>(...)` the head is an
application whose LAST identifier is a type ARGUMENT, so the name is the
first one.

The frontier is **11741** — everything through `Core/Core.fs`.

## `HashSet` means two types, and the harness replays which

`Core/Core.fs` writes `HashSet<WeakReference<IAdaptiveObject>>()` and
mutates it: that is `System.Collections.Generic`'s, because the file's
HEADER opens that namespace last. F# is last-open-wins — measured against
the real compiler, not assumed — and F++ identifies a type by its bare NAME,
so two called `HashSet` merge and the port's flattening destroys the
namespaces that told them apart.

Until a type can be told apart by more than its name, the harness replays
the resolution F# performed: in a file whose HEADER opens
`System.Collections.Generic` last, and which does not itself DECLARE the
name, `HashSet<` is the mutable one.

Both qualifications are load-bearing and both were found by getting it
wrong. Reading the WHOLE file for the last open catches one nested inside a
module — `Deltas.fs` has exactly that, and rewriting its uses moved the
frontier backwards by 1,400 lines. And `HashCollections.fs` opens the
namespace in its header while declaring `HashSet` itself, all 77 uses its
own.

**This is still a workaround for a missing mechanism**, and the mechanism is
named: types identified by more than their bare name, which reaches the
backend, where every type is a string. `MutableHashSet` exists for the same
reason, and so does "a user type whose name matches a prelude type MERGES
with it".

## The tuple view of an out parameter is SYNTHESIZED

F# creates it for every method with a trailing out parameter:
`d.TryGetValue k` is `(found, value)` where the declaration says
`TryGetValue(k, value : byref<_>)`. The prelude had been writing both by
hand, which is the compiler's job — a library declares .NET signatures and
calls them either way, and the port cannot be asked to spell them
differently.

Inference picks the view when the declared shape does not fit what the call
asks for and the view does; lowering makes the cell, passes it, and reads it
back beside the result. `Dictionary.TryGetValue`, `WeakReference` and the
weak table now carry one declaration each instead of two.

It had to go in TWICE — a member of the file being compiled binds through
`tracked`, a separate path from the general one, and putting the view only
in the general path left every same-file `TryGet` unchanged. That split is
worth remembering for anything else that adapts a member's type.

## Interlocked is generic, as .NET's is

`Interlocked.Exchange(&finalizers, [])` swaps a LIST. Declaring these at
`int` alone made that a type error; `Exchange` and `CompareExchange` are
generic now, and `AdaptiveToken.fs` types past them.

## `ref` cells, and what makes a read dereference

F# has `byref<'T>` for a location a callee may write and `Ref<'T>` for one a
program passes around. wasm-GC has no address of a local, so both are one
cell here — and what tells them apart is the **declaration**, not the type.

The automatic dereference was keyed on the TYPE, which meant every cell
dereferenced: `r.Value` read through it twice and trapped. It is keyed on the
parameter being written `byref`/`outref` now, which is exactly F#'s rule, and
`ref` is one line of prelude on top of it.

Worth recording how that was nearly mis-filed. The trap was banked as a
known issue marked PRE-EXISTING, on the evidence that it failed before the
change — but the change was already COMMITTED, so "before" included it. The
right check is to disable the suspect and re-run, which took one build and
found the cause immediately.

## Array slices

`a.[lo..hi]` and `dst.[lo..hi] <- src`. Three uses in the whole library, and
they only surfaced once `ref` typed — before that the enclosing function was
untyped and the slice was never reached, which is the pattern all day: a fix
does not move the frontier so much as reveal the next thing.

The write has to be recognised BEFORE its target is lowered. Lowering the
target reads the slice, and a read is not a place to write to.

## Type abbreviations are registered before any signature is read

In an `and` group the abbreviation can come after the interface that uses it:
`IAdaptiveValueVisitor` takes an `aval<'T>` three lines above `and aval<'T> =
IAdaptiveValue<'T>`. Registering abbreviations in declaration order left that
parameter opaque, so no argument ever widened into it and every `v.Visit x`
in the library failed. A pre-pass registers them all first.

## Measuring the port stopped being the slow part

Inferring all 22,332 ported lines took longer than ten minutes and was never
seen to finish; it now takes eight seconds. The cause was a base-chain cycle,
not volume — see CLAUDE.md. That changes how the work is done: the whole
remaining error set is visible at once instead of one error per run.

## Optional and named arguments

Both, and every call form F# allows:

    Dir.Get "root"                                        omitted -> None
    Dir.Get("root", recursive = true)                     named, skipping one
    Dir.Get("root", "*.fs", true)                         positional, wrapped in Some
    Dir.Get(path = "x", recursive = true, pattern = "p")  all named, out of order
    Dir.Get("root", ?pattern = p)                         the option passed through

A name is an argument name only when the CALLEE declares it — everywhere else
`x = v` is still an equality test, and a test says so. Inference puts the
arguments in declaration order and leaves Lower a per-slot instruction: take
this written element, take it wrapped, or pass None.

`?x` rides in the tree as its own token, both in the parameter list and at the
call, so the rest of the pipeline sees ordinary shapes.

## `[<AutoOpen>]`

An auto-opened module's contents are in scope for everything after it. The
adaptive library leans on this: `HashSet.computeDelta` and `applyDelta` live
in an auto-opened `DifferentiationExtensions.HashSet`, three thousand lines
away from the `HashSet` module that holds `empty`. Without it those names
resolved to the PRELUDE's set operators, which are backed by `HashNode` — so
`Traceable`'s `'State` was bound to a `HashNode` before its first field was
even read, and every field after it looked wrong.

The port script was stripping the attribute; it keeps it now.

## Where it stops now

58 diagnostics over the 39 ported files. An implemented interface is now
recorded under its DECORATED name (`interface IAdaptiveValue<'State> with`
implements IAdaptiveValue`1), so concrete values widen into generic
interfaces again — 77 to 58. The whole occurs-check family — 65
errors — was ONE poisoned alias-table entry (see CLAUDE.md): the abbreviation
`MultiSetMap = HashMap<'k, HashSet<'v>>` re-registered itself under
`HashMap`, and every use of HashMap in the project expanded wrong. The
"statics share the class's parameters" diagnosis recorded here earlier was
WRONG — the untied hovers were this same poison viewed from another angle.

The remaining 58, clustered by cause (line numbers are DISPLACED — these
errors are blamed at parked-dot retry time, so hover the actual expressions,
do not trust the reported line):

* **A reader class where a function is expected** (~14): `ListTreeReader<'a>
  vs AdaptiveToken -> 'a`, `Cache<'a,'b> vs 'a -> 'b`, `IndexMapping<...> vs
  Index -> 'a`. One shared shape — some application path unifies the CLASS
  against a function type instead of calling a member or constructor.
* **A concrete class vs IAdaptiveObject** (~8): widening into an interface
  at a NON-argument position (`AdaptiveOr vs IAdaptiveObject`, the reduce
  classes). unifyArg widens; plain unify does not.
* **`IEnumerable<'a> vs HashSet<'a>`** (4, in the CE builders' YieldFrom):
  NOT the isSeqName decoration — tested, count unchanged. Something else.
* **StructTuple2 vs reference tuple** (4+), **Index vs int** (4, one
  `inherit` line), **MinMax<Index>/Ordered<ReversedCompare>** instances (4),
  slice on MapExt content (1), occurs in AdaptiveFileSystem-adjacent
  Compute overrides (2).

### The plan the user set: `#if FPP`

The reflection/DynamicMethod zoo (ShallowEqualityComparer and friends)
cannot ever compile here — it gets `#if !FPP` guards in the FDA sources
instead of shims. `tests/port-reference.py` already has `pick_branch` with a
defined-set for `#if FABLE_COMPILER`; add FPP to that machinery and guard
the zoo at the source.

### Stage 2 has been measured now

Building the CLEAN PREFIX (13,767 lines through Traceable/Instances.fs, with
a cval/AVal.map/transact smoke test appended) produces the first LOWERING
inventory:

    27  not lowerable: assignment target
     7  not lowerable: for-in (no GetEnumerator on the source)
     2  base-related

The 27 were FIXED in one stroke: they were properties with `inline get/set`
accessors, and `propSetter` looked the setter up only in the RESOLVER's
member index — keyed by plain spelling, while inference's fields table keys
`Inner`2.set_Count` by the decorated owner (and already carries the
definition). propSetter now consults the fields table first, exactly as
`memberAt` does.

Stage 2 on the clean prefix: 36 errors at first contact, now FIVE, and the
smoke test is within sight. Landed this stretch (gates pending as this was
written):

* **Late loop sources get the enumerator protocol**: `for kv in d` over a
  Dictionary whose type settles late (a ctor result) parked nothing and was
  silently unlowerable; finalization now wires GetEnumerator/MoveNext/
  Current at the same synthetic offsets the eager branch uses.
* **`Unchecked.defaultof<T>` pins its written argument** (registers into
  instRaw so the existing pinning grounds it), and a STRUCT default lowers
  as a zeroed ERecord under a `$struct:` marker — UNVERIFIED for POD
  layouts, kept because null trapped anyway.
* **Member-`new` constructors predeclare** in `and` groups (struct-block
  types like MapExtEnumerator have no other constructor), and a SINGLE
  candidate is taken when the ordinary path has no scheme; the chosen-ctor
  arm now records the SPECIALIZATION DEMAND (instRaw) itself — without it
  the stamper dropped the template ("unbound variable Dictionary").
* **A destructuring let types its VALUE first** and hands the pattern
  patExpect — `let (v, _) = kvp.Value` over a struct tuple now reads, as it
  does in a match arm.
* **Prelude Dictionary** gained the comparer ctor (ignored — structural
  hashing; divergence), TryAdd, TryRemove.
* **Port**: VolatileSetData de-structed to a class with a zero ctor;
  ConcurrentDictionary → Dictionary; qualified System.Collections.Generic
  names stripped; comparer-passing create bodies simplified; the private
  rename is now ARITY-AWARE (Traceable<'S,'D> inside a renamed cache class
  stays the record).

ALL FIVE fixed. The "self-host regression" that parked this branch was
nothing of the kind: the leftover `GetEnvironmentVariable` debug toggles in
Infer are not compilable by F++, so the self-compiled compiler STUBBED the
whole `infer` function and trapped on entry. Strip the instrumentation
BEFORE gating — the stub warnings named it all along.

The TryGetValue mystery was the OUT-VIEW choice: a still-variable argument
fits the full byref signature in a trial, so the full signature swallowed
the variable (`v := 'k * ByRefCell<'v>`). F#'s rule is syntactic — one
written element means the view, the full count means the .NET signature —
so `dotDemand` now carries the written ARGUMENT COUNT and the choice reads
it. The MapExt owner in the hover was a red herring (the bare-name display
of a poisoned binding, not the actual resolution).

The smoke test: cval → AVal.map → force → transact → force, appended to the
port prefix cut at Traceable/History.fs. `smoke.fpp` is rebuilt from
adaptive.fpp by the recipe in the session notes; group.fsx/ms.fsx in the
scratchpad are the measurement and hover probes.

## THE FULL LIBRARY COMPILES AND LOADS

All 38 files (everything but AdaptiveFileSystem and the aset{}/alist{}
builder sugar in ComputationExpressions.fs) compile with ZERO errors, every
initializer runs, and the aval smoke stays green. The error count went
68 -> 0 in one sitting; each fix was a mechanism:

* **Nominal subsumption lives in the UNIFIER.** A subsumeHook installed by
  inference answers TCon mismatches: it returns the class's DECLARED
  interface instantiation (implTys, threaded through Workspace like bases)
  substituted at the receiver's arguments, and unifySeen unifies the pair
  itself so trials stay undoable. `HashSetDelta<'a>` widening into
  `IEnumerable<'x>` binds 'x to SetOperation<'a> — what the class actually
  enumerates — where a name-only rule bound it to 'a and manufactured
  "SetOperation would contain itself". Arity-mismatched entries are OTHER
  classes sharing a bare name and are skipped: substituting nothing and
  unifying raw parameter variables corrupted every later use.
* **Exact overloads outrank declaration order.** unifyTrialScore counts the
  bindings a fit needs; a zero-binding parameter fit (IndexOf(Index) for an
  Index argument) wins, anything less exact keeps the old first-fit rule.
  Picking the generic member bound the receiver's class parameter GLOBALLY.
* **Numeric defaulting never touches declaration-level variables.** A
  leftover constraint whose argument is a level-0 var is some class's
  parameter; defaulting it took MapExt's 'Key to int for the whole project.
  The constraint drops instead — stamping resolves it per instantiation.
* **Stored types freshen COMPLETELY at use.** Every site that unifies a
  fields/bases/implTys tree now freshens all leftover free variables, not
  just Params+Quantified — leaked foreign variables were landmines.
* **Overloaded accessor properties register decorated** (registerField, not
  a raw dictSet): the second `Item` overwrote the first and the wrong index
  type always won.
* **`stillNamed` finally guards the template drop** (the comment always
  promised it): a secondary constructor names its primary symbolically from
  inside a template, and dropping the primary unbound History.
* Port: extent-scoped .Invoke rewriting (adapted closures only — `x.Invoke`
  and `cache.Invoke` are real members; parameters typed FSharpFunc anchor
  at their declaring line), file-scoped renames for non-private colliding
  reader types, `type X with` augmentations excluded from renaming,
  MutableHashSet grew a real enumerator, MapExt KeyValue enumerations go
  through ToSeq, dotless indexers get their dot, `override
  Compute(token, dirty)` states its dirty-set type, LevelChanged guards use
  annotated helpers, and one ctor-with-property-initializers writes its
  fields out loud.

The remaining frontier is RUNTIME tails of the collection smoke (a $tup3
cast in the alist applyDelta path) and the parked builder sugar. The
`cval`/`cset`-style ABBREVIATION constructors still don't resolve
(ctor-through-abbreviation); the smoke uses the class names.

## THE SMOKE TEST RUNS: 2, then 42

`let c = cval 1` / `AVal.map (fun v -> v * 2) c` / `force` prints 2;
`transact (fun () -> c.Value <- 21)`; `force` prints 42. Construction,
evaluation, caching, transactions, level-ordered invalidation, and
recomputation of FSharp.Data.Adaptive all execute in F++-compiled wasm-GC.
Every fix on the way was a REAL mechanism, in dependency order:

* **Interface identity is ONE name.** `interface aval<'T> with`,
  `interface IAdaptiveValue<'T> with` and the declaration IAdaptiveValue`1
  spelled three vtable keys for one slot. ifaceNameOf resolves
  abbreviations (aliases threaded into Lower), ifaceKeyOf appends the
  arity, and the emitter's slot table strips it — every spelling, one slot.
* **Interface property SETTERS exist.** Accessor lifting now surfaces
  `set_P` beside `P`; `x.Level <- v` on an interface receiver dispatches
  through the vtable like the read does.
* **Static properties are reads, not closures.** `T.P` where P's scheme is
  a value type applies the lifted accessor (fields table tells properties
  from methods); `T.M args` no longer double-applies the synthesized unit.
* **A stamped constructor stands for its class.** DCE parks class members
  on the ctor and only the stamps were ever called — members park on every
  stamped clone too. And a class whose only contribution is an OVERRIDE
  (MapVal.Compute) now gets the instantiation-subclass treatment; the
  base-field copy casts to the ancestor that declares the slot.
* **Class `let mutable` is ONE storage.** The instance field held a
  snapshot while the class body's closures mutated a cell — the TransactQueue
  counted into the cell and Commit read the field, so the commit loop never
  ran. The field now holds the CELL ($forcecell/$cellof/$cellget/$cellset)
  and members read and write through it.
* **One layout, one name.** The canonical template built
  `StructTuple2$<int.#v>` as a boxed tuple while the concrete consumer cast
  `StructTuple2$<int.IAdaptiveObject>` — canonRecordNames collapses every
  reference argument to `obj` at emit entry, so both sides name one wasm
  type. Uniform struct tuples emit as $tupN.
* **Array.zeroCreate of a class element is NULL-filled** — the i31 zero
  made `isNull` false and the first traversal a cast failure.
* **Object expressions capture same-file locals only** (a prelude class
  member "capture" smuggled an uncallable EVar into the env), their members
  share the interface's type-variable scope (a dangling 'a defaulted to int
  and bound `compare` to the wrong instance), and nested
  `Case (struct (a, b)) when guard` binds its elements in the GUARD too.
* **Dot-resolution hops through implemented interfaces** for extension
  members (`x.MarkOutdated()` on a class whose extension sits on
  IAdaptiveObject) — the silent by-name field fallback typed fine and
  emitted an unknown field.
* Port: LevelChangedException rides in `Failure "!level:N"` (helpers decode
  it — string methods on a catch binder don't resolve), `static val
  mutable` becomes `static let mutable` with ValueNone/defaultof inits and
  bare self-references, module-level generic values are thunked like the
  class statics, `List<...>` is spelled ResizeArray, RuntimeHelpers
  identity-hash is `hash`, and a module-nested type colliding with a later
  top-level one is renamed (two AbstractVals were one merged class).

Next: the FULL adaptive.fpp (History/ASet/AMap...), then the actual test
suite. The gates on this batch had one lesson mid-stream: the new stamp
registry's dense offsets collided with the lowerer's synthetic-offset
families (7e6 `_fmt`) — bases must be disjoint; it now sits at 5e8.

## The smoke test REACHED THE ADAPTIVE MACHINERY

`ChangeableValue 1 |> AVal.map |> force` now compiles clean, every library
initializer runs, and execution reaches `AVal.force` — where it dies on a
CAST FAILURE in the interface dispatch (`value.GetValue AdaptiveToken.Top`
on an `IAdaptiveValue`1` receiver). That is the next session's single
target, and it is the first REAL adaptive-machinery bug: everything before
it is now infrastructure that works.

What landed to get here (gates pending as this was written):

* **`sizeof<'T>` is a real constant** — typed int in inference, carried as
  `$sizeof:name` through lowering, substituted per stamp in Link (like
  `$class:`), resolved in the emitter against the SAME tables layouts come
  from. `sizeof<int>`=4, a two-field POD struct=16, and a generic
  instantiation resolves right.
* **A generic value has NO eager initializer.** `let empty<'K,'V> = ...` as
  a startup init ran the template at UNRESOLVED arguments and trapped in
  whatever class-constrained call it reached. Templates are skipped; stamps
  carry their own bodies.
* **Stamp identity is a REGISTRY, not a hash.** offset+hash(mangled)%1e6
  collided at a few thousand stamps — one clone reading another's
  signature: a zip crash where arities differed, INVALID WASM where they
  agreed. First-come sequential offsets, deterministic.
* **A divergence cap in the stamper**: poisoned schemes (the shared-var
  hazard) hand the vtable machinery instantiations that DOUBLE each round
  (IndexList<T> -> IndexList<StructTuple2<T,T>> -> ...); nesting deeper
  than any real program writes degrades to the uniform representation with
  one warning. The OOM this fixed burned 40 minutes before the stamp trace
  named it.
* **The out-parameter view chooses by WRITTEN argument count** (F#'s own
  rule) — a still-variable argument fits the full byref signature in a
  trial, and the full signature then swallowed the variable.
* **`box`/`unbox` are identities BY NAME** wherever they resolved (the
  prelude declares `extern let unbox`), including piped (`|> unbox<T>`).
* **Port**: Equality.fs replaced by an honest shim (structural hash/=, the
  provider indirection kept); thunked generic-class statics
  (defaultComparer/empty families) with extent-scoped read rewriting;
  IsValueType/IsAssignableFrom/GenericZero/static-val spot-fixes — each a
  documented divergence.

The debug-loop lesson worth keeping: the "self-host regression" that parked
this branch was MY OWN `GetEnvironmentVariable` debug toggles — F++ cannot
compile them, so the self-hosted compiler stubbed the whole `infer` function
and trapped on entry. The stub warnings named it all along. STRIP
INSTRUMENTATION BEFORE GATING.

Known deliberate gaps, all banked: constructor-through-abbreviation
(`cval 1` — the smoke writes ChangeableValue for now), `Item5`+ tuple
fields, exceptions-as-types (NotSupportedException etc. stub), the
poisoned-scheme root cause behind the divergence cap.

## Compiling is not the same as running

The port has only ever been INFERRED. Lowering and emission are a separate
pass with their own failure class, and there is one known instance: a generic
class implementing a non-generic interface type-checks and then traps
(`unbound variable Accept`). How big that stage is has NOT been measured.
The cheap measurement is a twenty-line smoke test — build a cval, map it,
transact, read it back — which exercises the machinery end to end without
needing the 6,667-line test suite.

That suite needs NUnit, FsUnit and FsCheck. FsCheck's generators are
reflection-driven, so it is a hand-written harness or nothing; there is
precedent in this repo for exactly that.
