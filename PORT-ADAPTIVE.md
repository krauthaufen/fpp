# Porting FSharp.Data.Adaptive, whole

> `STATUS.md` is the wider picture — gate state, everything closed so far,
> and every known defect. This file is the port's own detail.

The quest: `FSharp.Data.Adaptive` compiles as F++ — all 41 files, 24,792
lines of it — with **the heart untouched**. The algorithms, the data
structures and the adaptive machinery are the library's; what may be
replaced is what depends on a runtime service F++ does not have, and each
replacement has to be a real construct, not a stub that lies.

## The rule, and why the Fable branch is not it

The library targets Fable as well as .NET, and that branch is tempting: no
reflection, no threading, no weak references. It is **not** what this port
takes. Fable's `WeakReference` never dies, its `Monitor` is a no-op, and its
`ShallowEqualityComparer` is plain reference equality for every type. Those
are changes to the semantics of the heart, which is the one thing that must
survive. The port takes the **.NET branch** and answers what it asks for.

## Running it

```bash
python3 tests/port-adaptive.py \
    ~/projects/FSharp.Data.Adaptive/src/FSharp.Data.Adaptive /tmp/adaptive.fpp
dotnet run -c Release --project src/Fpp.Cli -- check /tmp/adaptive.fpp
```

The driver reads the compile order from the `.fsproj`, so it ports what the
library itself says is the library, in the order the library says.

## Where it stands: DONE, and running

The port compiles whole and RUNS: `tests/adaptive-suite/Tests.fpp` holds
**100 tests, all green under wasmtime** — every portable plain test from
every reference test file (AVal, ASet, AMap, AList, History, Transaction,
Callbacks, WeakOutputSet, CollectionExtensions, AdaptifyHelpers-adjacent,
IndexMapping, MapExt), four deterministic reference-implementation property
harnesses standing in for the FsCheck suites (seeded random expression DAGs
diffed against naive-recompute models over hundreds of transactions), the
aval/aset/alist computation-expression builders, and derived-`Arb`
generation. The reference tests NOT ported are the ones that cannot mean
anything here: GC-memory metering (`History weak`, the AddCallback GC
pair) and the real-threads async test.

Run it:

```bash
python3 tests/port-adaptive.py \
    ~/projects/FSharp.Data.Adaptive/src/FSharp.Data.Adaptive /tmp/lib.fpp
cat /tmp/lib.fpp tests/adaptive-suite/Tests.fpp > /tmp/suite.fpp
dotnet run -c Release --project src/Fpp.Cli -- build -o /tmp/suite.wasm /tmp/suite.fpp
~/.wasmtime/bin/wasmtime -W function-references,gc /tmp/suite.wasm
# PASSED 100 FAILED 0
```

The sections below are kept as the record of how the frontier moved and
what each closure cost; the numbers in them are historical.

## What is replaced, and what it became

**`ShallowEquality.fs` → `tests/adaptive-shims/ShallowEquality.fpp`.** The
only file replaced outright, and the reason the quest needs replacing at
all. The original decides per type, at run time, which comparison a type
gets, and emits it as IL through `DynamicMethod` — 400 lines of it. But the
DECISION is a compile-time one, and a typeclass with overlapping instances
is that decision written in the language:

| the original | the port |
| --- | --- |
| `isUnmanaged` (enums, blittable structs) → value comparison | an instance per primitive |
| other value types → field-wise, one level, each field by its own comparer | an instance per struct type |
| reference types → `Object.ReferenceEquals` | the general instance |

The more specific instance wins, so adding a type is one declaration. Note
what is NOT there: `string` has no instance, because in .NET a string is a
reference type and the original compares it by identity too.

`ShallowEqualityComparer<'T>.Instance` and `.ShallowEquals(a, b)` are
rewritten onto three constrained functions — a type with class-constrained
statics is not expressible yet. Eight call sites, in three files.

## The frontier: what the compiler still owes

Both of these are F# the library actually writes, so they are compiler work,
not port work.

* ~~**Multi-case active patterns**~~ — **done.** `let (|Add|Rem|) d = ...`
  compiles to a function returning an `ActiveChoice`, with the cases
  rewritten onto its constructors in the body and onto its case patterns at
  every use, where the scrutinee goes through the function first. The
  rewrite fires only when EVERY clause head belongs to one active pattern,
  so an ordinary union case that merely shares a name keeps its meaning.
  Partial patterns (`(|Foo|_|)`) are not built — the library has none.
* ~~**The verbose class syntax**~~ — **done.** `type X = class ... end`,
  and the same for `struct` and `interface`; the keywords are delimiters and
  what is between them is the ordinary body. `interface` is ambiguous — it
  also opens an interface IMPLEMENTATION as the first thing in a body — and
  a type name after it is what tells them apart.
* ~~**Intrinsic type extensions**~~ — **done.** `type X with member ...`
  adds members to a type declared elsewhere: no representation, no
  constructor, no vtable slot, just functions of the receiver resolved by
  its type. The 19 in the library are mostly on INTERFACES
  (`IAdaptiveValue`, `IOpReader`, `IAdaptiveHashSet`, `IAdaptiveObject` ×3),
  which is how the library hangs a fluent API off them, and that works. Two
  traps: the extension must not re-define the type's NAME (it shadowed the
  real declaration, and with it the constructor), and it declares neither a
  record nor a class.
* ~~`sprintf` with several specifiers including `%A`~~ — this was not the
  format at all. `sprintf "Rem%d(%A)" -cnt value` passes `-cnt`, and F#'s
  ADJACENT-PREFIX rule is what says so: a `-` with whitespace before and
  none after negates what follows, where `a - b` subtracts. F++ had the rule
  for numeric literals only, so `-cnt` parsed as subtraction. Fixed.

## The work list beyond the frontier

Counted across the .NET branch of the whole library, so the numbers are what
is actually coming:

| what | hits | the answer |
| --- | --- | --- |
| ~~`uint64`, `int16`, `uint16`~~ | — | **done.** New primitive types, and the missing halves of `byte`/`sbyte`'s tower with them. uint64 is unsigned on the i64 rail (`div_u`, `lt_u`, `shr_u`); int16/uint16 are int-shaped like byte/sbyte, narrowed by the conversion. Pinned against .NET in `stdlib/dotnet.fpp` |
| ~~`lock` / `Monitor`~~ | 90 | **done.** Real types in the prelude; one thread enters and exits every lock, which is the honest implementation, not a stub |
| ~~`Interlocked`~~ | 13 | **done.** Increment/Decrement/Exchange/CompareExchange, each taking its location by reference and returning what .NET returns |
| ~~`WeakReference`~~ | 34 | **done.** A strong `WeakReference<'a>` in the prelude: reading through one is identical, and what changes — a graph that relied on weakness to drop its dead half keeps it — is written down in DIVERGENCES.md |
| ~~`ConditionalWeakTable`~~ | 3 | **done.** An identity-keyed table in the prelude. The library's use is a per-object callback cache with an explicit `Remove`, so the behaviour is the same until something dies with callbacks attached |
| ~~byref `TryGetValue`~~ | — | **done.** F# hands the out-parameter over as a tuple, which IS expressible |
| reflection outside ShallowEquality (`typeof<>` in AdaptiveValue, HashSet, HashMap, IndexList, History, Cache) | ~30 | read each: most are `typeof<'a>` used as a cache key or a null test, which a typeclass or a constrained function answers |
| ~~`IDisposable` / `use`~~ | 25 | **done.** Disposal at the end of the scope, on the normal path and the raising one, over a real `try`/`finally`. `IEnumerator<'a>` inherits `Dispose` the way .NET's does, which is what `use e = xs.GetEnumerator()` needs |
| ~~computation expressions~~ | 2 files | **done.** `builder { ... }` is rewritten into builder-method calls between parsing and resolution, so resolve, infer and lower share ONE tree. What running that early cannot do is ask whether the builder defines `Run` or `Delay`, so those are emitted structurally — DIVERGENCES.md has the rule. `ComputationExpressions.fs` itself is still stopped by flexible types |
| flexible types in a member's parameters | — | `member x.For(elements : aval<#seq<'T1>>, ...)`. `#T` parses elsewhere and not here |
| `do base.M()` in a class body | 4 files | AdaptiveObject, Core, Transaction, Callbacks |
| the harness mangles a tupled member | 2 files | `port_closures` rewrites `member x.Invoke(a : T, b : U)` into `member (x (a : T) (b : U))` and loses the name — the DRIVER's bug, not the compiler's |
| `inherit` (119) | — | already works |

## The two harnesses, and which one to reach for

`tests/port-reference.py` ports **one** file (HashCollections) and is what
the acceptance test in `LibraryTests.fs` runs — it stays as it is, green.
`tests/port-adaptive.py` ports the **whole library** and reuses every rule
of the first. Rules belong in the first when they are about .NET in general,
in the second when they are about this port.
