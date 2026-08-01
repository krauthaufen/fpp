# Porting FSharp.Data.Adaptive, whole

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

## How much is actually left — measured, not guessed

The first-error frontier is pessimistic: it stops at the first problem and
says nothing about the 14,000 lines behind it. Parsing each of the 40 files
ON ITS OWN answers the real question, because a parse error is a missing
SYNTAX feature while a type error mostly needs cross-file context:

    27 of 40 files parse clean
    13 have a parse error, and the error counts are cascades —
       one construct produces hundreds of "unexpected token"

The distinct blockers behind those 13 are a short list, and the biggest one
was not a language feature at all: SIX files were stopped by `#nowarn
"7331"`, a compiler directive. Skipping directives took ten lines and made
four more files parse clean on the spot.

That is the shape of this work. The remaining constructs are ordinary F#
that any project would use — type extensions on DOTTED names
(`type System.Threading.Interlocked with`), computation expressions,
`use`/`IDisposable` — not exotica. Nothing so far has needed a
FSharp.Data.Adaptive-specific hack, and every fix has been small and
general.

## Where it stands

The port parses and type-checks from line 1 to **8027 of 22,635** — through
`ShallowEquality`, `Equality`, `FableHelpers`, all 4,500 lines of
`HashCollections.fs`, `Operations`, `Deltas`, `Index.fs`, all 3,908 lines
of `MapExt.fs`, and into `IndexList.fs`. Everything past the frontier is unknown, not known-bad: the
errors after the first are a cascade until the first is fixed.

The frontier is inside `IndexList.fs`. Two things are known to be waiting
there and beyond:

* **`&x` on a mutable LOCATION.** `&x` parses and types, and FORWARDING a
  byref parameter to another (`x.TryGetValue(key, &value)`) hands the same
  cell on, which is the whole of what MapExt needs. Taking the address of a
  mutable field or local (`Interlocked.Increment(&currentId)`,
  `weak.TryGetTarget(&old)`) still needs copy-in/copy-out around the call,
  or promotion of that storage to a cell.
* **Inline type-parameter constraints as TYPECLASSES.** `'Key : comparison`
  parses, stays in the tree and no longer counts as a type parameter — but
  it is still inert, and so — as it turns out — is the F++ spelling. A type
  declaration now PARSES `when C<'a>`, but nothing reads it: `Box<Opaque>`
  is accepted where `Opaque` has no `Ordered` instance. Inference still
  derives what a member's body needs, which is what made an early test look
  like it worked. So the order is: make a type-level constraint BIND (a
  given for the members, and a check at every instantiation), then translate
  the F# spelling onto it:

  | F# | F++ |
  | --- | --- |
  | `'a : comparison` | `Ordered<'a>` |
  | `'a : equality` | structural `=`, which is builtin — nothing to add |
  | `'a : unmanaged` | the one worth most: exactly the POD/blittable
    property the layout machinery already computes for struct arrays and
    C-compatible layout. As a class it would let USER code demand it, which
    is what a zero-copy `Buffer<'t>` needs |
  | `'a : struct` / `not struct` | the value-vs-reference split
    `ShallowEquality` wants too |

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
| `lock` / `Monitor` (58 + 32) | 90 | real types in the prelude; a single-threaded runtime enters and exits every lock, which is the honest implementation, not a stub |
| `Interlocked` | 13 | same — the increment is atomic when there is one thread |
| ~~`WeakReference`~~ | 34 | **done.** A strong `WeakReference<'a>` in the prelude: reading through one is identical, and what changes — a graph that relied on weakness to drop its dead half keeps it — is written down in DIVERGENCES.md |
| ~~`ConditionalWeakTable`~~ | 3 | **done.** An identity-keyed table in the prelude. The library's use is a per-object callback cache with an explicit `Remove`, so the behaviour is the same until something dies with callbacks attached |
| ~~byref `TryGetValue`~~ | — | **done.** F# hands the out-parameter over as a tuple, which IS expressible |
| reflection outside ShallowEquality (`typeof<>` in AdaptiveValue, HashSet, HashMap, IndexList, History, Cache) | ~30 | read each: most are `typeof<'a>` used as a cache key or a null test, which a typeclass or a constrained function answers |
| `IDisposable` / `use` | 25 | `use` is scoped disposal; F++ has neither yet |
| computation expressions (`ComputationExpressions.fs`, `seq { }`) | 2 files | builders |
| `inherit` (119) | — | already works |

## The two harnesses, and which one to reach for

`tests/port-reference.py` ports **one** file (HashCollections) and is what
the acceptance test in `LibraryTests.fs` runs — it stays as it is, green.
`tests/port-adaptive.py` ports the **whole library** and reuses every rule
of the first. Rules belong in the first when they are about .NET in general,
in the second when they are about this port.
