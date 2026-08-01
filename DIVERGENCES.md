# Deliberate divergences from F#

F++ inherits F#'s semantics. Every departure is a decision, not an
accident, and each one is listed here with the reason it was taken.

Two rules keep this honest:

1. **The oracle cannot arbitrate a divergence.** The conformance gate runs
   each program under `dotnet fsi` and under `fpp`+wasmtime and diffs the
   output. For anything on this list that diff legitimately fails, so the
   gate is silent exactly where we most need a check. Every entry therefore
   needs its own test asserting *our* behaviour directly, never a diff
   against F#.
2. **This list stays short.** A divergence is a cost paid by everyone who
   knows F# and expects it to mean what it says. If an entry cannot carry a
   reason that survives being read aloud, it should not be here.

---

## Arrays are compared by reference

F#: `[| 1; 2 |] = [| 1; 2 |]` is `true` — arrays compare structurally.
F++: it is `false`. Arrays are equal only to themselves.

**Reason.** An array is inherently mutable: its contents may change while
its identity stays the same. Structural equality on such a value is not a
property of the value, it is a property of a moment in time — two arrays
equal now may be unequal after any write, with no assignment to either
name. Identity is the only thing about an array that is stable, so identity
is what equality reports.

**Second reason: cost.** Arrays are the container people reach for when
there are many elements, and `=` is the one operator nobody reads as
expensive. Structural comparison hides an O(n) walk — over the whole
buffer, per comparison — behind a symbol that looks free, in exactly the
data structure most likely to be large. Reference equality is O(1) and
honest; anyone who wants element-wise comparison can ask for it by name.

The same argument decides hashing, and more sharply: a structural hash of a
mutable buffer is incoherent as a hash key, because the hash moves under
mutation while the object remains the same object. Anything holding it in a
hash container silently loses it.

`hash` on an array is therefore its LENGTH — stable, cheap, and unchanged
by writes to elements. That is a legal hash for identity equality (the only
obligation is that equal values hash equally), and it is deliberately not a
good one: arrays are not meant to be hash keys. Anything that wants to key
on array contents passes an `IEqualityComparer` that says so.

This also matches what an array *is* in F++ — a buffer whose purpose is to
be handed to C or JS by address, and which can be mutated through a pinned
pointer while the GC-side value looks untouched. See REPRESENTATION.md.

**Status: true today, but by accident.** The runtime equality walk has no
array case and falls through to `ref.eq`. When per-type `equals`/`hash` are
generated (see DESIGN.md, "Identity"), arrays must be given identity
equality *explicitly* — the natural implementation of "structural equality,
recursing into components" would quietly make them structural and break
this.

---

## The transcendental functions are ours, and not bit-identical to .NET

F#: `exp`, `log`, `sin`, `cos`, `tan`, `sinh`, `cosh`, `tanh`, `asin`,
`acos`, `atan`, `atan2` and `**` come from the platform's libm, and .NET
publishes their results as the answer.
F++: they are implemented in F++ itself, in the prelude, and agree with
.NET to about 1e-15 relative — not to the last bit.

**Reason: there is nothing to call.** wasm has `sqrt`, `abs` and `trunc` as
instructions and stops there. There is no libm beneath a wasm module, and
no host function to import that would not put a foreign dependency at the
bottom of the language. So these functions are not a binding to an
implementation; they *are* the implementation, and the accuracy is whatever
we write.

What that costs, precisely:

- `exp` and `log` reduce against a two-word split of ln2 and use a Taylor
  series; `sin` and `cos` reduce against a three-word split of pi/2. The
  reduction degrades for arguments past roughly 1e8, where three words of
  pi/2 stop being enough. .NET stays accurate much further out.
- `pow` is exact for integer exponents up to 2^1024 (repeated squaring, so
  `(-2.0) ** 3.0` is exactly `-8`), and goes through `exp (b * log a)`
  otherwise, which loses a few more bits than a dedicated `pow`.
- `sqrt`, `abs` and `truncate` ARE the machine instructions, so those are
  bit-identical.

**Consequence for the gate.** The oracle diffs stdout byte-for-byte, so it
cannot arbitrate these: the last digit legitimately differs. They are
tested against F# to a tolerance instead ("the math surface" in
ClassTests), which is the honest check — and `sqrt`/`abs`/`truncate`, being
exact, stay eligible for the oracle.

**Not a divergence:** `%` on floats. F# defines it as the truncated
remainder and so do we (`a - b * truncate (a / b)`), even though wasm has no
instruction for it. `min`/`max` likewise use F#'s own definition,
`if a < b then a else b`.

## Members on `string` are a fixed builtin set, not extension members

A string is a primitive — an array of bytes with no class to hang members
on — so `s.Substring 2` cannot resolve the way a member on a declared type
does. The set F# code actually uses is registered as builtin members instead
and emitted through the `$str` primitives: `Substring` (1 and 2 argument),
`StartsWith`, `EndsWith`, `Contains`, `IndexOf` (char, string, and string
from an index), `LastIndexOf`, `Split` (char), `Replace`, `Trim` and
`TrimEnd`.

**Reason.** The alternative was to rewrite every call site onto seam
functions (`startsWith s p`), and that moves the codebase AWAY from F#
compatibility for the compiler's convenience. The member surface is the F#
surface; the fix belongs in the compiler.

**The divergence.** The set is CLOSED. `s.ToUpper()` or `s.PadLeft 3` do not
resolve, and neither does a user-defined extension member on `string` or on
any other builtin — general extension members remain an open language
feature. The bounded set was derived from what the compiler's own sources
call; growing it is a one-line registration plus a primitive, deliberately
so.

**Where they agree exactly.** Semantics are .NET's, pinned by oracle tests
on the cases where a hand-rolled implementation would drift: an empty needle
is found at index 0, a missing one gives -1, `Split` keeps trailing empty
pieces (`"a,b,"` gives three), and `Replace` scans left to right without
letting replacements overlap (`"aaa".Replace("aa", "b")` is `"ba"`, not
`"b"`). `Trim` trims ASCII whitespace; the full Unicode set is not
implemented.

## `IsSome`, `IsNone` and `Value` on `option` are builtin members

`o.IsSome`, `o.IsNone` and `o.Value` resolve, and mean exactly what F# means
by them. They are not declared on the prelude's `Option` type, though:
they are registered as builtin members the way the `string` surface is, and
lower to the `match` they stand for.

**Reason: cost, not semantics.** A member on a generic DU is stamped per
instantiation, and `option` is instantiated at very nearly every type in the
compiler. All three are properties of the TAG — identical code at every
element type — so a copy per element type is pure waste. Declaring them on
`Option` compiles and behaves the same; it just pays for something nobody
uses.

**The divergence.** As with `string`, the set is CLOSED: `o.IsValueNone` or
a user-defined extension member on `option` do not resolve. `Option` itself
carries no other members, and general extension members on builtins remain an
open language feature.

## There is no `Array.empty`

F# exposes it as a VALUE. It is absent here because a generic *value* is not
stamped per instantiation: it would be initialized once, at the canonical
(uniform) representation, and an `int[]`'s elements are a PACKED `$parr_i`,
so code stamped at int casts to that type and a uniform empty array traps.

`List.empty`, `Seq.empty` and `Set.empty` ARE values: lists, seqs and (since
Set became an AVL tree) sets carry no packed array, so there is nothing to
get wrong. `Set.empty` used to take unit for exactly this reason and no
longer does.

Lifting this means monomorphizing generic value bindings (cloning the global
per instantiation), the same treatment functions already get.

## Fixed while porting the FsCheck-style property tests

These were REAL divergences from F#, found by property testing the collections
against ordered reference models, and are fixed:

* **Collection equality was structural over the TREE, not the content.**
  `Map.ofList [(1,1);(2,2);(3,3)] = Map.ofList [(3,3);(2,2);(1,1)]` was `false`
  (F#: `true`) because derived equality compared AVL shape, and insertion order
  changes the rotations. Map and Set now declare `Equals`/`GetHashCode` over
  their in-order contents. HashMap/HashSet are CLASSES, where `=` was identity
  — an even worse trap — so `HashNode` declares content equality too
  (count plus an entry-wise lookup, and an order-independent hash).
  Equality on a Map/Set now costs a list of its entries; correctness first.
* **`List.init` applied its generator in DESCENDING index order** (F# is
  ascending). Invisible for pure generators, but the compiler's own vtable
  builder appends to a vector inside the generator, so its adapter functions
  came out reversed — a self-hosting divergence that only the byte fixpoint
  caught. `String.init` had the same bug. Both are ascending now.

## Known, and not divergences the tests can see

* A user type whose name matches a PRELUDE type does not shadow it cleanly: the
  program miscompiles (traps) instead of either shadowing or erroring. This is
  why the property-testing RNG is called `PropRng` rather than `Rng` and its
  helpers live inside `Gen` — two existing tests declare their own `type Rng`.
* **A `let` binding shadows a builtin conversion inside its own body.** In
  `let string : Gen<string> = ... string x ...` the inner `string` resolved to
  the binding being defined rather than to the conversion, so the code applied a
  record as a function and TRAPPED at run time instead of failing to compile.
  F# resolves the builtin there (the binding is not recursive). The prelude now
  routes those conversions through `genShowInt`/`genCharOf`/... — but the
  underlying resolution difference is unfixed, and it is silent.

## `.[ ]` needs an `Item` member, and there are no other indexers

`recv.[i]` binds a member named `Item` on the receiver's type, and
`recv.[i] <- v` binds `set_Item` — the .NET indexer, spelled the way F#
spells it (`member x.Item with get i = ... and set i v = ...`). That is the
whole of it: a two-dimensional index (`m.[i, j]`), a slice (`xs.[1..3]`) and
F#'s `GetSlice` do not resolve.

**Where it used to go wrong.** An index on a type that had no indexer was
lowered as an unnamed ARRAY read, which compiles to a cast that fails at run
time. That is now a compile error naming the type — but only for a type this
compilation has seen the members of, which is what keeps the dogfooding gate
(every source typed with NOTHING resolved) from calling `JsonNode.[…]` an
error.

## A generic class reached through an INTERFACE cannot depend on its layout

A member reachable through a vtable keeps the canonical all-anyref
signature — that is the dispatch contract — so it is never specialized. A
member called directly IS specialized. When the two disagree, the interface
one loses:

```fsharp
type Arr<'a>(items : 'a[]) =
    interface IEnumerator<'a> with
        member _.Current = items.[0]     // reads `items` at the UNIFORM
                                          // representation
let e = Arr<int>([| 5; 6 |]) :> IEnumerator<int>
e.Current                                 // traps: the field holds a PACKED
                                          // int array
```

Constructing it is fine, calling the member directly is fine, and at a
reference element type (`Arr<string>`) even the interface call is fine. It
is the combination — an interface method reading a field whose layout
depends on a type parameter — that has no correct answer today.

**Why the prelude's own collections dodge it.** `ResizeArray`, `Dictionary`
and `MutableHashSet` hold their elements in a packed `'a[]`, so none of them
implements `IEnumerable<'a>`. They carry a plain `GetEnumerator` member
instead, which is what `for x in xs` looks for (the loop is structural, as
in F#), and hand back the BUILT-IN array iterator over a snapshot. So
`for x in ra` works at every element type, and `Seq.map f ra` does not
compile — go through `ra.ToArray ()`. A compile error is the honest failure
here; the alternative was a runtime trap that only appeared at packed
element types.

Lifting this means monomorphizing the CLASS, not just its members: a
per-instantiation descriptor whose vtable names the stamped bodies.

## The .NET collections carry no byref members

`TryGetValue`, `TryPop`, `Remove(item, out removed)` and every other method
whose .NET signature needs a byref out-parameter are absent — F++ has no
byref. Use `ContainsKey` and the indexer.

`StringBuilder.Append` takes a string or a char; .NET's numeric overloads
are not there, so write `sb.Append (string x)`.

`ResizeArray` and `Dictionary` construct with no arguments only:
`Dictionary()`, not `Dictionary(capacity)` or `Dictionary(comparer)`.
Equality and hashing are always the structural `=` and `hash`, never an
`IEqualityComparer`.

The mutable set is called `MutableHashSet`, not `HashSet`. Its MEMBERS are
.NET's exactly — `Add` answers whether the element was new, `Remove` whether
it was there, plus `Contains`/`Count`/`Clear`/`UnionWith`/`ExceptWith`/
`IsSubsetOf`/`Overlaps` — only the type's name differs. `HashSet` is taken
twice over: by this prelude's own immutable one and by
FSharp.Data.Adaptive's, which the acceptance corpus ports. A user type whose
name matches a prelude type MERGES with it rather than shadowing it (below),
so claiming the .NET name would break every program that declares its own.

**Where they agree exactly.** Enumeration is INSERTION-ORDERED, like .NET's
in practice; `Add` on a duplicate key throws where `d.[k] <- v` overwrites;
`HashSet.Add` answers whether the element was new; `ResizeArray.Remove`
removes the first occurrence and answers whether it found one;
`StringBuilder.Length` counts characters, not chunks. All of that is pinned
by `stdlib/dotnet.fpp`, which runs under both compilers and must print the
same 93 values.
