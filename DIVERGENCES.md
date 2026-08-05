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
any other builtin. `type X with member ...` DOES work for a declared type or
interface (see below); what stays out of reach is extending a BUILTIN. The bounded set was derived from what the compiler's own sources
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

## A generic class implementing an interface is monomorphized

A member reached through a vtable keeps the canonical all-anyref signature —
that IS the dispatch contract — so it is never specialized, and it would read
a `'a[]` field at the uniform representation while a `C<int>` holds a PACKED
array. One class, one descriptor, one vtable, shared by every instantiation:
the cast failed at run time, at packed element types only, with no
diagnostic.

So each instantiation of a class that implements an interface becomes a
SUBCLASS of it. The stamped constructor allocates `C$<int>`, whose vtable
slots name the members stamped at `int`; the fields, their order and every
read that casts to `C` are inherited unchanged, and `:? C` still answers true
because the chain says so. A class whose vtable members depend on the layout
drags its constructor into stamping with them, however plain the constructor
looks — the constructor is what allocates, and allocating is what picks the
vtable.

**The cost.** One extra descriptor and one wasm struct type per (class,
element type) that is actually constructed, and the interface members are
stamped rather than shared. Classes that implement no interface are
untouched.

**What is still not covered.** A generic class constructed INSIDE another
generic class' member — the .NET shape where a collection hands out its own
`Enumerator<'a>` — canonicalizes the inner instantiation and traps the same
way. The member's own quantified variable is not the one the class is
generic in, so the demand carries a variable the substitution does not know.
Repro in `tests/known-issues/`. The prelude's collections do not hit it: they
snapshot into an array and hand back the built-in array iterator.

## F#'s constraint spellings ARE typeclasses

`type Box<'a> when Ordered<'a> = ...` and F#'s own
`type Box<'a when 'a : comparison>` mean the same thing and are both
enforced: the constraint travels on the type's CONSTRUCTOR, so building a
`Box<Opaque>` wants `Ordered<Opaque>` the way any other call would and is
rejected by name.

| F# | the class |
| --- | --- |
| `'a : comparison` | `Ordered<'a>` |
| `'a : unmanaged` | `Unmanaged<'a>` |
| `'a : equality` | nothing to ask for — structural `=` is builtin |
| `'a : struct`, `not struct`, `null`, `(new : unit -> 'a)` | no counterpart; they describe a CLR representation |

`Unmanaged<'a>` is the blittable property: no references, a fixed size, C's
layout. It is what the compiler already decides when it lays out a POD array
or matches emscripten's padding, and its instance carries `byteSize`, which
is the fact a caller actually wants. Instances exist for every primitive;
a struct needs its own, which is the piece a deriving plugin should fill.

## The integer types, and which are int-shaped

`sbyte`, `byte`, `int16`, `uint16`, `int`, `uint32`, `int64` and `uint64`
all exist, with the full numeric tower. Two rails carry them: `int64` and
`uint64` are 64-bit, everything else is int-SHAPED — held in an i32, already
masked (or sign-extended) — so the operators on a `byte` or an `int16` are
the integer ones and the CONVERSION is what narrows.

Signedness shows up exactly where it should: `10UL - 20UL` wraps to
18446744073709551606, and `UInt64.MaxValue > 10UL` is true, which it would
not be if the bits were read signed. `string` on a `uint64` prints unsigned;
`print` boxes, and a box carries no signedness, so print through `string`.

`nativeint` and `unativeint` are absent.

## Active patterns are multi-case and total

`let (|Add|Rem|) x = ...` works: the pattern's cases construct in its body
and match at its uses, literal payloads included. It compiles to a function
returning an `ActiveChoice`, and a match whose clause heads are all cases of
one active pattern passes its scrutinee through that function first. A
clause set that mixes them with anything else does not, so a union case
that merely shares a name is untouched.

PARTIAL active patterns (`(|Foo|_|)`, returning an option) and parameterised
ones (`(|Foo|) arg x`) are not implemented.

## Type extensions are intrinsic only

`type X with member x.Foo () = ...` adds members to a type declared
elsewhere — a class, a record, a union or an INTERFACE — and they resolve on
any value of that type, dispatched statically, as F# dispatches them. What
is not there: extending a builtin (`string`, `int`, an array), and
`[<Extension>]`-style extension methods from another assembly. The
extension declares nothing — no record, no constructor, no vtable slot — so
an interface extension is a function of the receiver, not a new slot every
implementer must fill.

## Weak references are STRONG, and byref members are absent bar one

`WeakReference<'a>` and `ConditionalWeakTable<'k,'v>` exist and hold their
targets. wasm-GC has no weak references and no finalizers: there is no way
to observe that a value became unreachable and no way to be told, so
`TryGetTarget` always succeeds and a table entry lives until it is removed.

**The divergence has teeth.** Reading through one behaves identically — .NET
cannot collect what is still reachable either. What changes is a graph that
relied on weakness to drop its dead half: it keeps it. A cache keyed on
objects grows until its entries are removed explicitly.

`ConditionalWeakTable` compares keys by IDENTITY, as .NET's does; two
structurally equal keys are two entries.

`TryGetValue` IS there, on `Dictionary` and on `ConditionalWeakTable`. F#
hands a byref out-parameter over as a TUPLE, and that shape is expressible:
`match d.TryGetValue k with | (true, v) -> ...` is one source for both
languages.

**byref itself works.** A byref is a one-field CELL — wasm has no address of
a local — and `&x` on a mutable local or field copies IN and OUT around the
call: the callee gets a cell built from the location, and the location is
written back when the call returns. Forwarding one byref parameter to
another hands the same cell on, with no copy.

What that is NOT is an ALIAS. A callee that reaches the same location by
another route does not see the write until the call ends, and two byrefs to
one location do not see each other. Single-threaded, and for the
out-parameter shape everything actually uses, it is indistinguishable.

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
same 111 values — the seq usage included, so `Seq.map f (ra :> seq<int>)`
means in F++ exactly what it means in F#.

## Computation expressions: what still differs

The rewrite is F#'s, read off the F# compiler rather than reconstructed —
each shape was obtained by quoting `builder { ... }` and printing the
desugared quotation, and the oracle suite holds us to it: the builders in
those tests print on every call, so the two compilers are diffed on the call
TRACE, not merely on the answer.

`Run` and `Delay` appear exactly when the builder declares them, each
independently, which needs the builder's TYPE. It comes from a probe: a file
containing a computation expression is resolved and inferred once with every
one of them left alone but its builder typed, and the rewrite runs on the
answers. Files without one skip the probe. The same probe answers the other
type-directed question — whether a bare expression in the body is a value to
`Yield` or a statement, which in F# only its type can say.

`and!` follows the same measured rules: `Bind2Return`/`Bind3Return` when the
builder has them and the continuation ends in `return`, then `Bind2`/`Bind3`,
then `BindReturn`/`Bind` over a merge — and the merge nests the way F#'s
does, the first two sources staying put while the rest fold into a third. A
builder with no merge at all binds the group in SEQUENCE, which computes the
same value over a different graph; that is the only fallback left in it.

What is left:

**The builder must be a NAME.** `seq { }`, `aval { }`, `Foo.builder { }`,
`x.b { }` — but not an application. F# allows any expression, and Expecto's
`test "name" { ... }` is the shape that wants one. A brace after an arbitrary
atom is far more often an ARGUMENT, and guessing wrong newly exposes every
construct in a body the parser had been keeping as token soup — which is how
this restriction was arrived at rather than assumed.

**A builder the probe could not type gets no `Run` and no `Delay`.** That is
the reading that still compiles against the SMALLEST builder, so an unknown
one degrades to the minimum rather than to a call that cannot resolve. It
happens when the file does not type check, or when there is no project
around it.

**`seq { }` has no `Using`, `TryWith` or `TryFinally`.** Scoping a resource
or a handler ACROSS a suspension needs the enumerator to own it, and the
prelude's sequences are built from combinators, not from a state machine. The
rewrite still emits the calls, so `use` or `try` inside a `seq { }` is an
error naming the missing member rather than a wrong answer.

## `use` disposes, and nothing else does

wasm-GC has no finalizers. `use` and an explicit `Dispose` are the only ways
anything is ever released — there is no collector to fall back on, and a
handle nobody disposes stays undisposed. That is why `IEnumerator<'a>`
carries `Dispose` here exactly as .NET's does: a library walking a sequence
it did not build has no other way to hand it back.

**`for x in xs` does NOT dispose its enumerator.** F# wraps the loop in a
try/finally; F++ does not. Every enumerator the prelude builds releases
nothing, so the difference is invisible today — but a user enumerator that
holds something will not be told the loop ended.

**byref is not an alias, and `try`/`finally` emits its finalizer twice.**
Only one copy ever runs; a closure to share it would cost an allocation per
entry for code that is typically one call.

## The FSharp.Data.Adaptive port skips AdaptiveFileSystem.fs

One file of the forty, and it is the only one skipped.

`AdaptiveTools/AdaptiveFileSystem.fs` is not adaptive machinery — it is a
tool built ON the machinery that watches a directory and reads files. It
needs a `FileSystemWatcher`, a `BlockingCollection`, a `Thread` and a
`static do`, and none of those exist here. Nothing else in the library refers
to anything it defines, so skipping it removes no dependency of the heart.

It also uses NAMED optional arguments — `GetFiles(path, ?regex = rx,
recursive = true)` — which this compiler does not have. Optional parameters
themselves work: a caller may leave a trailing `?x` off, and it may pass the
value rather than the option. What is missing is naming an argument at the
call, and every site that needs it is in this file.

The reason to say so plainly rather than leave the file in and failing: in
ONE concatenated pass, a file that does not parse hides every file after it.
Left in, this one peripheral tool reported 1,655 diagnostics that belonged to
nothing, and made the eight files behind it look broken when they were not.

## The port renames PRIVATE types that collide across modules

F++ keys types by BARE NAME, so two types of one name declared in different
modules become one type. The adaptive library does this often: a private
`Traceable` sits in three modules, `Monoid` in four. Merged, `IndexList.trace`
answered with the HashSet one, and `Traceable`'s `'State` came out as a set.

F# tells them apart by their enclosing module, and so does IL — this is the
same distinction `[<CompilationRepresentation(ModuleSuffix)>]` exists to make
where a module's name collides with a type's. The port does it textually: a
`private` type whose name is already taken is renamed `<Module>_<Name>` inside
its module.

Only `private` ones, and that limit is measured, not assumed:

    rename nothing                        259 diagnostics
    rename every colliding type           263   (worse)
    rename the private ones only          246

A public type is referenced from OUTSIDE its module, and renaming it within
the module alone breaks those references — which is why the greedy rule loses.

This is a porting transformation and not a fix. The compiler should key types
by their declaration, not their spelling; STATUS.md scopes what that takes.

## LevelChangedException rides in a `Failure` message

F++ has no user exception TYPES — `exn` is the prelude's closed DU. The
library's one custom exception, `LevelChangedException of newLevel : int`,
becomes `Failure ("!level:" + string n)`; two helpers (`isLevelMsg`,
`levelOfMsg`) decode it at the catch sites. The helpers exist because a
string METHOD on a catch-pattern binder (`msg.StartsWith`) does not resolve
— an annotated top-level function does. `reraise()` becomes `raise e` with
the exception bound by the handler.

## `static val mutable` becomes `static let mutable`

Same zero-initialized slot, a spelling the compiler lowers. A DU-typed one
(`ValueOption<Transaction>`) initializes to its real empty case, because a
NULL falls through an exhaustive `ValueSome/ValueNone` match; everything
else takes `Unchecked.defaultof`. The private qualified self-references
(`Transaction.RunningTransaction`) become bare reads — private means no
reference outside the class exists.

## Module-level generic VALUES are thunked

`let empty<'T> = ...` compiles to one shared global initialized at program
start at the UNIFORM representation — where a `'Key : comparison` body has
no instance to call. The port writes `let empty<'T> () = ...` and turns
every read into a call, which the monomorphizer stamps per instantiation —
the same treatment the generic classes' `static let empty` got.

## Identity hash is spelled `hash`

`RuntimeHelpers.GetHashCode` is .NET's reference-identity hash; F++'s
`hash` on a class that declares no `GetHashCode` override IS the identity
hash. An override that only says so (`Real`'s) is dropped: it restates the
default.

## `List<T>` is spelled `ResizeArray<T>`

One type, the prelude's name for it. The `type List<'T> with` heap-order
extensions become `type ResizeArray<'T> with`.

## A value-position range is a LIST

`(a .. b)` handed around as a value is `seq<'a>` in F#, materialized lazily.
F++ has no lazy seq machinery to hang it on, so a range DENOTES its list —
`[ a .. b ]`, a value range, and a range spliced into brackets all build the
same list, at any `Integral` element, through the prelude's `RangeOps.Seq`
stamped per element type. `for i in a .. b` never materializes anything: it
keeps the direct while lowering. A program that leans on a range's laziness
(`Seq.take 5 (0 .. 1000000000)`) would build the list; the library has no
such use.

`seq { a .. b }` is the same divergence one level up: the computation
expression does not SPLICE a range item yet, so the port rewrites the two
sites the library has onto the list bracket. Native CE splicing is on the
roadmap (STATUS.md).

## A generic type test checks the HEAD

`:? IAdaptiveValue<int>` under .NET checks the full instantiation; F++
descriptors carry no type arguments, so the test is against the erased
constructor — any `IAdaptiveValue<_>` answers yes. The library's uses all
re-discriminate behind the test (a `Tag` string, a payload match), so the
difference is invisible there. A program relying on the ARGUMENTS of a
generic type test to discriminate would take the wrong branch. Type tests
against a generic PARAMETER (`:? 'T`) work — the stamp substitutes the
concrete head, including for members inherited from a generic base.

## A local binding does not generalize its CONSTRAINED variables

`let cmp a b = compare b a` inside a function stays monomorphic in the
variable `compare`'s `Ordered` constraint mentions: the local's body is
emitted once inside the enclosing binding, so the operation must resolve
through the ENCLOSING instantiation — generalizing the variable severed
that tie and the comparison silently ran at int. The cost: a LOCAL helper
with a class constraint cannot be used at two different types in one body
(F# allows it). Hoist it to the top level, where constrained generalization
is the supported path — the error message points at the second use.

## `Comparer<T>.Default` and `FastGenericComparer` become obj-expressions

Both are .NET factory surfaces for "the comparer this type already
implies". The port rewrites them to `{ new IComparer<_> with member
__.Compare(a, b) = compare a b }` — except at `Index`, whose sites sit in
scopes where a constructor parameter NAMED `compare` shadows the builtin;
those spell `a.CompareTo b` directly.

## Derived `Arb` covers records and unions — not tuples, not GADTs

Property-generation instances are derived for every record and union that
declares none, generically in the type's own parameters. Plain tuples are
uniform references with nothing to dispatch on (`instName` says `$ref`), a
GADT's per-case signatures make uniform generation wrong, and a
function-typed component has no canonical inhabitant — all three refuse to
the ordinary "no instance Arb<...>" diagnostic. Struct tuples and records
with tuple FIELDS work: the field's components are what derivation walks.

## The two adaptive `range` functions carry return ascriptions

`ASet.range`/`AList.range` in the port are ascribed `: aset< ^T >` /
`: alist< ^T >`. F# infers the same type; the ascription is belt-and-braces
against a class of higher-order-application inference gaps that used to
leave the result element unpinned (since fixed — see STATUS.md), kept
because it states nothing false and costs nothing.
