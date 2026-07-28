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
