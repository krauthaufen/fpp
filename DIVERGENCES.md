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
hash container silently loses it. `hash` on an array is therefore identity-
based too.

This also matches what an array *is* in F++ — a buffer whose purpose is to
be handed to C or JS by address, and which can be mutated through a pinned
pointer while the GC-side value looks untouched. See REPRESENTATION.md.

**Status: true today, but by accident.** The runtime equality walk has no
array case and falls through to `ref.eq`. When per-type `equals`/`hash` are
generated (see DESIGN.md, "Identity"), arrays must be given identity
equality *explicitly* — the natural implementation of "structural equality,
recursing into components" would quietly make them structural and break
this.
