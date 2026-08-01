module KnownIssue

// A user type whose name matches a PRELUDE type merges with it instead of
// shadowing it. Expected: 3. Actual: "missing field skeys in HashSet", and
// the constructor is stubbed.
//
// Diagnosis. The members table is keyed by the bare type NAME
// ("HashSet.Count"), so two declarations of the same name contribute to one
// entry and construction reads fields that belong to the other type.
//
// It is not a corner: it is why the prelude carries no mutable `HashSet`
// (the name belongs to the immutable one here and in the ported
// FSharp.Data.Adaptive), so the bug costs real library surface.
//
// Fixing it means qualifying type names by their defining file — in the
// fields, ctor, member and descriptor tables alike — or, more cheaply,
// dropping prelude entries owned by a name the project declares itself.

type HashSet<'k>(n : int) =
    member x.Count = n

let s = HashSet<int>(3)
let a = print s.Count
