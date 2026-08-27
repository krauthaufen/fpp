// A SECONDARY CONSTRUCTOR CANNOT FILL THE INSTANCE IT JUST BUILT.
//
// F# spells that `new (args) as x = <delegate> then <body>`: the delegation
// builds the object, `as x` names it, and the `then` body runs against the
// finished instance. F++ parses neither the `as` binder in that position nor
// the `then` clause, so all three lines below are "unexpected token at top
// level" — the error points at the constructor, not at anything wrong in the
// program.
//
// Delegation with NO body already works (`new (x : int) = Point (x, 0)`, see
// tests/conformance/suites/overloads.fpp). What is missing is only the case
// that needs to run statements afterwards.
//
// Why it matters beyond the syntax: it is the reason `ResizeArray<'a>` has no
// collection-taking constructor, so `ResizeArray<int> ([ 5; 6; 7 ])` does not
// compile even though .NET has had that overload forever. The same shape
// blocks any prelude collection built FROM a sequence. The conformance suite
// `collections.fpp` records the omission where it bites.
//
// Restructuring the primary constructor to take the sequence instead is NOT
// the cheap way out: `ResizeArray` is a generic class, so per CLAUDE.md its
// constructor is already forced into stamping to carry a per-instantiation
// vtable, and it underpins StringBuilder and the compiler's own sources.
//
// Expected once fixed: 3
module KnownIssue

type Bag<'a>() =
    let mutable n = 0
    member x.Count = n
    member x.Add (v : 'a) : unit = n <- n + 1
    new (xs : seq<'a>) as x =
        Bag<'a>()
        then for v in xs do x.Add v

let b = Bag<int>([ 1; 2; 3 ])
print (string b.Count)
