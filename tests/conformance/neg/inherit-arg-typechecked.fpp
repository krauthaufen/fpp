// A BASE CONSTRUCTOR'S ARGUMENTS ARE TYPE-CHECKED.
//
// They used to be LOWERED but never INFERRED, so this compiled clean —
// `--strict` included — and ran with a string where a list belongs. The same
// gap cost WITNESSES: with nothing typing the argument, no instantiation was
// recorded for what it names, so a generic value passed to a base constructor
// stayed canonical and its witness went out UNIFORM. `IndexList.trace`
// reaching AbstractReader this way was 6 of fpp.adaptive's 39 uniform sites.
//
// The expected parameter type must flow INTO the argument (`exprExpect`, the
// channel an ordinary argument uses). Typing it bottom-up and unifying
// afterwards is not the same thing and is wrong twice over: it rejects
// `(<>) "Input"` passed where `obj -> bool` is declared, and it records the
// instantiation at `obj` — an unflagged witness asserting "pointer" over what
// may be a raw int, which is worse than the flagged fallback it replaces.
//! 23 list<'a> vs string
module InheritArgTypechecked
[<AbstractClass>]
type Base<'T>(seed : list<'T>) =
    member b.Seed = seed
    abstract Tag : int
type Derived<'T>(x : int) =
    inherit Base<'T>("this is not a list")
    override d.Tag = x
printfn "%d" ((Derived<int>(7) :> Base<int>).Tag)
