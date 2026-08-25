// KNOWN ISSUE: `string` on a RECORD, union, tuple or list answers "?".
//
//   string { X = 1; Y = 2 }    // F#: "{ X = 1\n  Y = 2 }"   F++: "?"
//   string (1, 2)              // F#: "(1, 2)"               F++: "?"
//   string [ 1; 2 ]            // F#: "[1; 2]"               F++: "?"
//
// It reaches the RUNTIME walker, which cannot know field or case names.
// `%A` renders these correctly because Infer records the hole's type
// (ShowTypes) and Lower routes it through the Show class.
//
// Doing the same for `string` — record the argument type at the `string`
// token and route to `$class:Show:show:<ty>` — compiles, and then HANGS at
// run time: the Show instance is itself written in terms of `string`, so the
// routing is self-recursive. Breaking that cycle (a Show implementation that
// cannot re-enter `string`, or a separate entry point for it) is the actual
// work; the routing is the easy half.
//
// Interpolation inherits the gap, since `$"{x}"` renders through `string`.
module StringOfStructured

type Pt = { X : int; Y : int }
printfn "%s" (string { X = 1; Y = 2 })   // F# "{ X = 1\n  Y = 2 }", F++ "?"
printfn "%s" (string (1, 2))             // F# "(1, 2)", F++ "?"
