// KNOWN ISSUE: `string` on a RECORD, union, tuple or list answers "?".
//
//   string { X = 1; Y = 2 }    // F#: "{ X = 1\n  Y = 2 }"   F++: "?"
//   string (1, "a")            // F#: "(1, a)"               F++: "?"
//   string [ "a"; "b" ]        // F#: "[a; b]"               F++: "?"
//
// It reaches the RUNTIME walker, which cannot know field or case names. `%A`
// renders these correctly, through the Show class (Infer records the hole's
// type in ShowTypes and Lower routes it).
//
// Routing `string` there too is NOT the fix, for two separate reasons:
//
//  1. `instance Show<int>` is literally `static show x = string x`, so the
//     routing is self-recursive — it compiles and then HANGS.
//  2. The two renderings DIFFER on nested strings and chars. `%A` quotes
//     them and `string` does not:
//         string (1, "a")      = "(1, a)"      %A = "(1, \"a\")"
//         string [ "a"; "b" ]  = "[a; b]"      %A = "[\"a\"; \"b\"]"
//     They agree only when nothing inside is a string.
//
// So this needs a SECOND rendering mode on the Show class — a `str` beside
// `show`, differing in how a nested string or char is written — with the
// generated instances providing both. That is the actual work.
//
// Interpolation inherits the gap, since `$"{x}"` renders through `string`.
module StringOfStructured

type Pt = { X : int; Y : int }
printfn "%s" (string { X = 1; Y = 2 })   // F# "{ X = 1\n  Y = 2 }", F++ "?"
printfn "%s" (string (1, "a"))           // F# "(1, a)", F++ "?"
