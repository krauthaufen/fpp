module KnownIssue

// A STATIC member reached through a QUALIFIED type does not resolve.
// Expected: 3. Actual: "unknown field Make", and the call is stubbed.
//
// Diagnosis. `Inner.Box.Make` is a three-segment dotted head: module, type,
// member. Member lookup keys on the LAST identifier and needs the receiver's
// type from the member-site table, which is recorded when the head resolves
// to a type — and `Inner.Box` (a qualified TYPE) does not get there.
//
// This is the same family as the constructor bug fixed in 53703ff: a head
// that can be qualified must be named by its LAST segment, and every
// `List.tryFind (fun t -> t.Kind = Ident)` over a head is that question. See
// STATUS.md; there are about thirty of them left to read.
//
// Everything else qualifies correctly — functions, values, constructors,
// union cases in expressions and in patterns, record-literal field labels,
// type annotations and generic type applications.

module Inner =
    type Box<'a>(v : 'a) =
        member x.V = v
        static member Make (n : int) = Box<int>(n)

let ok = Inner.Box<int>(7)          // a qualified CONSTRUCTOR: works
let a = printfn "%d" ok.V           // 7

let bad = Inner.Box.Make 3          // "unknown field Make"
let b = printfn "%d" bad.V
