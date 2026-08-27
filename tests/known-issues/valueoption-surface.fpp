// ValueOption's MEMBERS AND MODULE ARE MISSING.
//
// `ValueSome`/`ValueNone` construct and match correctly, so the type itself
// works. What is absent is the surface around it:
//
//   * `v.IsNone` / `v.IsSome` — compiles, then traps at run time
//   * the `ValueOption` module — `ValueOption.defaultValue`, `.map`, `.bind`
//     and the rest resolve to nothing
//
// The `Option` equivalents are all present, so this is a missing prelude
// surface rather than a representation problem. Uncomment either line below
// to see the two failures separately; as written it is the module one.
//
// Expected once fixed: 9
module KnownIssue

let b : int voption = ValueNone

// print (string b.IsNone)      // traps
print (string (ValueOption.defaultValue 9 b))
