// A MODULE ABBREVIATION DOES NOT RESOLVE.
//
// `module Ab = Inner` gives a module a second name; every later `Ab.x` is
// `Inner.x`. The declaration parses, but nothing binds the new name, so the
// use reaches emission as an unresolved variable:
//
//     error (strict): stubbed ... unresolved variable ... name=Ab
//
// Found while probing for the `modules` conformance suite, which is why no
// such suite exists yet — the abbreviation is too common a shape to write
// around. Nested targets (`module Ab = Inner.Deep`) fail the same way.
//
// Expected once fixed: 2
module KnownIssue

module Inner =
    let y = 2

module Ab = Inner

print (string Ab.y)
