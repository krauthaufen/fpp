// `for struct(k, v) in xs` BINDS ITS ELEMENTS — over a list as well as an array.
//
// `lowerPat` has no struct-tuple form, so a struct-tuple pattern lowers to a
// WILDCARD: irrefutable, and binding nothing. The ARRAY for-loop works around
// that by destructuring the element through `structBindElem`; the cons walk
// (a list, and a materialized non-ordinal range) did not, so the body named
// variables nothing bound and the whole function came out stubbed — invisible
// until something made it reachable, and then a trap with no diagnostic.

let mutable tests = 0
let mutable failures = 0
let check (what : string) (got : string) (want : string) : unit =
    tests <- tests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" what got want

// the cons walk — the path that had no workaround
let mutable acc = 0
for struct (k, v) in [ struct (1, 10); struct (2, 20); struct (3, 30) ] do
    acc <- acc + k * v
check "for over list" (string acc) "140"

// mixed element types, so a wrong binder shows up as a wrong string
let mutable names = ""
for struct (n, s) in [ struct (1, "a"); struct (2, "b") ] do
    names <- names + string n + s
check "for over list, mixed" names "1a2b"

// the array path, which already worked and must keep working
let mutable acc2 = 0
for struct (k, v) in [| struct (4, 5); struct (6, 7) |] do
    acc2 <- acc2 + k * v
check "for over array" (string acc2) "62"

printfn "DONE tests=%d failures=%d" tests failures
