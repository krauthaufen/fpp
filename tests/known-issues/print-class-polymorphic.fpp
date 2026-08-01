module KnownIssue

// `print` of a class-polymorphic expression converts as though it were an
// int. Expected: 2.5. Actual: a cast failure inside $toi.
//
// Diagnosis. `print` picks its conversion from the OpKind recorded at the
// print token, which inference takes from the argument's type. For an
// argument whose type is settled by class resolution rather than by
// unification at that site, the kind comes out empty and the int path is
// emitted. `printfn "%f"` is unaffected — the format string constrains the
// argument before the kind is read — and binding through an annotated
// `let` fixes it, which is what stdlib/dotnet.fpp does.

let ok : float = abs -2.5
let a = print ok                         // 2.5
let b = print (abs -2.5)                 // traps
