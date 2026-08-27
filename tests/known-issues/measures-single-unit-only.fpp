// UNITS OF MEASURE HANDLE ONE UNIT, NOT AN ALGEBRA.
//
// `[<Measure>] type m` and `5.0<m>` work, and the arithmetic that stays
// inside one unit answers exactly what F# answers (measures are ERASED at
// run time in F# too, so the values agree). What is missing is the algebra:
//
//   * `float<m/s>` as an annotation — the `/` is read as a second type
//     ARGUMENT, giving "type mismatch: float vs float<m, s>"
//   * `10.0<m/s>` as a literal — does not parse at all
//
// So a measures conformance suite cannot be ported: the interesting half of
// the feature is the composition, and dimensioned division is the first
// thing any such test does. The single-unit cases below DO work and are the
// part worth keeping in mind if this is ever finished.
//
// Expected once fixed: 10.44 (100.0<m> / 9.58<s>, near enough)
module KnownIssue

[<Measure>] type m
[<Measure>] type s

let dist = 100.0<m>
let time = 9.58<s>
let v : float<m/s> = dist / time
print (string v)
