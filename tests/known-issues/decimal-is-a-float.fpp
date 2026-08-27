// `decimal` IS A BINARY FLOAT, SILENTLY.
//
// The `m` suffix is accepted and the value behaves as a `float`, so every
// decimal computation is done in binary and answers what a float answers:
//
//     0.1m + 0.2m   F#: 0.3        F++: 0.30000000000000004
//
// System.Decimal is a 128-bit BASE-TEN type whose whole reason to exist is
// that money arithmetic comes out exact. A program that reaches for `m` is
// asking for precisely the property this does not provide, and nothing
// warns — the literal compiles, the arithmetic runs, the answer is wrong in
// the last places.
//
// Two ways out, and the choice is not obvious:
//   * implement it — a 128-bit base-10 numeric type, its arithmetic, its
//     parsing and its printing. Real work, and it needs an int128 or a
//     four-word representation the backends do not have today.
//   * REJECT the `m` suffix, so the mistake is a compile error rather than
//     a wrong number. Cheap, and honest, but it breaks any source that
//     currently uses `m` and happens to tolerate float precision.
//
// Until then this is recorded rather than fixed, because a silent wrong
// answer deserves to be written down somewhere.
//
// Expected once fixed: 0.3
module KnownIssue

let a = 0.1m
let b = 0.2m
print (string (a + b))
