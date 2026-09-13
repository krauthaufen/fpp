// `box` OF A CANONICAL TYPE PARAMETER HOLDING A TAGGED SCALAR.
//
// `box v` inside a generic body answers by the STATIC kind of `v`. Where the
// instantiation STAMPS (int and the boxed scalars — `boxedScalar` in Link) the
// binder is concrete and the box is emitted; that case is fixed and pinned by
// suites/boxgenericclosure.fpp. bool, char, byte, sbyte, int16, uint16 and
// uint32 do NOT stamp: they ride the uniform word as TAGGED scalars, and in
// canonical code no static type separates a tagged scalar from a pointer, so
// `box` is emitted as the identity and `unbox` meets a tagged word instead of
// a box object.
//
// This prints nothing and throws. F# prints "True" then "x".
//
// WHAT IT NEEDS: the decision has to be made at RUNTIME from the witness the
// body already carries — the same mechanism `lowMkCellW` uses to pick a raw
// vs. ref cell (`refMask w`). The witness also has to name WHICH scalar, since
// each boxed scalar carries its own class id (CID_BOX_BASE + kind), so the box
// site becomes a small dispatch on the witness kind rather than one shape.
//
// NOT a regression: before the stamped half was fixed, `int` failed here too.
module BoxCanonicalTaggedScalar
let viaClosure (v : 'a) : unit -> obj = fun () -> box v
printfn "%s" (string (unbox<bool> ((viaClosure true) ())))
printfn "%s" (string (unbox<char> ((viaClosure 'x') ())))
