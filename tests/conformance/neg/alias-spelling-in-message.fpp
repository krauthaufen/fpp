// A DIAGNOSTIC NAMES THE TYPE THE WAY THE AUTHOR WROTE IT.
//
// `int32` and `int` are one type, and the compiler canonicalizes on the way
// to emission — but the message must still say `int32` to someone who wrote
// `int32`, which is what fsc does ("This expression was expected to have
// type 'int32'"). Reporting the canonical `int` instead makes the reader
// hunt for a name that is nowhere in their file.
//
// The alias therefore survives inference and is canonicalized at the
// BOUNDARY (Types.typeConName). If someone moves that back to the point
// where a written name becomes a type, these two lines start saying `int`
// and `float` and this case fails.
module Neg_alias_spelling_in_message
//! 16 int32
//! 17 double
let a : int32 = "s"
let b : double = "s"
printfn "%s %s" (string a) (string b)
