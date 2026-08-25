// KNOWN ISSUE: a string is not an IEnumerable<char> for the Seq module.
//
//   for c in "abc" do ...      // works
//   "abc".ToCharArray ()       // works
//   Seq.length "abc"           // type mismatch: IEnumerable<'a> vs string
//   List.ofSeq "abc"           // same
//
// `for ... in` over a string is special-cased, and the String module covers
// map/filter/iter/collect, so the gap is only the generic sequence functions.
// Closing it means giving `string` the seq interface rather than another
// special case.
module StringAsSeq

printfn "%d" (Seq.length "abc")   // F# prints 3; F++ does not compile
