// a list whose ELEMENT type does not fit the seq the parameter asks for.
// The widening `list -> seq` is by constructor NAME, so without an element
// check this compiled and rendered three EMPTY strings.
module Neg_seq_element_mismatch
//! 6 type mismatch: IEnumerable<string> vs list<int>
printfn "%s" (String.concat "," [ 1; 2; 3 ])
