// KNOWN ISSUES: two computation-expression forms F# accepts and F++ does not.
//
// 1. A COMPUTED builder head — the thing before `{ ... }` must be a name:
//
//      (List.head builders) { return 5 }
//      // F++: type mismatch: OptionBuilder vs 'a -> 'b
//
//    Binding it first (`let b = List.head builders` then `b { ... }`) works.
//
// 2. `let! x = e in body` — the single-line `in` form inside a builder block.
//    The binder does not scope over the body:
//
//      ob { let! v = Some 3 in return v * 10 }
//      // F++: unbound value 'v'
//
//    The offside form (`let! v = Some 3` on its own line) works.
//
// Both are accepted F# and neither is common; the offside spellings are what
// the conformance suite uses.
module ComputedBuilderHead

type OB() =
    member _.Bind (x : 'a option, f : 'a -> 'b option) : 'b option = Option.bind f x
    member _.Return (v : 'a) : 'a option = Some v

let obs = [ OB() ]
let b = (List.head obs) { return 5 }              // F++: type mismatch
let c = (List.head obs) { let! v = Some 3 in return v }   // F++: unbound 'v'
