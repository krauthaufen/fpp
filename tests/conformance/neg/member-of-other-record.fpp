// a member that exists only on ANOTHER record type. Records cannot inherit,
// so the name existing elsewhere is proof it cannot be reached here; left
// accepted this lowered to a bare member access and trapped.
module Neg_member_of_other_record
//! 11 has no member
type A = { X : int }
type B = { Y : int }
type B with
    member b.OnlyB (f : int -> int) : int = f b.Y
let a : A = { X = 1 }
printfn "%d" (a.OnlyB (fun v -> v + 1))
