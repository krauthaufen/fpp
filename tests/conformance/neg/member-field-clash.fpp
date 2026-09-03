// a member taking a record field's name: `r.Name` in the member's own body
// resolved to the MEMBER, and the program hung in the recursion at run time
module Neg_member_field_clash
//! 7 same name as a field
type Repro =
    { Name : int }
    member r.Name : int = r.Name
printfn "%d" ({ Name = 5 } : Repro).Name
