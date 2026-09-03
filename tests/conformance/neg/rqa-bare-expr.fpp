// a case of a [<RequireQualifiedAccess>] type named bare, in expression
// position. Upstream: the attribute was parsed and IGNORED, so two such
// types declaring one case name bound it to whichever came last.
module Neg_rqa_bare_expr
//! 10 RequireQualifiedAccess
[<RequireQualifiedAccess>]
type Colour = Red | Green
[<RequireQualifiedAccess>]
type Fruit = Red | Apple
let x = Red
printfn "%A" x
