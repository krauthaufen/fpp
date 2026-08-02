// A `let rec f ... and g ...` group inside the big `lower` function
// MISCOMPILES under self-host. The .NET build is fine, all 637 tests pass,
// and the corpus gate then dies with an `unreachable` deep inside a lambda —
// in code that has nothing to do with the group.
//
// Found by writing this, in Core/Lower.fs:
//
//     let rec hasStructPayload (p : GreenNode) : bool =
//         (structPayloadOf p).IsSome || ...
//     and structPayloadOf (p : GreenNode) : GreenNode option = ...
//
// Splitting it into two ordinary bindings — `structPayloadOf` first, then a
// self-recursive `hasStructPayload` that calls it — fixed the gate with NO
// other change. The nested branch the group existed for was never even
// reached during the failing compile, which is what makes this the shape and
// not the logic.
//
// This file does not reproduce it on its own: a `let rec ... and` group at
// module level compiles and runs correctly, as below. What has not been
// isolated is which ingredient of the enclosing function matters — its size,
// its closure over the surrounding `let`s, or the group's position among
// them. Somebody should narrow it before it bites again, because the failure
// mode is a runtime trap a long way from the cause.

module M

let rec isEven (n : int) : bool =
    if n = 0 then true else isOdd (n - 1)
and isOdd (n : int) : bool =
    if n = 0 then false else isEven (n - 1)

let go =
    printfn "%b %b" (isEven 4) (isOdd 4)
