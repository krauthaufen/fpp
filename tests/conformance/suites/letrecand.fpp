// `let rec ... and` GROUPS, ported from dotnet/fsharp's
// tests/fsharp/core/letrec, letrec-mutrec and letrec-mutrec2.
//
// The case that matters is the FORWARD reference: the first binding of a
// group uses the second, which has not been typed yet. Its type has to be
// the one the later binding turns out to have — including for a MEMBER
// access on the result, which is where this went wrong. `(payload k).IsSome`
// ahead of `and payload ... : int option` compiled clean and trapped at run
// time, because the access never learned its receiver was an option.
//
// DROPPED: `let rec` over VALUES that observe each other's initialisation
// (F#'s lazy-initialisation checks and the InvalidOperationException they
// raise), and the recursive-object-expression cases.
module Core_letrecand

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

// ---- plain mutual recursion ------------------------------------------------

let rec isEven (k : int) : bool = if k = 0 then true else isOdd (k - 1)
and isOdd (k : int) : bool = if k = 0 then false else isEven (k - 1)

test "mutual-even" (isEven 4)
test "mutual-odd" (isOdd 5)
test "mutual-even-zero" (isEven 0)
test "mutual-odd-zero" (not (isOdd 0))

// the same group written the other way round
let rec odd2 (k : int) : bool = if k = 0 then false else even2 (k - 1)
and even2 (k : int) : bool = if k = 0 then true else odd2 (k - 1)

test "mutual-reversed-order" (even2 6 && odd2 7)

// ---- a FORWARD reference whose result takes a member -----------------------

// the receiver's type comes from a binding BELOW: an option, and `.IsSome`
// is a member of it
let rec hasPayload (k : int) : bool = (payloadOf k).IsSome
and payloadOf (k : int) : int option = if k > 0 then Some k else None

test "forward-option-is-some" (hasPayload 3)
test "forward-option-is-none" (not (hasPayload 0))

// `.Value` through a forward reference
let rec doubled (k : int) : int = (someOf k).Value
and someOf (k : int) : int option = Some (k * 2)

eq "forward-option-value" (string (doubled 3)) "6"

// a LIST, a RECORD and a STRING through a forward reference
type Holder = { Amount : int; Label : string }

let rec isEmptyList (k : int) : bool = (listOf k).IsEmpty
and listOf (k : int) : int list = if k > 0 then [ k ] else []

let rec amountOf (k : int) : int = (holderOf k).Amount
and holderOf (k : int) : Holder = { Amount = k * 3; Label = "h" }

let rec widthOf (k : int) : int = (labelOf k).Length
and labelOf (k : int) : string = if k > 0 then "abc" else ""

test "forward-list-is-empty" (isEmptyList 0)
test "forward-list-not-empty" (not (isEmptyList 2))
eq "forward-record-field" (string (amountOf 3)) "9"
eq "forward-string-member" (string (widthOf 1)) "3"

// a THREE-way group, each reaching the next
let rec stepA (k : int) : bool = (stepB k).IsSome
and stepB (k : int) : int option = if stepC k then Some k else None
and stepC (k : int) : bool = k > 0

test "three-way-group" (stepA 3)
test "three-way-group-false" (not (stepA 0))

// ---- the same shapes, LOCAL to a function ----------------------------------

let localGroup (p : int) : bool =
    let rec has (k : int) : bool = (payload k).IsSome
    and payload (k : int) : int option = if k > 0 then Some k else None
    has p

test "local-forward-option" (localGroup 3)
test "local-forward-option-none" (not (localGroup 0))

let localMutual (n : int) : bool =
    let rec ev (k : int) : bool = if k = 0 then true else od (k - 1)
    and od (k : int) : bool = if k = 0 then false else ev (k - 1)
    ev n

test "local-mutual" (localMutual 8)
test "local-mutual-odd" (not (localMutual 7))

// a group closing over the enclosing function's bindings
let closingGroup (bound : int) (v : int) : int =
    let rec down (k : int) : int = if k <= 0 then bound else up (k - 1)
    and up (k : int) : int = if k <= 0 then bound + 1 else down (k - 1)
    down v

eq "closing-group" (string (closingGroup 10 4)) "10"
eq "closing-group-odd" (string (closingGroup 10 3)) "11"

// ---- mutual recursion over a mutually recursive TYPE -----------------------

type Tree =
    | Leaf of int
    | Node of Forest

and Forest =
    | Empty
    | Cons of Tree * Forest

let rec sumTree (t : Tree) : int =
    match t with
    | Leaf v -> v
    | Node f -> sumForest f

and sumForest (f : Forest) : int =
    match f with
    | Empty -> 0
    | Cons (t, rest) -> sumTree t + sumForest rest

let sample = Node (Cons (Leaf 1, Cons (Node (Cons (Leaf 2, Empty)), Cons (Leaf 3, Empty))))

eq "mutual-over-mutual-types" (string (sumTree sample)) "6"
eq "mutual-forest-empty" (string (sumForest Empty)) "0"

// the FORWARD direction over those types: the first binding names the second
let rec depthTree (t : Tree) : int =
    match t with
    | Leaf _ -> 1
    | Node f -> 1 + depthForest f

and depthForest (f : Forest) : int =
    match f with
    | Empty -> 0
    | Cons (t, rest) ->
        let a = depthTree t
        let b = depthForest rest
        if a > b then a else b

eq "forward-depth" (string (depthTree sample)) "3"

// ---- generic bindings in a group -------------------------------------------

let rec lengthOf (xs : 'a list) : int =
    match xs with
    | [] -> 0
    | _ :: rest -> 1 + lengthOf rest

and countTwice (xs : 'a list) : int = 2 * lengthOf xs

eq "generic-in-group" (string (lengthOf [ 1; 2; 3 ])) "3"
eq "generic-in-group-strings" (string (lengthOf [ "a"; "b" ])) "2"
eq "generic-forward" (string (countTwice [ 1; 2 ])) "4"

// ---- a group whose members are used before AND after ------------------------

let rec ping (k : int) : string = if k <= 0 then "done" else pong (k - 1)
and pong (k : int) : string = if k <= 0 then "stop" else ping (k - 1)

eq "ping-even" (ping 4) "done"
eq "ping-odd" (ping 3) "stop"
eq "pong-direct" (pong 2) "stop"

printfn "DONE tests=%d failures=%d" ntests failures
