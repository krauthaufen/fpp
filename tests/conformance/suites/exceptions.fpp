// Exception semantics in the common F#/F++ subset: what a handler sees, what
// order `finally` runs in, and what survives a rethrow. dotnet/fsharp's own
// `control` suite is the async one, so this is written in the harness's shape
// rather than ported verbatim.
module Core_exceptions

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- try/with yields a value -------------------------------------------

test "with-value" ((try 1 with _ -> 2) = 1)
test "with-catches" ((try failwith "x" with _ -> 2) = 2)
test "with-message" ((try failwith "boom" with Failure m -> m | _ -> "?") = "boom")
test "with-nested-inner" ((try (try failwith "a" with _ -> 1) with _ -> 2) = 1)
test "with-nested-outer" ((try (try failwith "a" with _ -> failwith "b") with Failure m -> m | _ -> "?") = "b")

// ---- finally runs on BOTH paths, and in order ---------------------------

let order = ResizeArray<string>()

let normalPath () =
    order.Clear ()
    let r =
        try
            order.Add "body"
            1
        finally
            order.Add "finally"
    order.Add "after"
    r

test "finally-normal-value" (normalPath () = 1)
test "finally-normal-order" (List.ofSeq order = [ "body"; "finally"; "after" ])

let throwPath () =
    order.Clear ()
    let r =
        try
            try
                order.Add "body"
                failwith "x"
                0
            finally
                order.Add "finally"
        with _ ->
            order.Add "handler"
            2
    r

test "finally-throw-value" (throwPath () = 2)
// the finally runs BEFORE the handler that catches past it
test "finally-throw-order" (List.ofSeq order = [ "body"; "finally"; "handler" ])

let nestedFinally () =
    order.Clear ()
    (try
        try
            try
                failwith "x"
            finally
                order.Add "inner"
        finally
            order.Add "outer"
     with _ -> order.Add "caught")
    List.ofSeq order

test "finally-nested-order" (nestedFinally () = [ "inner"; "outer"; "caught" ])

// ---- what the handler matches ------------------------------------------

exception MyError of int

test "custom-raise" ((try raise (MyError 7) with MyError n -> n | _ -> 0) = 7)
test "custom-not-failure" ((try raise (MyError 7) with Failure _ -> 1 | MyError _ -> 2 | _ -> 3) = 2)
test "failure-not-custom" ((try failwith "x" with MyError _ -> 1 | Failure _ -> 2 | _ -> 3) = 2)
test "wildcard-last" ((try raise (MyError 1) with Failure _ -> 1 | _ -> 9) = 9)
test "first-match-wins" ((try failwith "x" with Failure _ -> 1 | _ -> 2) = 1)

// ---- rethrow ------------------------------------------------------------

let rethrown () =
    try
        try
            failwith "inner"
        with Failure m ->
            failwith (m + "-again")
    with Failure m -> m

test "rethrow-message" (rethrown () = "inner-again")

// ---- exceptions cross frames and loops ----------------------------------

let deep (n : int) : int =
    let rec go k = if k = 0 then failwith "bottom" else 1 + go (k - 1)
    try go n with Failure m -> String.length m

test "through-frames" (deep 20 = 6)

let outOfLoop () =
    let mutable seen = 0
    try
        for i in 1 .. 10 do
            seen <- i
            if i = 3 then failwith "stop"
    with _ -> ()
    seen

test "out-of-for" (outOfLoop () = 3)

let outOfWhile () =
    let mutable i = 0
    try
        while true do
            i <- i + 1
            if i = 4 then failwith "stop"
    with _ -> ()
    i

test "out-of-while" (outOfWhile () = 4)

// a lambda that raises, called through a higher-order function
test "through-lambda" ((try List.map (fun x -> if x = 2 then failwith "m" else x) [1;2;3] |> List.length with _ -> 0 - 1) = 0 - 1)

// ---- the standard raisers ----------------------------------------------

test "failwithf" ((try failwithf "n=%d" 3 with Failure m -> m | _ -> "?") = "n=3")
test "invalidArg" ((try invalidArg "p" "bad" |> ignore; false with _ -> true))
test "raise-Failure" ((try raise (Failure "z") with Failure m -> m | _ -> "?") = "z")

// ---- a handler's own value is the result -------------------------------

test "handler-value-type" ((try "a" with _ -> "b") = "a")
test "finally-does-not-change-value" ((try 5 finally ignore 0) = 5)

// ---- reraise ----------------------------------------------------------
// `reraise ()` re-raises what the enclosing `with` clause caught. F# gives
// no other way to name that exception, so a wildcard handler can reraise
// just as a binding one can.

exception Reraised of string

let viaWildcard () : unit = try failwith "boom" with _ -> reraise ()
test "reraise-from-wildcard" ((try (viaWildcard (); "no") with e -> e.Message) = "boom")

let viaCase () : unit = try raise (Reraised "x") with Reraised _ -> reraise ()
test "reraise-keeps-the-case"
     ((try (viaCase (); "no") with Reraised m -> m | _ -> "wrong") = "x")

// a handler may reraise CONDITIONALLY
let sometimes (n : int) : unit =
    try failwith "cond" with e -> (if n > 0 then reraise () else ())

test "reraise-when-taken" ((try (sometimes 1; "no") with e -> e.Message) = "cond")
test "reraise-when-not-taken" ((sometimes 0; "ran") = "ran")

// through two levels of handler
let twice () : unit = try (try failwith "deep" with _ -> reraise ()) with _ -> reraise ()
test "reraise-through-two-levels" ((try (twice (); "no") with e -> e.Message) = "deep")

// a `finally` still runs when the handler reraises
let mutable finLog = ""
let withFinally () : unit =
    try
        try failwith "e6" with _ -> reraise ()
    finally finLog <- finLog + "fin"

test "reraise-runs-finally" ((try (withFinally (); "no") with e -> e.Message) = "e6")
test "reraise-finally-ran" (finLog = "fin")

// a handler that does NOT reraise is unaffected
let handled () : string = try failwith "e4" with e -> "handled " + e.Message
test "handler-without-reraise" (handled () = "handled e4")

// ---- the argument exceptions carry .NET's message shape --------------------

test "invalidArg-message"
     ((try (invalidArg "p" "bad thing"; "no") with e -> e.Message) = "bad thing (Parameter 'p')")
test "invalidOp-message"
     ((try (invalidOp "oops"; "no") with e -> e.Message) = "oops")
test "nullArg-message"
     ((try (nullArg "q"; "no") with e -> e.Message) = "Value cannot be null. (Parameter 'q')")

printfn "DONE tests=%d failures=%d" ntests failures
