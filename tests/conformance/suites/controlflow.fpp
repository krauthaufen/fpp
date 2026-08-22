// Control-flow expressions, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/Expressions/
// ControlFlowExpressions (TryFinally, TryWith, SimpleFor, SequenceIteration)
// with the loop forms of BasicGrammarElements and the slice sugar of
// SyntacticSugar/Slices.
//
// The upstream files exit non-zero on failure and mostly check ONE thing; the
// ORDER of effects is what makes these interesting, so each case here records
// its effects into a string and asserts the whole trace.
//
// DROPPED: `try ... finally` INSIDE a `seq { }` (upstream
// TryFinallyInSequence01) — the sequence builder has no TryFinally member
// here; [<AllowNullLiteral>] classes and Unchecked.defaultof<record> (null
// records are not in the subset); and the WARNING cases (a non-unit finally
// body), which the negative gate covers rather than this one.
module Core_controlflow

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- try/with catches, and the handler picks by SHAPE --------------------

let caught1 =
    try
        failwith "epicfail"
        false
    with
    | Failure "non-epicfail" -> false
    | Failure "epicfail" -> true
    | _ -> false

test "trywith-failure-literal" caught1

// F#'s `Failure` pattern matches a plain System.Exception, so an exception of
// ANOTHER type is what falls to the wildcard
exception MyErr of int

let caught2 =
    try
        raise (MyErr 1)
        "none"
    with
    | Failure m -> "failure:" + m
    | _ -> "other"

test "trywith-other-exception" (caught2 = "other")

// the value of a try/with IS the value of whichever branch ran
let tryValue (fail : bool) : int =
    try
        if fail then failwith "x"
        1
    with _ -> 2

test "trywith-value-ok" (tryValue false = 1)
test "trywith-value-caught" (tryValue true = 2)

// a handler may re-raise, and an OUTER handler takes it
let nested =
    try
        try
            failwith "inner"
        with _ ->
            failwith "rethrown"
    with Failure m -> m

test "trywith-nested-rethrow" (nested = "rethrown")

// an exception that is NOT matched by the handler list leaves the try
let unmatched =
    try
        try
            raise (MyErr 2)
            "no"
        with Failure m -> "wrong:" + m
    with _ -> "outer"

test "trywith-unmatched-escapes" (unmatched = "outer")

// a user-declared exception carries its payload through the handler
let userExn =
    try
        raise (MyErr 42)
        0
    with
    | MyErr n -> n
    | _ -> 0 - 1

test "trywith-user-exception" (userExn = 42)

let userExnUnmatched =
    try
        raise (MyErr 7)
        "no"
    with
    | Failure _ -> "failure"
    | _ -> "wildcard"

test "trywith-user-not-failure" (userExnUnmatched = "wildcard")

// ---- try/finally: the finally block runs on BOTH paths --------------------

let mutable trace = ""

let finallyOnSuccess () : int =
    try
        trace <- trace + "body "
        1
    finally
        trace <- trace + "finally "

trace <- ""
let fv = finallyOnSuccess ()
test "finally-on-success" (fv = 1 && trace = "body finally ")

// even though the finally block runs, the exception still propagates
let mutable finallyHit = false

let caughtAfterFinally =
    try
        try
            failwith "epicfail"
            false
        finally
            finallyHit <- true
    with _ -> true

test "finally-then-handler" caughtAfterFinally
test "finally-hit-on-exception" finallyHit

// the finally of an INNER try runs before the outer handler
trace <- ""
let orderOfEffects =
    try
        try
            trace <- trace + "raise "
            failwith "e"
            "no"
        finally
            trace <- trace + "inner-finally "
    with _ ->
        trace <- trace + "handler "
        "done"

test "finally-order" (orderOfEffects = "done" && trace = "raise inner-finally handler ")

// ---- for loops -----------------------------------------------------------

let mutable counter = 0
for _ in 1 .. 10 do
    counter <- counter + 1
test "for-range" (counter = 10)

counter <- 0
for i = 10 downto 0 do
    counter <- counter + 1
test "for-downto" (counter = 11)

// a downto loop that never runs
counter <- 0
for _ = 0 downto 1 do
    counter <- counter + 1
test "for-downto-empty" (counter = 0)

// an ascending loop whose bounds cross never runs either
counter <- 0
for _ = 5 to 1 do
    counter <- counter + 1
test "for-to-empty" (counter = 0)

// a single-iteration loop
counter <- 0
for _ = 3 to 3 do
    counter <- counter + 1
test "for-to-single" (counter = 1)

// stepped ranges, including a step that does not divide the span
let mutable acc = []
for i in 0 .. 2 .. 9 do
    acc <- i :: acc
test "for-stepped" (List.rev acc = [ 0; 2; 4; 6; 8 ])

acc <- []
for i in 10 .. -3 .. 0 do
    acc <- i :: acc
test "for-stepped-down" (List.rev acc = [ 10; 7; 4; 1 ])

// the loop variable is a fresh binding per iteration, and shadowing is fine
let mutable sum = 0
for i in [ 1; 2; 3 ] do
    let i = i * 10
    sum <- sum + i
test "for-list-shadow" (sum = 60)

// over an array, a sequence and a string's chars
sum <- 0
for x in [| 4; 5; 6 |] do
    sum <- sum + x
test "for-array" (sum = 15)

sum <- 0
for x in Seq.take 3 (Seq.initInfinite (fun i -> i + 1)) do
    sum <- sum + x
test "for-seq" (sum = 6)

// a tuple pattern in the loop header
let mutable prod = 0
for (a, b) in [ (2, 3); (4, 5) ] do
    prod <- prod + a * b
test "for-tuple-pattern" (prod = 26)

// nested loops run the inner one in full per outer step
let mutable cells = 0
for _ in 1 .. 3 do
    for _ in 1 .. 4 do
        cells <- cells + 1
test "for-nested" (cells = 12)

// ---- while ---------------------------------------------------------------

let mutable n = 0
let mutable steps = 0
while n < 100 do
    n <- n + 7
    steps <- steps + 1
test "while-loop" (n = 105 && steps = 15)

// a while whose condition is false at entry never runs its body
let mutable never = 0
while false do
    never <- never + 1
test "while-never" (never = 0)

// ---- if/then/else is an EXPRESSION ---------------------------------------

let branch (x : int) : string = if x > 0 then "pos" elif x < 0 then "neg" else "zero"

test "if-elif-else" (branch 1 = "pos" && branch (0 - 1) = "neg" && branch 0 = "zero")

// a unit-typed `if` with no else runs for its effect only
let mutable effect = 0
if true then effect <- 1
if false then effect <- 2
test "if-no-else" (effect = 1)

// ---- slices --------------------------------------------------------------

let arr = [| 0; 1; 2; 3; 4; 5 |]

test "slice-middle" (Array.toList arr.[1..3] = [ 1; 2; 3 ])
test "slice-from" (Array.toList arr.[4..] = [ 4; 5 ])
test "slice-to" (Array.toList arr.[..2] = [ 0; 1; 2 ])
test "slice-all" (Array.toList arr.[*] = [ 0; 1; 2; 3; 4; 5 ])
test "slice-empty" (Array.toList arr.[3..2] = [])
test "slice-single" (Array.toList arr.[2..2] = [ 2 ])
// a slice is a COPY: writing through it leaves the source alone
let sliced = arr.[1..2]
sliced.[0] <- 99
test "slice-is-copy" (arr.[1] = 1)

let str = "abcdef"
test "slice-string" (str.[1..3] = "bcd")
test "slice-string-from" (str.[4..] = "ef")

// ---- sequential expressions ----------------------------------------------

// `a; b` runs a for its effect and answers b
let mutable order = ""
let seqValue =
    order <- order + "1"
    order <- order + "2"
    99
test "sequential" (seqValue = 99 && order = "12")

printfn "DONE tests=%d failures=%d" ntests failures
