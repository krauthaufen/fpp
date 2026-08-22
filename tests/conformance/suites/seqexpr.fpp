// SEQUENCE EXPRESSIONS, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/Expressions/DataExpressions/
// SequenceExpressions (final_yield_*, IfThenElse0*, tailcalls0*) and the
// comprehension forms of RangeExpressions.
//
// A sequence is LAZY, so the interesting checks are what runs and WHEN: the
// suite counts source effects rather than only comparing elements, which is
// what catches a comprehension that materialises its source.
//
// DROPPED: `try ... finally` inside `seq { }` (the builder has no
// TryFinally), and the tail-call depth tests (they measure stack, not
// semantics).
module Core_seqexpr

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- the shapes a body can take ------------------------------------------

let one = seq { yield 10 }
test "yield-one" (Seq.toList one = [ 10 ])

let three = seq { yield 1; yield 2; yield 3 }
test "yield-several" (Seq.toList three = [ 1; 2; 3 ])

// `yield!` splices another sequence in
let spliced = seq { for i in [ 1; 2 ] do yield! seq { yield i + 1 } }
test "yield-bang" (Seq.toList spliced = [ 2; 3 ])

let nestedBang = seq { yield 0; yield! three; yield 4 }
test "yield-bang-middle" (Seq.toList nestedBang = [ 0; 1; 2; 3; 4 ])

// a `for` over a range
let squares = seq { for i in 1 .. 4 do yield i * i }
test "for-range" (Seq.toList squares = [ 1; 4; 9; 16 ])

// a `for` over a list, with a filter
let evens = seq { for i in [ 1; 2; 3; 4; 5; 6 ] do if i % 2 = 0 then yield i }
test "for-if" (Seq.toList evens = [ 2; 4; 6 ])

// if/then/else inside the body, both branches yielding
let branchy = seq { for i in 1 .. 4 do if i % 2 = 0 then yield "e" else yield "o" }
test "if-else" (Seq.toList branchy = [ "o"; "e"; "o"; "e" ])

// nested `for`s multiply
let pairs = seq { for a in 1 .. 2 do for b in 1 .. 3 do yield (a, b) }
test "nested-for-count" (List.length (Seq.toList pairs) = 6)
test "nested-for-first" (List.head (Seq.toList pairs) = (1, 1))
test "nested-for-last" (List.last (Seq.toList pairs) = (2, 3))

// a `let` inside the body
let withLet = seq { for i in 1 .. 3 do
                        let d = i * 2
                        yield d + 1 }
test "let-in-body" (Seq.toList withLet = [ 3; 5; 7 ])

// an empty sequence
let none : int seq = seq { for i in 1 .. 3 do if false then yield i }
test "empty" (Seq.isEmpty none)

// ---- laziness: nothing runs until it is pulled ---------------------------

let mutable pulled = 0

let counted =
    seq { for i in 1 .. 100 do
            pulled <- pulled + 1
            yield i }

test "not-run-yet" (pulled = 0)

let firstThree = Seq.toList (Seq.take 3 counted)

test "take-values" (firstThree = [ 1; 2; 3 ])
test "take-pulls-three" (pulled = 3)

// enumerating again RESTARTS the body
pulled <- 0
let againTwo = Seq.toList (Seq.take 2 counted)
test "restart-values" (againTwo = [ 1; 2 ])
test "restart-pulls" (pulled = 2)

// an INFINITE sequence is fine as long as it is cut
let naturals = Seq.initInfinite (fun i -> i)
test "infinite-take" (Seq.toList (Seq.take 4 naturals) = [ 0; 1; 2; 3 ])

let infiniteSeqExpr =
    seq { let mutable i = 0
          while true do
            yield i
            i <- i + 1 }

test "infinite-body" (Seq.toList (Seq.take 3 infiniteSeqExpr) = [ 0; 1; 2 ])

// ---- the combinators over a sequence expression --------------------------

let src = seq { for i in 1 .. 6 do yield i }

test "map" (Seq.toList (Seq.map (fun x -> x * 10) src) = [ 10; 20; 30; 40; 50; 60 ])
test "filter" (Seq.toList (Seq.filter (fun x -> x > 4) src) = [ 5; 6 ])
test "sum" (Seq.sum src = 21)
test "length" (Seq.length src = 6)
test "exists" (Seq.exists (fun x -> x = 3) src)
test "forall" (Seq.forall (fun x -> x > 0) src)
test "skip" (Seq.toList (Seq.skip 4 src) = [ 5; 6 ])
test "head" (Seq.head src = 1)
// bound first: fsi rejects a continuation line that starts with `=`
let collected = Seq.toList (Seq.collect (fun x -> seq { yield x; yield x }) (seq { yield 1; yield 2 }))
test "collect" (collected = [ 1; 1; 2; 2 ])

// a sequence built from a list comprehension and back
test "of-list" (Seq.toList (List.toSeq [ 1; 2 ]) = [ 1; 2 ])
test "to-array" (Array.toList (Seq.toArray src) = [ 1; 2; 3; 4; 5; 6 ])

// ---- list and array comprehensions share the shape -----------------------

let listComp = [ for i in 1 .. 4 do yield i * i ]
test "list-comprehension" (listComp = [ 1; 4; 9; 16 ])

let listCompIf = [ for i in 1 .. 6 do if i % 3 = 0 then yield i ]
test "list-comprehension-if" (listCompIf = [ 3; 6 ])

let arrComp = [| for i in 1 .. 3 do yield i + 1 |]
test "array-comprehension" (Array.toList arrComp = [ 2; 3; 4 ])

// the arrow form, without the `yield` keyword
let arrowComp = [ for i in 1 .. 3 -> i * 2 ]
test "arrow-comprehension" (arrowComp = [ 2; 4; 6 ])

// a comprehension over a sequence expression
let overSeq = [ for x in src do if x > 3 then yield x ]
test "comprehension-over-seq" (overSeq = [ 4; 5; 6 ])

// ---- effects happen in ORDER, once per element ---------------------------

let mutable trace = ""

let traced =
    seq { for c in [ "a"; "b" ] do
            trace <- trace + c
            yield c }

trace <- ""
let drained = Seq.toList traced
test "effect-order" (drained = [ "a"; "b" ] && trace = "ab")

// a filtered element still runs the effects before the filter
trace <- ""
let filtered = Seq.toList (Seq.filter (fun (c : string) -> c = "b") traced)
test "effects-before-filter" (filtered = [ "b" ] && trace = "ab")

printfn "DONE tests=%d failures=%d" ntests failures
