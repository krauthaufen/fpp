// CUSTOM COMPUTATION EXPRESSIONS, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/Expressions/
// ComputationExpressions and the builder cases of LanguageFeatures.
//
// A builder is an ordinary object: `b { ... }` rewrites to calls on it, and
// which calls appear is decided by the SYNTAX in the block. The cases that
// matter are the rewrites that are easy to get subtly wrong — `let!` chaining
// into Bind, a `return!` passing the value through unchanged, `for` reaching
// For rather than a loop, and Zero standing in for a missing else.
//
// DROPPED: `use!`/`try...finally` in a builder (deterministic cleanup has its
// own gate), custom operations (`[<CustomOperation>]`), and Delay/Run, which
// only matter for laziness the checks here cannot observe.
module Core_custombuilder

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- an option builder -----------------------------------------------------

type OptionBuilder() =
    member _.Bind (x : 'a option, f : 'a -> 'b option) : 'b option =
        match x with
        | Some v -> f v
        | None -> None
    member _.Return (v : 'a) : 'a option = Some v
    member _.ReturnFrom (v : 'a option) : 'a option = v
    member _.Zero () : unit option = Some ()

let opt = OptionBuilder()

let addOpt (a : int option) (b : int option) : int option =
    opt {
        let! x = a
        let! y = b
        return x + y
    }

test "bind-both" (addOpt (Some 1) (Some 2) = Some 3)
test "bind-first-none" (addOpt None (Some 2) = None)
test "bind-second-none" (addOpt (Some 1) None = None)
test "single-return" (opt { return 7 } = Some 7)
test "return-from" (opt { return! Some 8 } = Some 8)
test "return-from-none" ((opt { return! (None : int option) }) = None)

// the bound value is the UNWRAPPED one, and the body may compute with it
let doubled (a : int option) : int option =
    opt {
        let! x = a
        return x * 2
    }

test "bind-then-compute" (doubled (Some 4) = Some 8)
test "bind-then-compute-none" (doubled None = None)

// a `let` beside a `let!` is an ordinary binding
let mixed (a : int option) : int option =
    opt {
        let! x = a
        let y = 10
        return x + y
    }

test "let-beside-bind" (mixed (Some 5) = Some 15)

// nesting one builder block inside another
let nested (a : int option) (b : int option) : int option =
    opt {
        let! x = a
        let! y =
            opt {
                let! v = b
                return v * 10
            }
        return x + y
    }

test "nested-blocks" (nested (Some 1) (Some 2) = Some 21)
test "nested-blocks-none" (nested (Some 1) None = None)

// ---- Bind runs the continuation exactly once -------------------------------

let mutable binds = 0

type CountingBuilder() =
    member _.Bind (x : 'a option, f : 'a -> 'b option) : 'b option =
        binds <- binds + 1
        match x with
        | Some v -> f v
        | None -> None
    member _.Return (v : 'a) : 'a option = Some v

let counting = CountingBuilder()

let twoBinds =
    counting {
        let! a = Some 1
        let! b = Some 2
        return a + b
    }

test "counting-result" (twoBinds = Some 3)
test "bind-called-per-let-bang" (binds = 2)

// a None short-circuits: the SECOND Bind never runs
let before = binds
let shortCircuit =
    counting {
        let! a = (None : int option)
        let! b = Some 2
        return a + b
    }

test "short-circuit-result" (shortCircuit = None)
test "short-circuit-stops-binding" (binds = before + 1)

// ---- a list builder: Combine, Yield, For, Zero ------------------------------

type ListBuilder() =
    member _.Yield (v : 'a) : 'a list = [ v ]
    member _.YieldFrom (vs : 'a list) : 'a list = vs
    member _.Combine (a : 'a list, b : 'a list) : 'a list = a @ b
    member _.Delay (f : unit -> 'a list) : 'a list = f ()
    member _.Zero () : 'a list = []
    member _.For (xs : 'a list, f : 'a -> 'b list) : 'b list = List.collect f xs

let lb = ListBuilder()

test "single-yield" (lb { yield 1 } = [ 1 ])
test "two-yields-combine" (lb { yield 1
                                yield 2 } = [ 1; 2 ])
test "yield-from" (lb { yield! [ 1; 2 ] } = [ 1; 2 ])
test "yield-and-yield-from" (lb { yield 0
                                  yield! [ 1; 2 ] } = [ 0; 1; 2 ])
test "for-over-list" (lb { for v in [ 1; 2; 3 ] do yield v * 2 } = [ 2; 4; 6 ])
test "for-with-yield-from" (lb { for v in [ 1; 2 ] do yield! [ v; v ] } = [ 1; 1; 2; 2 ])
test "empty-block-is-zero" (lb { () } = ([] : int list))

// a `for` whose body is conditional reaches Zero on the false side
test "for-with-if" (lb { for v in [ 1; 2; 3; 4 ] do
                           if v % 2 = 0 then yield v } = [ 2; 4 ])

// ---- the builder is an ordinary value ---------------------------------------

let useBuilder (b : OptionBuilder) (v : int) : int option = b { return v + 1 }
test "builder-passed-as-argument" (useBuilder opt 1 = Some 2)

// the head of the block may be COMPUTED, not just a name
let builders = [ OptionBuilder(); OptionBuilder() ]
let firstBuilder = List.head builders
test "builder-in-list" (firstBuilder { return 5 } = Some 5)
test "computed-builder-head" ((List.head builders) { return 5 } = Some 5)
test "computed-head-with-bind" ((List.head builders) { let! v = Some 3
                                                       return v } = Some 3)

// ---- the single-line `in` form ---------------------------------------------

// `let! x = e in body` on one line: the binder scopes over the body, and the
// body is a computation item too — a `return` there is the builder's Return,
// not a stray expression.
test "in-form-bind" (opt { let! v = Some 3 in return v * 10 } = Some 30)
test "in-form-return-from" (opt { let! v = Some 1 in return! Some (v * 5) } = Some 5)
test "in-form-chained" (opt { let! a = Some 1 in let! b = Some 2 in return a + b } = Some 3)
test "in-form-plain-let" (opt { let! a = Some 2
                                let b = 3 in return a + b } = Some 5)
test "in-form-plain-let-only" (opt { let b = 4 in return b } = Some 4)
test "in-form-none" (opt { let! v = (None : int option) in return v } = None)

printfn "DONE tests=%d failures=%d" ntests failures
