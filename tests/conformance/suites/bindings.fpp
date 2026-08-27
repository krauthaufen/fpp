// BINDING EXPRESSIONS, ported from dotnet/fsharp's
// Conformance/Expressions/BindingExpressions (in01..in05, MutableLocals01,
// UpperBindingPattern, AmbigLetBinding) and the binding cases of
// tests/fsharp/core/libtest.
//
// A `let` binds a PATTERN, not just a name, and that is where the semantics
// live: which names a pattern introduces, what a later binding of the same
// name does to an earlier one, when the right-hand side runs, and what
// `mutable` changes. The destructuring forms are checked one per shape,
// because each is a separate path in the compiler and they have diverged
// from one another before.
//
// DROPPED: the ambiguity cases whose point is a WARNING, `let` bindings in
// class bodies (the members suite owns those), and the `use!`/`let!` forms,
// which belong to computation expressions.
module Core_bindings

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- `let ... in`: the binding scopes over the CONTINUATION ----------------

let chained = let a = 1 in let b = 2 in a + b
eq "let-in-chain" (string chained) "3"

let shadowedIn = let x = 1 in let x = x + 10 in x
eq "let-in-shadows-with-the-old-value" (string shadowedIn) "11"

let nestedIn = let a = (let b = 2 in b * 3) in a + 1
eq "let-in-nested-on-the-right" (string nestedIn) "7"

// the same written as a block, which means the same thing
let asBlock =
    let a = 1
    let b = 2
    a + b
eq "block-form" (string asBlock) "3"

// a binding used only by the next one
let staged =
    let raw = "  x  "
    let trimmed = raw.Trim ()
    trimmed + "!"
eq "staged-bindings" staged "x!"

// ---- SHADOWING -------------------------------------------------------------

let shadowSteps () : string =
    let v = 1
    let step1 = string v
    let v = v * 2
    let step2 = string v
    let v = v * 3
    step1 + step2 + string v

eq "each-shadow-sees-the-previous" (shadowSteps ()) "126"

// a shadow of a different TYPE is fine: it is a new binding
let retyped () : string =
    let v = 1
    let v = string v + "!"
    v

eq "shadow-may-change-type" (retyped ()) "1!"

// shadowing a FUNCTION
let shadowedFn () : string =
    let f (x : int) = x + 1
    let a = f 1
    let f (x : int) = x * 10
    string a + string (f 1)

eq "shadowed-function" (shadowedFn ()) "210"

// an inner scope's shadow does not escape it
let mutable outerSeen = ""
let scoped =
    let v = "outer"
    let inner () =
        let v = "inner"
        v
    outerSeen <- inner ()
    v

eq "inner-shadow-stays-inside" scoped "outer"
eq "and-the-inner-saw-its-own" outerSeen "inner"

// ---- the right-hand side runs ONCE, where it is written --------------------

let mutable trace = ""
let note (s : string) (v : int) : int =
    trace <- trace + s
    v

let ordered =
    let a = note "a" 1
    let b = note "b" 2
    let c = note "c" 3
    a + b + c

eq "right-hand-sides-in-order" trace "abc"
eq "and-their-values" (string ordered) "6"

// a binding never read still runs
trace <- ""
let unusedRuns =
    let _ = note "x" 0
    note "y" 1

eq "an-unread-binding-still-runs" trace "xy"
eq "unused-value" (string unusedRuns) "1"

// reading a binding many times does not re-run it
trace <- ""
let readTwice =
    let v = note "z" 5
    v + v

eq "read-twice-runs-once" trace "z"
eq "read-twice-value" (string readTwice) "10"

// ---- DESTRUCTURING, one form at a time -------------------------------------

// tuple
let (t1, t2) = (1, 2)
eq "tuple-destructure" (string (t1 + t2)) "3"

let (n1, (n2, n3)) = (1, (2, 3))
eq "nested-tuple-destructure" (string (n1 + n2 + n3)) "6"

let (m1, m2, m3) = (1, 2, 3)
eq "triple-destructure" (string (m1 + m2 + m3)) "6"

// a tuple of mixed types
let (label, count) = ("n", 4)
eq "mixed-tuple-destructure" (label + string count) "n4"

// list
let [ l1; l2 ] = [ 1; 2 ]
eq "list-destructure" (string (l1 + l2)) "3"

// cons
let (h :: tl) = [ 1; 2; 3 ]
eq "cons-head" (string h) "1"
eq "cons-tail" (string (List.length tl)) "2"

// ARRAY — the same shape as the list one, and the path that had to be added
// on BOTH sides (inference classified it as a simple binding while lowering
// destructured it, so one element gave a wrong value and two a type error)
let [| a1; a2 |] = [| 3; 4 |]
eq "array-destructure" (string (a1 + a2)) "7"

let [| only |] = [| 7 |]
eq "single-element-array-destructure" (string only) "7"

let [| s1; s2 |] = [| "x"; "y" |]
eq "array-destructure-of-strings" (s1 + s2) "xy"

// record
type Pt = { X : int; Y : int }

let { X = px; Y = py } = { X = 1; Y = 2 }
eq "record-destructure" (string (px + py)) "3"

// only SOME fields
let { X = onlyX } = { X = 9; Y = 0 }
eq "partial-record-destructure" (string onlyX) "9"

// `as` keeps the whole beside the parts
let (w1, w2) as whole = (1, 2)
eq "as-binds-the-parts" (string (w1 + w2)) "3"
eq "as-binds-the-whole" (string (fst whole + snd whole)) "3"

// a union case
type Wrapped = Wrap of int * string

let (Wrap (wn, ws)) = Wrap (5, "s")
eq "union-destructure" (string wn + ws) "5s"

// destructuring inside a FUNCTION parameter
let addPair (a : int, b : int) : int = a + b
eq "tuple-parameter" (string (addPair (1, 2))) "3"

let sumOfPt ({ X = x; Y = y } : Pt) : int = x + y
eq "record-parameter" (string (sumOfPt { X = 3; Y = 4 })) "7"

// and in a lambda
let viaLambda = List.map (fun (a, b) -> a + b) [ (1, 2); (3, 4) ]
eq "lambda-tuple-parameter" (String.concat "," (List.map string viaLambda)) "3,7"

// destructuring in a `for`
let mutable pairSum = 0
for (a, b) in [ (1, 2); (3, 4) ] do pairSum <- pairSum + a * b
eq "for-tuple-destructure" (string pairSum) "14"

// ---- `mutable` --------------------------------------------------------------

let counted () : string =
    let mutable n = 0
    n <- n + 1
    n <- n + 1
    string n

eq "mutable-local" (counted ()) "2"

// each call gets its own cell
eq "mutable-locals-are-per-call" (counted () + counted ()) "22"

// a mutable read inside a loop sees the writes
let accumulated () : string =
    let mutable acc = 0
    for i in 1 .. 4 do acc <- acc + i
    string acc

eq "mutable-accumulator" (accumulated ()) "10"

// a mutable of a reference type
let swapped () : string =
    let mutable s = "a"
    s <- s + "b"
    s <- s + "c"
    s

eq "mutable-string" (swapped ()) "abc"

// shadowing a mutable with an immutable, and back
let mixedMut () : string =
    let mutable v = 1
    v <- 2
    let v = v * 10
    string v

eq "immutable-shadow-of-a-mutable" (mixedMut ()) "20"

// a module-level mutable, written from a function
let mutable moduleLevel = 0
let bumpModuleLevel () : unit = moduleLevel <- moduleLevel + 1

bumpModuleLevel ()
bumpModuleLevel ()
eq "module-level-mutable" (string moduleLevel) "2"

// ---- `let rec` and `and` ----------------------------------------------------

let rec fact (n : int) : int = if n <= 1 then 1 else n * fact (n - 1)
eq "let-rec" (string (fact 5)) "120"

let rec isEven (n : int) : bool = if n = 0 then true else isOdd (n - 1)
and isOdd (n : int) : bool = if n = 0 then false else isEven (n - 1)

test "mutually-recursive-even" (isEven 8)
test "mutually-recursive-odd" (isOdd 7)
test "mutually-recursive-not-even" (not (isEven 7))

// a rec group INSIDE a function
let localRec (n : int) : int =
    let rec go (i : int) (acc : int) : int =
        if i > n then acc else go (i + 1) (acc + i)
    go 1 0

eq "local-let-rec" (string (localRec 4)) "10"

// ---- a binding whose value is a FUNCTION -----------------------------------

let adder = fun (a : int) (b : int) -> a + b
eq "lambda-binding" (string (adder 1 2)) "3"

let partiallyApplied = adder 10
eq "partial-application-binding" (string (partiallyApplied 5)) "15"

// a closure captures the binding, not a copy of the scope
let makeAdder (n : int) : (int -> int) = fun v -> v + n
let add3 = makeAdder 3
let add10 = makeAdder 10
eq "closures-capture-separately" (string (add3 1) + "," + string (add10 1)) "4,11"

// a closure over a MUTABLE sees later writes
let capturing () : string =
    let mutable v = 1
    let read () = v
    v <- 99
    string (read ())

eq "closure-over-a-mutable" (capturing ()) "99"

// ---- an UPPERCASE binder is still a binder in a `let` ----------------------
// The rule that an uppercase name in a pattern is a union case applies to
// MATCH clauses only; a let, a parameter and a `for` bind whatever name they
// are given.

let Upper = 5
eq "uppercase-let-binder" (string Upper) "5"

let withUpperParam (Value : int) : int = Value * 2
eq "uppercase-parameter" (string (withUpperParam 4)) "8"

let mutable upperLoopSum = 0
for I in 1 .. 3 do upperLoopSum <- upperLoopSum + I
eq "uppercase-loop-binder" (string upperLoopSum) "6"

// ---- type ANNOTATIONS on a binding -----------------------------------------

let annotated : int = 5
let annotatedFn (v : int) : string = string v
let annotatedGeneric : int list = []

eq "annotated-value" (string annotated) "5"
eq "annotated-function" (annotatedFn 7) "7"
eq "annotated-empty-list" (string (List.length annotatedGeneric)) "0"

// the annotation decides an otherwise ambiguous literal
let asFloat : float = 2.0
let asFloat32 : float32 = 2.0f
eq "annotated-float" (string asFloat) "2"
eq "annotated-float32" (string asFloat32) "2"

printfn "DONE tests=%d failures=%d" ntests failures
