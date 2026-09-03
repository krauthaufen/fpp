// BYREF PARAMETERS, ported from dotnet/fsharp's tests/fsharp/core/byrefs
// (the byref-of-primitive and byref-of-field cases) and the ByRef cases of
// Conformance/Expressions.
//
// `byref<'a>` is an ALIAS of a storage location, not a copy of its value. So
// what this suite checks is that a write through the alias is visible at the
// original, that reading through it sees writes made since, and that passing
// the same location twice aliases it twice. The `&x` at the call site is
// what takes the address; without it the value would be copied and every
// case here would answer the same as a by-value parameter.
//
// DROPPED: `inref`/`outref` (F# distinguishes them by attribute, and the
// read/write behaviour is the byref behaviour), byrefs to array elements
// and to struct fields taken across a call boundary (F# restricts where
// those may travel), and returning a byref — a scope rule, not a value one.
module Core_byrefs

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

// ---- a write through the alias reaches the original -------------------------

let bump (x : byref<int>) : unit = x <- x + 1

let mutable v = 1
bump &v
eq "written-through-the-alias" (string v) "2"
bump &v
bump &v
eq "written-repeatedly" (string v) "4"

let setTo (x : byref<int>, n : int) : unit = x <- n

let mutable w = 0
setTo (&w, 42)
eq "assigned-through-the-alias" (string w) "42"

// the alias READS the current value, not the one it was made from
let double1 (x : byref<int>) : unit = x <- x * 2

let mutable d = 5
double1 &d
eq "read-then-written" (string d) "10"
double1 &d
eq "read-sees-the-previous-write" (string d) "20"

// ---- by-value does NOT write back -------------------------------------------

let bumpCopy (x : int) : unit =
    let mutable y = x
    y <- y + 1

let mutable untouched = 1
bumpCopy untouched
eq "by-value-leaves-the-original" (string untouched) "1"

// the same function body, the two parameter modes side by side
let mutable byv = 10
let mutable byr = 10
bumpCopy byv
bump &byr
eq "the-two-modes-differ" (string byv + "/" + string byr) "10/11"

// ---- returning a value AND writing through the alias -------------------------

let takeAndReport (x : byref<int>) : string =
    let before = x
    x <- x * 3
    string before + "->" + string x

let mutable r = 4
eq "reports-both-sides" (takeAndReport &r) "4->12"
eq "and-the-write-stuck" (string r) "12"

// ---- SEVERAL byref parameters -----------------------------------------------

let swap (a : byref<int>, b : byref<int>) : unit =
    let t = a
    a <- b
    b <- t

let mutable p = 1
let mutable q = 2
swap (&p, &q)
eq "swapped-first" (string p) "2"
eq "swapped-second" (string q) "1"

// the SAME location passed twice is one location: the swap is a no-op
let mutable both = 7
swap (&both, &both)
eq "aliased-twice-is-one-location" (string both) "7"

// and a write through one alias is seen by the other
let addInto (a : byref<int>, b : byref<int>) : unit =
    a <- a + 1
    b <- b + 1

let mutable twice2 = 0
addInto (&twice2, &twice2)
eq "both-writes-hit-the-same-location" (string twice2) "2"

// ---- byrefs of other types ---------------------------------------------------

let appendTo (s : byref<string>) : unit = s <- s + "!"

let mutable str = "a"
appendTo &str
appendTo &str
eq "string-byref" str "a!!"

let flip (b : byref<bool>) : unit = b <- not b

let mutable flag = false
flip &flag
test "bool-byref" flag
flip &flag
test "bool-byref-back" (not flag)

let scale (f : byref<float>) : unit = f <- f * 2.0

let mutable fl = 1.5
scale &fl
eq "float-byref" (string fl) "3"

// a byref of a RECORD replaces the whole value, since the alias is of the
// binding, not of any field
type Pt = { X : int; Y : int }

let moveTo (p : byref<Pt>) : unit = p <- { X = 9; Y = 9 }

let mutable pt = { X = 1; Y = 2 }
moveTo &pt
eq "record-byref" (string pt.X + "," + string pt.Y) "9,9"

// a byref of a LIST, which is immutable — the alias still rebinds it
let consOnto (xs : byref<int list>) : unit = xs <- 0 :: xs

let mutable lst = [ 1; 2 ]
consOnto &lst
eq "list-byref" (String.concat "," (List.map string lst)) "0,1,2"

// ---- a byref threaded through a LOOP -----------------------------------------

let addAll (acc : byref<int>, xs : int list) : unit =
    for x in xs do acc <- acc + x

let mutable total = 0
addAll (&total, [ 1; 2; 3; 4 ])
eq "accumulated-through-a-byref" (string total) "10"

// and called repeatedly, so the accumulator carries across calls
addAll (&total, [ 10 ])
eq "accumulator-carries-across-calls" (string total) "20"

// a while loop that stops on the aliased value
let countDown (n : byref<int>) : int =
    let mutable steps = 0
    while n > 0 do
        n <- n - 1
        steps <- steps + 1
    steps

let mutable countdown = 3
eq "loop-reads-the-alias" (string (countDown &countdown)) "3"
eq "loop-left-it-at-zero" (string countdown) "0"

// ---- a byref of a LOCAL, not just a module-level mutable ---------------------

let localAlias () : string =
    let mutable inner = 1
    bump &inner
    bump &inner
    string inner

eq "byref-of-a-local" (localAlias ()) "3"

// each call has its OWN local, so the aliases do not collide
eq "locals-are-per-call" (localAlias () + localAlias ()) "33"

// a local passed down two levels
let bumpTwice (x : byref<int>) : unit =
    bump &x
    bump &x

let nested () : string =
    let mutable inner = 0
    bumpTwice &inner
    string inner

eq "byref-passed-through-two-levels" (nested ()) "2"

// ---- the ORDER of writes is the order of the statements ---------------------

let mutable trace = ""
let noteWrite (x : byref<int>, tag : string) : unit =
    trace <- trace + tag
    x <- x + 1

let mutable seqv = 0
noteWrite (&seqv, "a")
noteWrite (&seqv, "b")
noteWrite (&seqv, "c")
eq "writes-in-order" trace "abc"
eq "writes-all-landed" (string seqv) "3"

// ---- a write FOLLOWED by statements (the statement-position dispatch) ------
// the write lowered through the statement path, which bypassed the offset
// interception and stored through the tagged word into nowhere — the write
// VANISHED whenever anything followed it in the body

let growList (r : byref<int list>, n : int) : unit =
    r <- n :: r
    let mutable after = 0
    after <- after + 1
    ignore after

let statementWrite () : string =
    let mutable xs : int list = []
    growList (&xs, 7)
    growList (&xs, 8)
    string (List.length xs) + "/" + string (List.head xs)

eq "byref-write-then-statements" (statementWrite ()) "2/8"

// ---- allocation BEFORE the dispatch, through an array element --------------
// the callee churns first; the byref arrives as a view over an element (an
// unconvertible caller), so this pins the heap path with the collector
// moving things between entry and the write

let churnThenGrow (r : byref<int list>, n : int) : unit =
    let mutable churn : int list = []
    let mutable i = 0
    while i < 20 do
        churn <- i :: churn
        i <- i + 1
    ignore churn
    r <- n :: r

let viaElement () : string =
    let box = [| ([] : int list) |]
    let mutable i = 0
    while i < 200 do
        churnThenGrow (&box.[0], i)
        i <- i + 1
    string (List.length box.[0]) + "/" + string (List.head box.[0])

eq "byref-churn-into-element" (viaElement ()) "200/199"

// ---- a TUPLED byref callee -------------------------------------------------
// the byref is a PATTERN BINDER (`λ_arg. match _arg with (b, p) -> ...`) and
// the caller passes a literal tuple whose elements the backend spreads

let extendT (b : byref<float>, k : float) : unit =
    b <- b + k
    let mutable trail = 0
    trail <- trail + 1
    ignore trail

let tupledCalls () : string =
    let mutable acc = 1.5
    extendT (&acc, 2.0)
    extendT (&acc, 3.0)
    sprintf "%.1f" acc

eq "byref-tupled-callee" (tupledCalls ()) "6.5"

printfn "DONE tests=%d failures=%d" ntests failures
