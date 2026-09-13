// BOXING A GENERIC VALUE CAPTURED BY A CLOSURE.
//
// `box v` inside a lambda that CAPTURES a generic `v` handed back the raw
// scalar: `unbox<int>` then threw, because the value was never boxed. Boxing
// the same `v` directly worked, and so did boxing a captured `int` — only the
// combination failed, which is what made it look like a closure bug.
//
// Covers the instantiations that STAMP — int and the boxed scalars. bool,
// char, byte and the narrow ints stay CANONICAL (see `boxedScalar` in Link),
// where a scalar rides a TAGGED word and no static type distinguishes it from
// a pointer; boxing those needs the runtime witness, and
// tests/known-issues/box-canonical-tagged-scalar.fpp holds that repro.
//
// It was neither. A clone stamped at int specialized the BINDER to int and
// left every USE of it naming the declaration's `'a` (substBinderTypes walked
// binders, not uses). Most paths never ask — the value rides the register the
// binder decided — but `refKindOfExpr` asks the USE, and a lifted lambda's
// env slot holds a type-parameter capture as RAW storage. So `box` saw a type
// parameter, skipped, and returned the raw int.
module BoxGenericClosure

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" name got want

let direct (v : 'a) : obj = box v
let viaClosure (v : 'a) : unit -> obj = fun () -> box v
type Erased = { Identity : obj; Get : unit -> obj }
let erased (value : 'a) : Erased = { Identity = box value; Get = fun () -> box value }

eq "boxed directly" (string (unbox<int> (direct 2))) "2"
eq "boxed inside a closure" (string (unbox<int> ((viaClosure 3) ()))) "3"
eq "through a record field" (string (unbox<int> ((erased 4).Get ()))) "4"
eq "and the eagerly boxed field agrees" (string (unbox<int> ((erased 4).Identity))) "4"

// a float rides the same path (it stamps too, being a boxed scalar)
eq "a float" (string (unbox<float> ((viaClosure 1.5) ()))) "1.5"
// a REFERENCE element must still round-trip: boxing it is the identity
eq "a string" (unbox<string> ((viaClosure "s") ())) "s"
// and the type test must answer on the captured box, not on a raw word
eq "the box knows its type" (string (((viaClosure 7) ()) :? int)) "True"
eq "and rejects another" (string (((viaClosure 7) ()) :? string)) "False"

printfn "DONE tests=%d failures=%d" ntests failures
