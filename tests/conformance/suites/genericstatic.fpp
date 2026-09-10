// A GENERIC CLASS' `static let` RUNS SEPARATELY PER INSTANTIATION.
//
// In .NET the statics of a generic type belong to the CLOSED type, so
// `Box<int>` and `Box<string>` have their own. Lifted to a top-level binding
// they became ONE global, built at the canonical (obj) instantiation and
// shared by every stamp — so the counts below both read 3 where F# reads
// 2 and 1.
//
// The sharing was the visible half. The unsound half is that such a value
// CAPTURES its instantiation: fpp.adaptive's CountingHashSet holds
// `static let traceNoRefCount`, whose closures are ComputeDelta$obj and
// ApplyDeltaNoRefCount$obj, so a `cset<int>` ran canonical code over RAW
// ints and put an untagged key in a tagged cell — the collector then traced
// a small integer as a pointer and aborted. That was the fifth heap GC
// regression, and it was this bug.
//
// A static whose own TYPE mentions no parameter (`static let mutable n = 0`,
// the counting idiom) has no key of its own, and a reader like `static member
// Count = n` is `unit -> int`. Infer therefore gives a STATIC the class'
// parameters in its scheme — a static belongs to the CLOSED type — so the use
// records an instantiation and the member is stamped. Both shapes are below.
module GenericStatic

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" name got want

type Box<'T>() =
    static let mutable items : list<'T> = []
    static member Add (x : 'T) = items <- x :: items
    static member Items : list<'T> = items

Box<int>.Add 1
Box<int>.Add 2
Box<string>.Add "a"

eq "int-instantiation-keeps-its-own" (string (List.length Box<int>.Items)) "2"
eq "string-instantiation-keeps-its-own" (string (List.length Box<string>.Items)) "1"
eq "and-the-values-are-that-instantiation's" (string (List.head Box<int>.Items)) "2"
eq "not-the-other's" (List.head Box<string>.Items) "a"

// a THIRD instantiation, to catch a fix that merely splits obj from int
type Holder<'T>() =
    static let mutable last : list<'T> = []
    static member Put (x : 'T) = last <- [ x ]
    static member Get : list<'T> = last

Holder<int>.Put 7
Holder<float>.Put 1.5
Holder<string>.Put "z"
eq "three-instantiations-int" (string (List.head Holder<int>.Get)) "7"
eq "three-instantiations-float" (string (List.head Holder<float>.Get)) "1.5"
eq "three-instantiations-string" (List.head Holder<string>.Get) "z"

// THE COUNTING IDIOM: the static's own type mentions no parameter at all.
// This is what a per-instantiation counter looks like, and it is the shape
// that has no key except the class' own parameters.
type Counter<'T>() =
    static let mutable n = 0
    static member Bump () = n <- n + 1
    static member Count = n

Counter<int>.Bump ()
Counter<int>.Bump ()
Counter<string>.Bump ()
eq "counter-int" (string Counter<int>.Count) "2"
eq "counter-string" (string Counter<string>.Count) "1"
eq "counter-untouched-instantiation" (string Counter<bool>.Count) "0"

printfn "DONE tests=%d failures=%d" ntests failures
