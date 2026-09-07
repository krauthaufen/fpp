// PROPERTY ACCESSORS, and the `and` that follows them.
//
// `member x.P with get () = v and set nv = v <- nv` writes two accessors of
// one property, joined by `and` — and `type A = … and B = …` joins two types
// of one group with the SAME keyword. The accessor parser took every `and`,
// so a type declared after such a property was swallowed: the declaration
// after it was left behind as a stray expression, and the error landed on the
// declaration's own line ("unbound value 'cval'").
//
// The shape is the fpp.adaptive one — a changeable value with a settable
// Value, an abbreviation for it in the same group — and it is why a whole
// consumer file's constructions could not resolve (~/claude/fpp-base-snags.md
// #42).
module Core_propaccessors

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" name got want

type CV<'T>(value : 'T) =
    let mutable v = value
    member x.Value with get () = v and set (nv : 'T) = v <- nv
    member x.Doubled with get () = (v, v)
and cval<'T> = CV<'T>

// the abbreviation is a real type: constructible, and usable in an annotation
let c = cval 7
eq "constructed-through-the-abbreviation" (string c.Value) "7"
let annotated (x : cval<int>) : int = x.Value
eq "the-abbreviation-as-an-annotation" (string (annotated c)) "7"

// the setter really is a setter
let sets =
    c.Value <- 9
    ()
eq "the-set-accessor" (string c.Value) "9"

// a get-only property beside them
eq "a-get-only-property" (string (fst c.Doubled) + "," + string (snd c.Doubled)) "9,9"

// at a reference instantiation too
let s = cval "a"
let sets2 =
    s.Value <- "b"
    ()
eq "the-same-at-a-reference-type" s.Value "b"

// a THREE-member group whose middle member ends in a set accessor
type Holder(start : int) =
    let mutable n = start
    member x.N with get () = n and set (nv : int) = n <- nv
and Pair = { A : int; B : int }
and Wrapper(h : Holder) =
    member x.Inner = h

let h = Holder 1
let hset =
    h.N <- 5
    ()
let p = { A = 2; B = 3 }
let w = Wrapper h
eq "the-group-after-a-setter-still-declares" (string h.N + " " + string (p.A + p.B) + " " + string w.Inner.N) "5 5 5"

printfn "DONE tests=%d failures=%d" ntests failures
