// A MEMBER MAY BE WRITTEN ABOVE THE CONSTRUCTOR IT CALLS.
//
// A type's members are typed where they stand, and the constructor was
// registered only when its own declaration was reached — so a static above
// an explicit `new(...)` found NO constructor and its body's type stayed a
// free VARIABLE. Nothing said so: the member then fitted every annotation
// (`let n : int = Tok.Top` was accepted, and printed a pointer as a number),
// and cross-file the use reached the backend as an unknown, which only
// `--strict` mentions.
//
// The shape is not exotic — it is how fpp.adaptive writes AdaptiveToken
// (`static member Top = AdaptiveToken(Unchecked.defaultof<_>)` above
// `internal new(caller)`), and it is what made fpp.rendering's scene.fpp
// fail to compile as separate files while the concatenated build was fine.
// Every type predeclares its constructors now, as an `and`-chained one
// already did.
module Core_staticbeforector

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" name got want

// the static is written ABOVE the constructor it calls
type Tok =
    val mutable n : int
    static member Top = Tok(7)
    static member OfInt (v : int) = Tok(v)
    member x.N = x.n
    new (n : int) = { n = n }

let top = Tok.Top
eq "a-static-above-its-ctor" (string top.N) "7"
eq "and-a-static-method" (string (Tok.OfInt 3).N) "3"

// a member calling a LATER `new` overload, and the overload picked by arity
type Pair =
    val mutable a : int
    val mutable b : int
    static member Diag (v : int) = Pair(v, v)
    static member Zero = Pair()
    member x.Sum = x.a + x.b
    new (a : int, b : int) = { a = a; b = b }
    new () = { a = 0; b = 0 }

eq "a-later-overload-by-arity" (string (Pair.Diag 4).Sum) "8"
eq "and-the-nullary-one" (string Pair.Zero.Sum) "0"

// a GENERIC type, whose predeclared constructor must carry the declaration's
// own parameters — an inline constraint (`when 'a : comparison`) names a
// class, not a parameter, and counting it gave the type the wrong arity
type Box<'a when 'a : comparison> =
    val mutable v : 'a
    static member Of (x : 'a) = Box<'a>(x)
    member x.V = x.v
    new (v : 'a) = { v = v }

eq "a-generic-type-at-int" (string (Box<int>.Of 5).V) "5"
eq "and-at-string" ((Box<string>.Of "s").V) "s"

// a PRIMARY-constructor class: the static is above every member, and the
// constructor is the declaration's own parameter list
type Counter(start : int) =
    static member FromZero = Counter(0)
    member x.Start = start

eq "a-primary-ctor-class" (string Counter.FromZero.Start) "0"

printfn "DONE tests=%d failures=%d" ntests failures
