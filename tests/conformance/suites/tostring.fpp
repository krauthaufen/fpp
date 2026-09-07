// `ToString` ANSWERS FOR EVERY OBJECT, AND THE OVERRIDE WINS.
//
// A call through a receiver whose static type declares no ToString — an
// INTERFACE, typically — had nothing to resolve to: it type-checked, reached
// the backend unlowered, and TRAPPED when the line ran, with nothing reported
// even under `--strict`. That is how fpp.adaptive's `aval` values could not
// be printed at all (~/claude/fpp-base-snags.md #46), and it read as a
// scale-dependent bug because the same call on the concrete class worked.
//
// ToString is a universal object member now, like GetHashCode and Equals, and
// it is DYNAMIC: slot 3 of the class' vtable row, the same dispatch $cmpv
// uses for Equals and CompareTo. So the override runs whatever the static
// type of the receiver is.
//
// The second half of the same bug: `string x` on a GENERIC class ignored its
// override — the member index is keyed by the declared name and a use site
// records the INSTANTIATION (`Box$<int>`), so the lookup missed and the call
// fell through to a Show instance that does not exist.
module Core_tostring

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" name got want

type IShape =
    abstract member Area : unit -> int

type Sq(n : int) =
    interface IShape with
        member x.Area () = n * n
    override x.ToString () = "sq(" + string n + ")"

type Circle(r : int) =
    interface IShape with
        member x.Area () = 3 * r * r
    override x.ToString () = "circle(" + string r + ")"

let s = Sq 3
let c = Circle 2

// on the class itself
eq "on-the-concrete-class" (s.ToString ()) "sq(3)"
eq "string-of-the-concrete-class" (string s) "sq(3)"

// through the INTERFACE: the class' own override answers
let i = s :> IShape
eq "through-an-interface" (i.ToString ()) "sq(3)"

// and it is the RUNTIME type that decides, not the annotation
let shapes : IShape list = [ s :> IShape; c :> IShape ]
eq "dispatched-per-object" (String.concat "," (List.map (fun (x : IShape) -> x.ToString ()) shapes)) "sq(3),circle(2)"
eq "and-the-interface-member-still-works" (String.concat "," (List.map (fun (x : IShape) -> string (x.Area ())) shapes)) "9,12"

// a GENERIC class' override, through `string` and through the member
type Box<'T>(v : 'T) =
    member x.Value = v
    override x.ToString () = "box(" + string x.Value + ")"

let bi = Box 3
let bs = Box "s"
eq "generic-class-member" (bi.ToString ()) "box(3)"
eq "generic-class-string" (string bi) "box(3)"
eq "generic-class-at-a-reference" (string bs) "box(s)"

// a class with NO override keeps answering something rather than trapping
type Plain(n : int) =
    member x.N = n
let p = Plain 1
eq "no-override-still-answers" (if (p.ToString ()).Length > 0 then "yes" else "no") "yes"

printfn "DONE tests=%d failures=%d" ntests failures
