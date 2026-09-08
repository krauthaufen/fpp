// AN UPCAST TAKES ITS TYPE ARGUMENTS FROM THE CLASS.
//
// `C<'T>(v) :> IBox<_>` is an `IBox<'T>`: the class declares which
// instantiation of the interface it implements, and the wildcard follows it.
// The two used to be INDEPENDENT variables, which is how the adaptive port's
// `AVal.constant` came out `'a -> aval<'b>` — a value of it then fitted a
// parameter declared `aval<seq<_>>`, the overload was chosen on that lie, and
// the option inside was ENUMERATED at run time (~/claude/fpp-base-snags.md
// #48). `neg/upcast-wildcard-argument.fpp` holds the rejection; this file
// holds what must keep working.
module Core_upcastargs

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" name got want

type IBox<'a> =
    abstract member Get : unit -> 'a

type C<'T>(v : 'T) =
    member x.V = v
    interface IBox<'T> with
        member x.Get () = v

// the wildcard follows the class' own parameter
let mk (v : 'T) : IBox<_> = C<'T> v :> IBox<_>

let bi = mk 3
eq "an-int-box" (string (bi.Get ())) "3"
let bs = mk "s"
eq "a-string-box" (bs.Get ()) "s"
let bo = mk (Some 3)
eq "an-option-box" (match bo.Get () with Some n -> string n | None -> "-") "3"
let bl = mk [ 1; 2; 3 ]
eq "a-list-box" (string (List.length (bl.Get ()))) "3"

// the element the wildcard settled on is the ARGUMENT's, so an overload set
// picks by it — this is the shape the port's builder has
type Picker() =
    member x.Which (v : IBox<seq<int>>) : string = "seq"
    member x.Which (v : IBox<list<int>>) : string = "list"
    member x.Which (v : IBox<int option>) : string = "option"
    member x.Which (v : IBox<int>) : string = "plain"

let p = Picker()
eq "overload-by-the-elements-type" (p.Which (mk (Some 7))) "option"
eq "and-a-list" (p.Which (mk [ 1 ])) "list"
eq "and-a-plain-one" (p.Which (mk 1)) "plain"

// an explicit target still means what it says
let named : IBox<int option> = mk (Some 5)
eq "an-annotated-target" (match named.Get () with Some n -> string n | None -> "-") "5"

// a two-parameter class, upcast to a one-parameter interface: the mapping is
// the class' declaration, not position
type IKeyed<'k> =
    abstract member Key : unit -> 'k

type Pair<'k, 'v>(k : 'k, v : 'v) =
    member x.Value = v
    interface IKeyed<'k> with
        member x.Key () = k

let keyed (k : 'k) (v : 'v) : IKeyed<_> = Pair<'k, 'v> (k, v) :> IKeyed<_>
let kp = keyed "id" 42
eq "the-declared-mapping-not-position" (kp.Key ()) "id"

printfn "DONE tests=%d failures=%d" ntests failures
