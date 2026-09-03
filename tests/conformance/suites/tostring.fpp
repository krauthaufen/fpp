// AN OVERRIDDEN ToString WINS, as it does in F# (KNOWN-ISSUES #8 from the
// fpp.base port). `string x` lowered straight to the Show class' `str`, which
// prints the structural form — so a type that overrides ToString printed its
// record shape from `string x` while `x.ToString ()` beside it answered
// correctly. Two spellings of one thing disagreeing is the shape to watch for.
//
// The override is an ordinary member, so the project-wide member index finds
// it by owner; a type WITHOUT one keeps the structural form, which is what the
// second half here pins.
module Core_tostring

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

[<Struct>]
type V2 =
    { X : float; Y : float }
    override v.ToString () = "[" + string v.X + ", " + string v.Y + "]"

let v = { X = 1.0; Y = 2.0 }

eq "string-uses-the-override" (string v) "[1, 2]"
eq "and-the-explicit-call-agrees" (v.ToString ()) (string v)

// a CLASS with an override, which needed a second fix: a class has no Show
// instance, so its `string c` was dropped from the table Lower routes by
// (an unsatisfied Show normally means "let the runtime walker do it") and it
// printed "?" while `c.ToString ()` beside it was right. A type that
// overrides ToString has an answer of its own and now keeps its entry.
type Named (n : string) =
    member _.N = n
    override _.ToString () = "<" + n + ">"

let c = Named "abc"
eq "class-override" (string c) "<abc>"
eq "class-override-agrees" (c.ToString ()) (string c)

// through a function whose parameter is the type, so the call site is not the
// declaration site
let show (x : V2) : string = string x
eq "override-through-a-parameter" (show { X = 3.0; Y = 4.0 }) "[3, 4]"

// a type WITHOUT an override keeps the structural form — the fix must not
// route everything through a member that is not there
[<Struct>]
type P = { A : int; B : int }
let p = { A = 1; B = 2 }
eq "no-override-keeps-the-structural-form" (string p) (sprintf "%A" p)

// a scalar is unaffected
eq "int-unaffected" (string 42) "42"
eq "float-unaffected" (string 1.5) "1.5"

printfn "DONE tests=%d failures=%d" ntests failures
