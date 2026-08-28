// TYPE-DIRECTED CONVERSION, ported from dotnet/fsharp's
// tests/fsharp/core/auto-widen (5.0, minimal, preview) — the
// BasicTypeDirectedConversionsTo* modules.
//
// Where the target type is KNOWN, F# inserts the conversion rather than
// demanding it be written: an annotation, a function's declared return, a
// record field, a collection whose element type is fixed, a parameter. The
// conversion that matters here is widening to a SUPERTYPE — to `obj`, to a
// base class, to an interface, to `seq`.
//
// The reason a whole suite is worth it: each of those positions is a
// separate place in the compiler that has to ask for subsumption rather
// than plain unification, and they were fixed one at a time. A position
// that regresses does not fail loudly — it simply demands `box` again.
//
// DROPPED: numeric widening (`let x : float = 1`), which F# allows only for
// method arguments and op_Implicit, not for a `let` annotation; and the
// `:> obj` cases that are explicit rather than inserted.
module Core_autowiden

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

// ---- to `obj`, at an ANNOTATION ---------------------------------------------

let asObjInt : obj = 1
let asObjString : obj = "s"
let asObjBool : obj = true
let asObjFloat : obj = 1.5
let asObjChar : obj = 'c'

test "int-to-obj" (asObjInt :? int)
test "string-to-obj" (asObjString :? string)
test "bool-to-obj" (asObjBool :? bool)
test "float-to-obj" (asObjFloat :? float)
test "char-to-obj" (asObjChar :? char)

// and the value survives the trip
eq "int-round-trip" (string (asObjInt :?> int)) "1"
eq "string-round-trip" (asObjString :?> string) "s"
eq "float-round-trip" (string (asObjFloat :?> float)) "1.5"

// the type test says NO to the wrong type
test "obj-is-not-a-string" (not (asObjInt :? string))
test "obj-is-not-an-int" (not (asObjString :? int))

// DROPPED: `let x : obj = 2 * 3`. F# refuses to widen an ARITHMETIC
// expression — the upstream file says why, in its own words: "these do NOT
// permit type-directed subsumption nor widening because a generic return
// type is involved". F++ accepts it, which is more permissive than F# rather
// than wrong, but it cannot be pinned against the oracle.

// a call's result, whose type is concrete, does widen
let fromACall : obj = string 42
eq "call-result-to-obj" (fromACall :?> string) "42"

// ---- to `obj`, at a declared RETURN ------------------------------------------

let returnsObj () : obj = 1
let returnsObjString () : obj = "s"
// (an arithmetic body is the dropped case above, so this one takes a value)
let returnsObjOf (v : int) : obj = v

test "return-to-obj" ((returnsObj ()) :? int)
eq "return-value" (string ((returnsObj ()) :?> int)) "1"
eq "return-string" ((returnsObjString ()) :?> string) "s"
eq "return-passed-through" (string ((returnsObjOf 5) :?> int)) "5"

// a LAMBDA's return, through an annotated binding
let lambdaToObj : unit -> obj = fun () -> 1
test "lambda-return-to-obj" ((lambdaToObj ()) :? int)

// ---- to `obj`, at a PARAMETER -------------------------------------------------

// NOT bool: the 32-bit scalars share one class id here, so a boxed bool
// answers `:? int` too (DIVERGENCES.md). Only types that are distinguishable
// in BOTH languages are asked about.
let describe (o : obj) : string =
    if o :? string then "string"
    elif o :? int then "int"
    elif o :? float then "float"
    else "other"

eq "argument-int" (describe 1) "int"
eq "argument-string" (describe "s") "string"
eq "argument-float" (describe 1.5) "float"

// through a pipe
eq "piped-argument" (1 |> describe) "int"

// ---- to `obj`, inside a TUPLE -------------------------------------------------

let pair : obj * obj = (1, "s")
test "tuple-first-to-obj" (fst pair :? int)
test "tuple-second-to-obj" (snd pair :? string)
eq "tuple-values" (string (fst pair :?> int) + (snd pair :?> string)) "1s"

let triple : obj * obj * obj = (1, "s", true)
let (t1, t2, t3) = triple
eq "triple-values" (string (t1 :?> int) + (t2 :?> string) + string (t3 :?> bool)) "1sTrue"

// ---- to `obj`, in a RECORD field ----------------------------------------------

type Holder = { Value : obj; Label : string }

let h = { Value = 5; Label = "five" }
test "record-field-to-obj" (h.Value :? int)
eq "record-field-value" (string (h.Value :?> int)) "5"
eq "the-other-field" h.Label "five"

let h2 = { h with Value = "now a string" }
test "copy-and-update-to-obj" (h2.Value :? string)
eq "copy-and-update-value" (h2.Value :?> string) "now a string"

// a record of several obj fields
type Row = { A : obj; B : obj }
let r = { A = 1; B = "x" }
eq "two-obj-fields" (string (r.A :?> int) + (r.B :?> string)) "1x"

// ---- to `obj`, as a collection ELEMENT ----------------------------------------

let objList : obj list = [ 1; 2; 3 ]
eq "obj-list-length" (string (List.length objList)) "3"
test "obj-list-elements" (List.forall (fun (o : obj) -> o :? int) objList)
eq "obj-list-values" (String.concat "," (List.map (fun (o : obj) -> string (o :?> int)) objList)) "1,2,3"

// a MIXED list, which is the point of obj
let mixed : obj list = [ 1; "s"; 2.5 ]
eq "mixed-list-length" (string (List.length mixed)) "3"
eq "mixed-list-described" (String.concat "," (List.map describe mixed)) "int,string,float"

let objArray : obj[] = [| 1; "s" |]
eq "obj-array-length" (string objArray.Length) "2"
test "obj-array-first" (objArray.[0] :? int)
test "obj-array-second" (objArray.[1] :? string)

// ---- to a BASE CLASS -----------------------------------------------------------

type Animal(name : string) =
    member _.Name = name
    abstract Sound : unit -> string
    default _.Sound () = "..."

type Dog() =
    inherit Animal("dog")
    override _.Sound () = "woof"

// at an annotation
let asBase : Animal = Dog ()
eq "derived-to-base-annotation" (asBase.Sound ()) "woof"
eq "base-member-through-it" asBase.Name "dog"

// at a return
let makeAnimal () : Animal = Dog ()
eq "derived-to-base-return" ((makeAnimal ()).Sound ()) "woof"

// at a parameter
let soundOf (a : Animal) : string = a.Sound ()
eq "derived-to-base-argument" (soundOf (Dog ())) "woof"

// in a list
let zoo : Animal list = [ Dog (); Animal "cat" ]
eq "derived-in-a-base-list" (String.concat "," (List.map (fun (a : Animal) -> a.Sound ()) zoo)) "woof,..."

// in a record field
type Pen = { Occupant : Animal }
let pen = { Occupant = Dog () }
eq "derived-in-a-record-field" (pen.Occupant.Sound ()) "woof"

// ---- to an INTERFACE ------------------------------------------------------------

type INamed =
    abstract GetName : unit -> string

type Person(n : string) =
    interface INamed with
        member _.GetName () = n

let asIface : INamed = Person "ann"
eq "class-to-interface-annotation" (asIface.GetName ()) "ann"

let makeNamed () : INamed = Person "bo"
eq "class-to-interface-return" ((makeNamed ()).GetName ()) "bo"

let nameOf (x : INamed) : string = x.GetName ()
eq "class-to-interface-argument" (nameOf (Person "cy")) "cy"

let named : INamed list = [ Person "a"; Person "b" ]
eq "class-to-interface-list" (String.concat "," (List.map (fun (x : INamed) -> x.GetName ()) named)) "a,b"

// ---- to `seq` --------------------------------------------------------------------

let asSeqFromList : seq<int> = [ 1; 2; 3 ]
eq "list-to-seq" (string (Seq.length asSeqFromList)) "3"
eq "list-to-seq-sum" (string (Seq.sum asSeqFromList)) "6"

let asSeqFromArray : seq<int> = [| 4; 5 |]
eq "array-to-seq" (string (Seq.length asSeqFromArray)) "2"
eq "array-to-seq-sum" (string (Seq.sum asSeqFromArray)) "9"

let takesSeq (xs : seq<int>) : int = Seq.sum xs
eq "list-argument-to-seq" (string (takesSeq [ 1; 2 ])) "3"
eq "array-argument-to-seq" (string (takesSeq [| 3; 4 |])) "7"

let returnsSeq () : seq<int> = [ 1; 2; 3 ]
eq "list-return-to-seq" (string (Seq.length (returnsSeq ()))) "3"

// ---- what must still be REJECTED -------------------------------------------------
// DROPPED: `let x : int = "s"` and an int in a `string list`. Widening does
// not make unrelated types compatible, and the negative gate owns the proof.

// a value that is ALREADY the target type is unaffected
let plainInt : int = 1
let plainList : int list = [ 1; 2 ]
eq "no-widening-needed-int" (string plainInt) "1"
eq "no-widening-needed-list" (string (List.sum plainList)) "3"

printfn "DONE tests=%d failures=%d" ntests failures
