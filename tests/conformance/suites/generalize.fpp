// GENERALIZATION AND THE VALUE RESTRICTION, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/InferenceProcedures
// (Generalization, TypeInference) and the inference cases of core/innerpoly.
//
// A binding generalizes at its `let`: after that it can be used at several
// types in the same program. What decides whether it may is SYNTACTIC — a
// function or a syntactic value generalizes, a parameterless binding whose
// right-hand side computes does not (the value restriction), and a mutable
// one never does. The checks are all "used at two types in one expression",
// because that is the only thing generalization is FOR.
//
// DROPPED: the error cases (`E_*` in the original: a value-restriction
// failure is a compile error, and the negative gate owns those), explicit
// `'T` annotations on members of a generic class, and statically resolved
// type parameters beyond the one inline case below.
module Core_generalize

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

// ---- a function generalizes at its binding ---------------------------------

let ident x = x

eq "identity-at-int" (string (ident 1)) "1"
eq "identity-at-string" (ident "a") "a"
eq "identity-at-bool" (string (ident true)) "True"
eq "identity-at-list" (string (List.length (ident [ 1; 2 ]))) "2"

let pair x y = (x, y)

eq "pair-at-int-char" (string (pair 1 'c')) "(1, c)"
eq "pair-at-string-bool" (string (pair "a" true)) "(a, True)"

// the two uses are in ONE expression, so one instantiation cannot serve both
eq "two-instantiations-in-one-expression" (ident "a" + string (ident 1)) "a1"

let compose f g x = f (g x)
eq "compose" (string (compose (fun v -> v + 1) (fun v -> v * 2) 5)) "11"
eq "compose-across-types" (compose string (fun (v : int) -> v * 2) 5) "10"

// a lambda BOUND to a name generalizes the same way
let konst = fun x -> fun _ -> x
eq "lambda-binding-at-int" (string (konst 1 "z")) "1"
eq "lambda-binding-at-string" (konst "a" 2) "a"

// ---- what does NOT generalize ------------------------------------------------

// an ANNOTATED binding is exactly as general as it says
let intIdent (x : int) : int = x
eq "annotated-is-monomorphic" (string (intIdent 3)) "3"

// a MUTABLE binding never generalizes: its cell is one location
let mutable held = 0
held <- 5
eq "mutable-binding" (string held) "5"

// a parameterless binding whose right-hand side COMPUTES stays at one type
let computed : int list = List.filter (fun v -> v > 1) [ 1; 2; 3 ]
eq "expansive-binding" (string (List.length computed)) "2"

// a syntactic VALUE does generalize — `None` and `[]` are usable at any type
let nothing = None
eq "syntactic-value-at-int" (string (nothing : int option)) ""
eq "syntactic-value-at-string" (string (nothing : string option)) ""
test "syntactic-value-is-none" (Option.isNone (nothing : int option))

let emptyList = []
eq "empty-list-at-int" (string (List.length (emptyList : int list))) "0"
eq "empty-list-at-string" (string (List.length (emptyList : string list))) "0"

// ---- generalization inside a nested let ------------------------------------

// `inner` generalizes even though it is local, so it serves both uses
let bothWays (v : int) : string =
    let inner x = x
    string (inner v) + inner "s"

eq "nested-binding-generalizes" (bothWays 1) "1s"

// a local binding that CAPTURES stays tied to what it captured
let capturing (n : int) : int =
    let add v = v + n
    add (add 0)

eq "capturing-local" (string (capturing 3)) "6"

// ---- a generic function passed as an argument ------------------------------

let applyTwice (g : int -> int) (v : int) : int = g (g v)
eq "generic-passed-at-int" (string (applyTwice ident 4)) "4"

let applyToBoth (g : 'a -> 'a) (a : 'a) (b : 'a) : 'a * 'a = (g a, g b)
eq "generic-parameter-used-twice" (string (applyToBoth ident 1 2)) "(1, 2)"
eq "generic-parameter-at-string" (string (applyToBoth ident "x" "y")) "(x, y)"

// ---- generic recursion -------------------------------------------------------

let rec mapAll (f : 'a -> 'b) (xs : 'a list) : 'b list =
    match xs with
    | [] -> []
    | x :: rest -> f x :: mapAll f rest

eq "generic-recursion-ints" (string (mapAll (fun v -> v + 1) [ 1; 2 ])) "[2; 3]"
eq "generic-recursion-strings" (string (mapAll (fun (s : string) -> s.Length) [ "ab"; "c" ])) "[2; 1]"

let rec depth (xs : 'a list list) : int =
    match xs with
    | [] -> 0
    | x :: rest ->
        let here = List.length x
        let there = depth rest
        if here > there then here else there

eq "generic-recursion-nested" (string (depth [ [ 1; 2 ]; [ 3 ] ])) "2"
eq "generic-recursion-nested-strings" (string (depth [ [ "a" ] ])) "1"

// ---- a written type parameter is RIGID inside the body ----------------------

// the body has to work for EVERY instantiation, so it may not decide that
// 'a is int — it can only pass the value through
let passThrough (x : 'a) : 'a list = [ x ]

eq "rigid-parameter-at-int" (string (List.length (passThrough 1))) "1"
eq "rigid-parameter-at-string" (string (List.head (passThrough "s"))) "s"

let swap (p : 'a * 'b) : 'b * 'a =
    let (a, b) = p
    (b, a)

eq "swap-int-string" (string (swap (1, "a"))) "(a, 1)"
eq "swap-string-bool" (string (swap ("a", true))) "(True, a)"

// two parameters that could be one, but are not
let firstOf (a : 'a) (_ : 'b) : 'a = a
eq "two-parameters-stay-two" (string (firstOf 1 "s")) "1"
eq "two-parameters-other-way" (firstOf "s" 1) "s"

// ---- generic data through generic functions ---------------------------------

type Box<'a> = { Item : 'a }

let boxUp (v : 'a) : Box<'a> = { Item = v }
let unbox2 (b : Box<'a>) : 'a = b.Item

eq "generic-record-int" (string (unbox2 (boxUp 5))) "5"
eq "generic-record-string" (unbox2 (boxUp "s")) "s"
eq "generic-record-nested" (string (unbox2 (unbox2 (boxUp (boxUp 7))))) "7"

type Pair<'a, 'b> =
    | Both of 'a * 'b
    | Neither

let describe (p : Pair<'a, 'b>) : string =
    match p with
    | Both _ -> "both"
    | Neither -> "neither"

eq "generic-union-int-string" (describe (Both (1, "a"))) "both"
eq "generic-union-other" (describe (Neither : Pair<int, int>)) "neither"

// ---- an inline binding resolves per USE --------------------------------------

let inline twice (v : ^a) = v + v

eq "inline-at-int" (string (twice 2)) "4"
eq "inline-at-float" (string (twice 1.5)) "3"
eq "inline-at-string" (twice "ab") "abab"

// ---- the annotation decides an otherwise ambiguous literal -------------------

let asFloat : float = 1.0
let asFloat32 : float32 = 1.0f
let asInt64 : int64 = 1L

eq "annotated-float" (string asFloat) "1"
eq "annotated-float32" (string asFloat32) "1"
eq "annotated-int64" (string asInt64) "1"

// the same literal in two annotated positions
let widthOf (v : float) : string = string v
let countOf (v : int) : string = string v
eq "literal-as-float" (widthOf 2.0) "2"
eq "literal-as-int" (countOf 2) "2"

// ---- a builtin CONVERSION used as a value ----------------------------------
// `string` and `int` are emitted at their application, so passing one as a
// function has to eta-expand it. The source type comes from the call.

eq "conversion-as-argument" (String.concat "," (List.map string [ 1; 2 ])) "1,2"
eq "conversion-of-floats" (String.concat "," (List.map string [ 1.5; 2.5 ])) "1.5,2.5"
eq "conversion-of-bools" (String.concat "," (List.map string [ true; false ])) "True,False"
eq "conversion-of-chars" (String.concat "," (List.map string [ 'a'; 'b' ])) "a,b"
eq "conversion-of-int64" (String.concat "," (List.map string [ 1L; 2L ])) "1,2"
eq "conversion-parsing" (string (List.sum (List.map int [ "1"; "2" ]))) "3"
eq "conversion-piped" (5 |> string) "5"
eq "conversion-piped-parse" (string ("7" |> int)) "7"
eq "conversion-over-an-array" (String.concat "," (Array.toList (Array.map string [| 1; 2 |]))) "1,2"
eq "conversion-composed" (compose string (fun (v : int) -> v * 2) 5) "10"

printfn "DONE tests=%d failures=%d" ntests failures
