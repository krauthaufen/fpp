// OPTIONAL PARAMETERS, positionally filled.
//
// `member x.M (n : int, ?flag : bool, ?other : bool)` may be called with the
// optionals left off, or with some of them given POSITIONALLY — F# wraps each
// written value in `Some` and passes `None` for the rest. With ONE optional
// declared that worked; with TWO, giving one of them failed to type at all
// ("type mismatch: Option<bool> vs bool"), because the path that fills an
// OMITTED optional had its wrap test negated — and that path is the only one
// a call with something left off can take.
//
// It cost fpp.dom a donor spelling and read as an overload-resolution bug,
// since the shape it was found on was overloaded (~/claude/fpp-base-snags.md
// #50). Overloading is incidental: the plain member below fails the same way.
module Core_optionalargs

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" name got want

let showOpt (o : bool option) : string =
    match o with
    | Some true -> "T"
    | Some false -> "F"
    | None -> "-"

type T() =
    member x.M (n : int, ?flag : bool, ?other : bool) : string =
        string n + showOpt flag + showOpt other
    member x.One (n : int, ?flag : bool) : string = string n + showOpt flag
    // an optional that is not the last parameter's neighbour: three of them
    member x.Three (n : int, ?a : bool, ?b : bool, ?c : bool) : string =
        string n + showOpt a + showOpt b + showOpt c

let t = T()

eq "none-given" (t.M 1) "1--"
eq "one-of-two-given" (t.M (1, true)) "1T-"
eq "both-given" (t.M (1, true, false)) "1TF"
eq "one-optional-declared" (t.One (2, true)) "2T"
eq "one-optional-omitted" (t.One 2) "2-"
eq "three-none" (t.Three 3) "3---"
eq "three-one" (t.Three (3, true)) "3T--"
eq "three-two" (t.Three (3, true, false)) "3TF-"
eq "three-all" (t.Three (3, true, false, true)) "3TFT"

// NAMED optionals, and a named one after a positional one
eq "named-optional" (t.M (1, flag = true)) "1T-"
eq "named-second-optional" (t.M (1, other = true)) "1-T"
eq "positional-then-named" (t.M (1, true, other = false)) "1TF"

// `?flag = e` passes the OPTION through rather than wrapping it
let someTrue : bool option = Some true
eq "option-passed-through" (t.M (1, ?flag = someTrue)) "1T-"
eq "none-passed-through" (t.M (1, ?flag = None)) "1--"

// the same shapes on an OVERLOADED member, which is how it was reported
type U() =
    member x.M (cb : int -> bool, ?flag : bool, ?other : bool) : string =
        "bool" + showOpt flag
    member x.M (cb : int -> unit, ?flag : bool, ?other : bool) : string =
        "unit" + showOpt flag
let u = U()
eq "overloaded-one-of-two" (u.M ((fun n -> true), true)) "boolT"
eq "overloaded-none" (u.M (fun n -> true)) "bool-"

printfn "DONE tests=%d failures=%d" ntests failures
