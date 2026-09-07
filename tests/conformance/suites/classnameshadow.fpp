// A BINDING MAY TAKE A CLASS MEMBER'S NAME.
//
// The typeclass members here are bare names — `show`, `str`, `create`,
// `read`, `write`, `min`, `max`, `abs`, `compare`, `arbitrary` — and a class
// member's name is global, so a use in another file can only be recognized by
// name. That made the name the whole test, and every one of those is a name a
// program legitimately binds: a `let show` was taken for `Show.show`, and the
// call ran the INSTANCE body in place of the binding.
//
// `let show (x : 'a) = "v(" + string x + ")"` answered "7" for `show 7` — the
// literal parts simply gone, no diagnostic, and the bug reads as "generic
// string concatenation drops its literals" (which is how it was reported:
// ~/claude/fpp-base-snags.md #45). The definition a use resolves to now has
// to LIVE WHERE THE CLASS IS DECLARED before its name is read as a member.
//
// F# has no typeclasses, so under the oracle these are ordinary bindings —
// which is exactly the point: they must answer the same here.
module Core_classnameshadow

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" name got want

// the reported shape: a GENERIC binding named like a class member
let show (x : 'a) = "v(" + string x + ")"
eq "generic-let-named-show-int" (show 7) "v(7)"
eq "generic-let-named-show-string" (show "s") "v(s)"
eq "generic-let-named-show-float" (show 1.5) "v(1.5)"

// the control it was compared against: a concrete binding, name not a member
let show2 (x : int) = "w(" + string x + ")"
eq "the-concrete-control" (show2 9) "w(9)"

// the class' other member name, and one taking two arguments
let str (x : int) (y : int) = "s" + string (x + y)
eq "a-binding-named-str" (str 2 3) "s5"

// names from the numeric and IO classes
let create (n : int) : string = "created " + string n
eq "a-binding-named-create" (create 3) "created 3"
let read (s : string) : string = "read " + s
eq "a-binding-named-read" (read "f") "read f"
let write (s : string) : string = "wrote " + s
eq "a-binding-named-write" (write "f") "wrote f"
let arbitrary (n : int) : int = n * 2
eq "a-binding-named-arbitrary" (string (arbitrary 21)) "42"

// a binding that shadows a member whose class the program also USES: the
// binding answers for the name, and the operators keep dispatching
let compare (a : int) (b : int) : string = "cmp" + string (a - b)
eq "a-binding-named-compare" (compare 5 2) "cmp3"
eq "and-the-operators-still-work" (string (2 + 3) + " " + string (2.5 * 2.0)) "5 5"
eq "and-sorting-still-orders" (String.concat "," (List.map string (List.sort [ 3; 1; 2 ]))) "1,2,3"

// the same for a binding used through a HIGHER-ORDER position
let describe (f : int -> string) (n : int) : string = f n
eq "passed-as-a-value" (describe show 4) "v(4)"

// a generic binding named like a member, recursing on itself
let rec abs (n : int) : int = if n < 0 then abs (0 - n) else n
eq "a-recursive-binding-named-abs" (string (abs (0 - 8))) "8"

printfn "DONE tests=%d failures=%d" ntests failures
