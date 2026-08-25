// OPERATORS, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/BasicGrammarElements
// (OperatorNames, PrecedenceAndAssociativity) and the operator cases of
// ExpressionsAndTypes.
//
// The theme is that an operator is an ordinary function with a funny name:
// it can be DEFINED, shadowed, partially applied, passed as a value, and
// declared on a TYPE as `op_Addition`. Precedence and associativity come
// from the first character, not from the definition — `+.` binds like `+`
// whatever it does — so each case checks a value the wrong grouping gets
// wrong rather than a build error.
//
// DROPPED: `?` dynamic-lookup operators (no reflection here) and the
// bitwise-on-native-int cases that `unsigned` already covers.
module Core_operators

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- defining an operator -------------------------------------------------

let (+.) (a : float) (b : float) : float = a * 10.0 + b
let (^^) (a : int) (b : int) : int = a * a + b
let (|>>) (x : int) (f : int -> int) : int = f (f x)

test "custom-infix" (1.0 +. 2.0 = 12.0)
test "custom-infix-second" (3.0 +. 4.0 = 34.0)
test "custom-caret" (3 ^^ 1 = 10)
test "custom-pipe" (5 |>> (fun v -> v + 1) = 7)

// an operator used PREFIX by name is an ordinary function
test "operator-as-function" ((+.) 1.0 2.0 = 12.0)
test "operator-partial" (List.map ((+.) 1.0) [ 2.0; 3.0 ] = [ 12.0; 13.0 ])

// ---- precedence follows the FIRST character -------------------------------

// `+.` binds like `+`, so `*` still binds tighter
test "precedence-mul-over-custom-plus" (1.0 +. 2.0 * 3.0 = 16.0)
// `^^` starts with `^`: RIGHT associative, and LOOSER than `+` (the ladder
// puts the caret family below the arithmetic one), so `1 + 2 ^^ 3` groups as
// `(1 + 2) ^^ 3` and the chain nests to the right
test "precedence-caret-right-assoc" (2 ^^ 3 ^^ 1 = 14)
test "precedence-caret-under-plus" (1 + 2 ^^ 3 = 12)

// the built-in ladder, each checked by a value the wrong grouping changes
test "mul-over-add" (2 + 3 * 4 = 14)
test "sub-left-assoc" (10 - 3 - 2 = 5)
test "div-left-assoc" (100 / 5 / 2 = 10)
test "mod-same-as-mul" (7 + 10 % 4 = 9)
test "compare-under-add" (1 + 1 = 2)
test "and-over-or" (true || true && false)
test "not-over-and" (not false && true)

// unary minus binds tighter than binary
test "unary-minus" (0 - 3 * 2 = 0 - 6)
test "unary-minus-float" (0.0 - 2.5 * 2.0 = 0.0 - 5.0)

// ---- pipelines and composition --------------------------------------------

let addOne (v : int) : int = v + 1
let dbl (v : int) : int = v * 2

test "pipe-forward" (3 |> addOne = 4)
test "pipe-forward-chain" (3 |> addOne |> dbl = 8)
test "pipe-backward" (addOne <| 3 = 4)
test "compose-forward" ((addOne >> dbl) 3 = 8)
test "compose-backward" ((addOne << dbl) 3 = 7)
test "compose-is-associative" (((addOne >> dbl) >> addOne) 3 = (addOne >> (dbl >> addOne)) 3)

// `|>` is LEFT associative, so the chain reads left to right
test "pipe-left-assoc" ([ 1; 2; 3 ] |> List.map dbl |> List.sum = 12)

// ---- shadowing a built-in operator ----------------------------------------

let (+++) (a : int) (b : int) : int = a + b

let shadowed =
    // a LOCAL definition wins inside its scope, and only there
    let (+++) (a : int) (b : int) : int = a * b
    3 +++ 4

test "shadow-local" (shadowed = 12)
test "shadow-does-not-escape" (3 +++ 4 = 7)

// SHADOWING A BUILT-IN operator (`let (+) a b = a * b`) is NOT covered here:
// F++ keeps the built-in, see tests/known-issues/operator-shadow-builtin.fpp

// ---- operators on a TYPE --------------------------------------------------

type Vec2 =
    { X : float; Y : float }

    static member (+) (a : Vec2, b : Vec2) = { X = a.X + b.X; Y = a.Y + b.Y }
    static member (-) (a : Vec2, b : Vec2) = { X = a.X - b.X; Y = a.Y - b.Y }
    static member ( * ) (k : float, v : Vec2) = { X = k * v.X; Y = k * v.Y }

let va = { X = 1.0; Y = 2.0 }
let vb = { X = 3.0; Y = 5.0 }

test "type-operator-add" ((va + vb).X = 4.0 && (va + vb).Y = 7.0)
test "type-operator-sub" ((vb - va).X = 2.0)
test "type-operator-scale" ((2.0 * va).Y = 4.0)
test "type-operator-nested" (((va + vb) - va).X = 3.0)

// ---- comparison and equality operators ------------------------------------

test "eq-operator" (1 = 1 && not (1 = 2))
test "ne-operator" (1 <> 2)
test "lt-le" (1 < 2 && 2 <= 2)
test "gt-ge" (3 > 2 && 3 >= 3)
test "compare-chained-by-and" (1 < 2 && 2 < 3)
test "structural-eq-list" ([ 1; 2 ] = [ 1; 2 ])
test "structural-eq-tuple" ((1, "a") = (1, "a"))

// min/max are functions over the same ordering
test "min-max" (min 3 5 = 3 && max 3 5 = 5)
test "compare-function" (compare 1 2 < 0 && compare 2 2 = 0 && compare 3 2 > 0)

// ---- boolean operators short-circuit --------------------------------------

let mutable sideEffects = 0
let bump (b : bool) : bool =
    sideEffects <- sideEffects + 1
    b

test "and-short-circuits" (not (false && bump true))
test "and-short-circuit-count" (sideEffects = 0)
test "or-short-circuits" (true || bump true)
test "or-short-circuit-count" (sideEffects = 0)
test "and-evaluates-when-needed" (true && bump true)
test "and-count-after" (sideEffects = 1)

printfn "DONE tests=%d failures=%d" ntests failures
