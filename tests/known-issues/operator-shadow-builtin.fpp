// KNOWN ISSUE: a let-bound operator does NOT shadow the built-in one.
//
//   let (+) (a : int) (b : int) : int = a * b
//   3 + 4        // F# = 12 (the binding wins); F++ = 7 (the built-in wins)
//
// Shadowing a CUSTOM operator works — `let (++)` over an outer `let (++)`
// picks the inner one — so this is specific to the operators that have an
// arithmetic CLASS. Lower's binary-operator path takes the let-binding only
// when `Classes.operatorClass op.Text` is None, which excludes every
// arithmetic operator.
//
// Dropping that condition so a resolved let-binding always wins makes EVERY
// module fail to validate ("global.set value must have right type" in the
// module initialiser), so something is already registered under `(+)` as a
// DefLet and every ordinary `+` starts resolving to it. Whatever that is has
// to be understood before the guard can be relaxed — the prelude itself
// defines no operator as a let binding.
module OperatorShadowBuiltin

let (+) (a : int) (b : int) : int = a * b

printfn "%d" (3 + 4)   // F# prints 12, F++ prints 7
