// Replaces FSharp.Data.Adaptive's ShallowEquality.fs.
//
// The original decides, per type and AT RUN TIME, which comparison a type
// gets, and emits it as IL through DynamicMethod. It is the one place in the
// library that cannot be ported: there is no reflection here and nothing to
// emit into. The DECISION it makes, though, is a compile-time one, and a
// typeclass with overlapping instances is exactly that decision expressed in
// the language:
//
//   * a reference type compares by IDENTITY (`Object.ReferenceEquals`) —
//     this is the general instance, and it is what "shallow" means: the
//     comparison never follows a reference
//   * a primitive compares by VALUE — the original reaches these through
//     `isUnmanaged`, which is true for every one of them
//   * a struct compares FIELD-WISE, one level deep, each field by its own
//     shallow comparison — an instance per struct type, which is what the
//     original builds with `MakeGenericType` per field
//
// The more specific instance wins, so adding a type to the value-compared
// set is one instance declaration and nothing else.

/// The comparison the original picks per type, picked here per instance.
[<AutoOpen>]
class ShallowEquality<'a>
    static shallowEquals : 'a -> 'a -> bool
    static shallowHash : 'a -> int

/// The general case: a reference type is compared by identity, spelled the
/// way the original spells it. The hash only has to AGREE with equality —
/// equal values must hash equally, unequal ones may collide — and `hash` on
/// a class that declares no GetHashCode is already the identity hash the
/// original uses.
instance ShallowEquality<'a>
    static shallowEquals a b = System.Object.ReferenceEquals (a, b)
    static shallowHash a = hash a

// The unmanaged types. `isUnmanaged` is true for every primitive in the
// original — enums and blittable structs — so each compares by value.
instance ShallowEquality<int>
    static shallowEquals a b = a = b
    static shallowHash a = hash a
instance ShallowEquality<int64>
    static shallowEquals a b = a = b
    static shallowHash a = hash a
instance ShallowEquality<uint32>
    static shallowEquals a b = a = b
    static shallowHash a = hash a
instance ShallowEquality<byte>
    static shallowEquals a b = a = b
    static shallowHash a = hash a
instance ShallowEquality<sbyte>
    static shallowEquals a b = a = b
    static shallowHash a = hash a
instance ShallowEquality<float>
    static shallowEquals a b = a = b
    static shallowHash a = hash a
instance ShallowEquality<float32>
    static shallowEquals a b = a = b
    static shallowHash a = hash a
instance ShallowEquality<bool>
    static shallowEquals a b = a = b
    static shallowHash a = hash a
instance ShallowEquality<char>
    static shallowEquals a b = a = b
    static shallowHash a = hash a

// NOT string: in .NET a string is a reference type, so the original compares
// it by identity too. Leaving it to the general instance is the faithful
// choice, not an omission.

/// The surface the rest of the library calls. `Set` is absent because
/// nothing in the library calls it — the comparison is settled at compile
/// time now, and a run-time override would have nothing to override.
/// The three entry points the rest of the library uses, as functions: a
/// TYPE with class-constrained statics is not expressible yet, and the port
/// rewrites `ShallowEqualityComparer<'T>.Instance` and
/// `ShallowEqualityComparer<_>.ShallowEquals(a, b)` onto these.
let shallowHashCode (v : 'a) : int when ShallowEquality<'a> = shallowHash v
let shallowEqualsOf (a : 'a) (b : 'a) : bool when ShallowEquality<'a> = shallowEquals a b
let shallowComparer () : IEqualityComparer<'a> when ShallowEquality<'a> =
    { new IEqualityComparer<'a> with
        member x.GetHashCode v = shallowHash v
        member x.Equals (a, b) = shallowEquals a b }
