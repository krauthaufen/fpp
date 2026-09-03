module Classes

open Vec

// ==== a user-defined typeclass ==========================================
// A class is not a type: no values, no boxing — just a constraint that a
// generic signature can demand. Hover `show` and `describe`.

class Display<'a>
    static display : 'a -> string

instance Display<int>
    static display v = string v

instance Display<float>
    static display v = string v

instance Display<bool>
    static display v = if v then "yes" else "no"

instance Display<V2d>
    static display v = sprintf "(%f, %f)" v.X v.Y

open Classes.Display

// generic over the class — hover: `when Display<'a>` rides the signature
let describe (label : string) (v : 'a) : string when Display<'a> =
    label + " = " + display v

// ==== a lawful class with a generic fold ================================

class Monoid<'a>
    static mempty : 'a
    static combine : 'a -> 'a -> 'a

instance Monoid<int>
    static mempty = 0
    static combine a b = a + b

instance Monoid<string>
    static mempty = ""
    static combine a b = a + b

instance Monoid<V2d>
    static mempty = { X = 0.0; Y = 0.0 }
    static combine a b = a + b

open Classes.Monoid

// one body folds ints, strings and vectors
let mconcat (xs : 'a list) : 'a when Monoid<'a> =
    let mutable acc = mempty
    for x in xs do
        acc <- combine acc x
    acc

// ==== an associated type ================================================
// The result type is decided by the INSTANCE, not written at the use.

class Norm<'v>
    type Mag
    static norm : 'v -> Mag

instance Norm<V2d>
    type Mag = float
    static norm v = sqrt (v.X * v.X + v.Y * v.Y)

instance Norm<float>
    type Mag = float
    static norm v = abs v
