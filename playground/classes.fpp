module Classes

open Vec

// ==== a user-defined typeclass ==========================================
// A class is not a type: no values, no boxing — just a constraint that a
// generic signature can demand. Hover `show` and `describe`.

class Show<'a>
    static show : 'a -> string

instance Show<int>
    static show v = string v

instance Show<float>
    static show v = string v

instance Show<bool>
    static show v = if v then "yes" else "no"

instance Show<V2d>
    static show v = sprintf "(%f, %f)" v.X v.Y

// generic over the class — hover: `when Show<'a>` rides the signature
let describe (label : string) (v : 'a) : string when Show<'a> =
    label + " = " + show v

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

// one body folds ints, strings and vectors
let mconcat (xs : 'a list) : 'a when Monoid<'a> =
    let mutable acc = mempty
    for x in xs do
        acc <- combine acc x
    acc

// ==== an associated type ================================================
// The result type is decided by the INSTANCE, not written at the use.

class Norm<'v>
    type Scalar
    static norm : 'v -> Scalar

instance Norm<V2d>
    type Scalar = float
    static norm v = sqrt (v.X * v.X + v.Y * v.Y)

instance Norm<float>
    type Scalar = float
    static norm v = abs v
