module Vec

// A 2d vector as an unboxed struct. Hover the type name, the fields,
// and the instances below.
[<Struct>]
type V2d = { X : float; Y : float }

// The operator classes: V2d joins the numeric tower by declaring
// instances. Hover `(+)` / `(*)` — they are ordinary members.
instance Add<V2d, V2d>
    type Result = V2d
    static (+) a b = { X = a.X + b.X; Y = a.Y + b.Y }

instance Sub<V2d, V2d>
    type Result = V2d
    static (-) a b = { X = a.X - b.X; Y = a.Y - b.Y }

instance Mul<V2d, V2d>
    type Result = V2d
    static (*) a b = { X = a.X * b.X; Y = a.Y * b.Y }

// the heterogeneous case Num can never express: scalar * vector
instance Mul<float, V2d>
    type Result = V2d
    static (*) s v = { X = s * v.X; Y = s * v.Y }

instance Num<V2d>
    static Zero = { X = 0.0; Y = 0.0 }
    static One  = { X = 1.0; Y = 1.0 }

// min/max do NOT require an ordering — a vector has a componentwise
// minimum but no total order
instance MinMax<V2d>
    static min a b = { X = min a.X b.X; Y = min a.Y b.Y }
    static max a b = { X = max a.X b.X; Y = max a.Y b.Y }

// Hover these: the inferred schemes carry their class constraints.
let dot (a : V2d) (b : V2d) = a.X * b.X + a.Y * b.Y

let lengthOf (v : V2d) = sqrt (dot v v)

// generic over ANY numeric type — hover shows `when Num<'a>`
let sumOf (xs : 'a[]) (zero : 'a) : 'a when Num<'a> =
    let mutable acc = zero
    for x in xs do
        acc <- acc + x
    acc

// generic clamp needs only MinMax — no ordering anywhere
let clamp (lo : 'a) (hi : 'a) (v : 'a) : 'a when MinMax<'a> =
    max lo (min hi v)
