// A generic instance whose body applies a CLASS OPERATOR to the
// instance's own type variable compiles clean and traps at runtime
// (`toi`, cast failure): the `+` below is lowered down the int-primitive
// path instead of riding to the per-type copy, so at 'a = float it
// unboxes a float as an int. The named-member shape (`combine`,
// `describe`) rides correctly, and a generic LET with the same operator
// (`let d x : 'a when Num<'a> = x + x`) also works — the gap is
// specifically operator uses inside a generic INSTANCE body. Found by
// writing the obvious generic vector type; nothing in the corpus had
// ever combined the three ingredients.
type V2<'a when Num<'a>> = { X : 'a; Y : 'a }

instance Add<V2<'a>, V2<'a>> when Num<'a>
    type Result = V2<'a>
    static (+) a b = { X = a.X + b.X; Y = a.Y + b.Y }

let v : V2<float> = { X = 1.0; Y = 2.0 }
let w = v + v
printfn "%s" (string w.X)
