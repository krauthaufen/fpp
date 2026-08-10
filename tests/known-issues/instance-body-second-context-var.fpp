// The second face of generic-instance-operator-body.fpp, same trap
// (`toi`, cast failure): an instance body that dispatches on TWO of its
// context variables resolves the second down the int path. One context
// variable stamps correctly (`when Sz<'a>` with `sz p.A` runs); it is
// the second dispatch that dies — `Sz.sz p.B` at 'b = float unboxes an
// int. Pre-existing (reproduces before the 2026-08 typeclass arc); both
// faces likely share one fix in how a stamped copy resolves $class
// markers for more than one instance argument.
type P<'a, 'b> = { A : 'a; B : 'b }
class Sz<'x>
    static sz : 'x -> int
instance Sz<int>
    static sz x = 1
instance Sz<float>
    static sz x = 2
instance Sz<P<'a, 'b>> when Sz<'a> and Sz<'b>
    static sz p = Sz.sz p.A + Sz.sz p.B
printfn "%s" (string (Sz.sz { A = 1; B = 2.5 }))
