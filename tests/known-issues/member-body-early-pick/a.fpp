// The documented corner of DESIGN.md rule 5. Box.Same asks for SE at the
// class's own type variable while file A is being checked. A plain `let`
// would wait (the requirement travels on its type and is answered per
// use, where the whole program's instances are on the table). A member
// body has nowhere to attach the requirement, so it takes the best
// instance visible IN THIS FILE — the catch-all — and that choice is
// baked into every copy of Box, including Box<Mine>, where B's instance
// is the better answer. Prints 1; the honest answer is 999. The fix is
// letting member bodies carry requirements to the copy-making step, the
// same ride let bodies already take.
module A
class SE<'a>
    static eq : 'a -> 'a -> int
instance SE<'a>
    static eq a b = 1
type Box<'t>(v : 't) =
    member x.Same (o : 't) : int = SE.eq v o
