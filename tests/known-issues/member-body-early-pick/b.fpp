module B
open A
type Mine = { X : int }
instance SE<Mine>
    static eq a b = 999
let b = Box { X = 1 }
print (string (b.Same { X = 2 }))
