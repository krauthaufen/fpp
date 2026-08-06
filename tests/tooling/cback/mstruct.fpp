[<Struct>]
type MV = { mutable X : float; mutable N : int }

let go =
    let mutable a = { X = 1.5; N = 2 }
    a.X <- a.X * 2.0            // in-place mutation
    a.N <- a.N + 40
    print a.X
    print a.N
    let mutable b = a           // COPY: b's mutations must not touch a
    b.X <- 99.0
    print a.X
    print b.X
    a <- b                      // struct assignment copies back
    b.N <- 7
    print a.N
    print b.N
