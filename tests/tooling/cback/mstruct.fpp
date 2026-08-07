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

let bump (v : MV) : MV =
    let mutable w = v           // the param travels BY VALUE
    w.N <- w.N + 1
    w

let go2 =
    let mutable a = { X = 0.5; N = 10 }
    let b = bump a              // a must be untouched
    print a.N
    print b.N
    print (bump (bump b)).N

[<Struct>]
type SR = { mutable Name : string; mutable K : int }

let churn (n : int) : int =
    let mutable s = 0
    let mutable i = 0
    while i < n do
        let l = [ i; i + 1 ]
        s <- s + List.length l
        i <- i + 1
    s

let go3 =
    let mutable r = { Name = "hello"; K = 1 }
    let x = churn 100000
    r.K <- r.K + x
    print r.Name
    print r.K
    let q = r
    r.Name <- "bye"
    print q.Name
    print r.Name
