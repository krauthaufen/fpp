// TRUE byref aliasing — the semantics the copy-in/copy-out workaround
// could not have. Reference: dotnet fsi.
let addOne (x : byref<int>) = x <- x + 1

type MRec = { mutable M : int }

let readTwice (x : byref<int>) (r : MRec) : int =
    let a = x           // reads the CURRENT value
    r.M <- r.M + 100    // mutates the location x aliases
    let b = x           // must SEE that write
    a + b

let go =
    let mutable n = 10
    addOne &n
    print n
    addOne &n
    addOne &n
    print n
    let r = { M = 1 }
    addOne &r.M
    print r.M
    let a = [| 7; 8 |]
    addOne &a.[1]
    print a.[1]
    // aliasing is OBSERVABLE mid-call: byref and direct path see each other
    let rr = { M = 5 }
    print (readTwice &rr.M rr)
    print rr.M

// FORWARDING: `&p` passed on — the fat pair travels through whole chains
let inc2 (x : byref<int>) = x <- x + 1
let incTwice (x : byref<int>) =
    inc2 &x
    inc2 &x
let deep (x : byref<int>) =
    incTwice &x
    inc2 &x

let go2 =
    let mutable q = 5
    incTwice &q
    print q
    let fr = { M = 100 }
    deep &fr.M
    print fr.M
