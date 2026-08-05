let fib (n : int) : int =
    let mutable a = 0
    let mutable b = 1
    let mutable i = 0
    while i < n do
        let t = a + b
        a <- b
        b <- t
        i <- i + 1
    a
let go =
    let mutable k = 0
    while k <= 20 do
        print (string (fib k))
        k <- k + 1
    if fib 10 = 55 then print "fib ok" else print "fib WRONG"
