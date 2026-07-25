module Demo

extern let jsRandom : int -> int

type Shape =
    | Dot
    | Box of int

let rec fib n =
    if n <= 1 then n
    else fib (n - 1) + fib (n - 2)

let fizzbuzz n =
    if n % 15 = 0 then "FizzBuzz"
    elif n % 3 = 0 then "Fizz"
    elif n % 5 = 0 then "Buzz"
    else "" + "#"

let describe s =
    match s with
    | Dot -> "a dot"
    | Box n -> "a box of " + fizzbuzz n

let header = print "=== F++ in the browser (wasm-GC) ==="
let f1 = print ("fib 25 = " + "")
let f2 = print (fib 25)
let shapes = [ Dot; Box 15; Box 9; Box 10; Box 7 ]
let rec show xs =
    match xs with
    | h :: t ->
        let x = print (describe h)
        show t
    | [] -> 0
let s1 = show shapes
let dice = print "three JS dice rolls:"
let d1 = print (jsRandom 6 + 1)
let d2 = print (jsRandom 6 + 1)
let d3 = print (jsRandom 6 + 1)
let arr = [| 3; 1; 4; 1; 5; 9; 2; 6 |]
let sumIt =
    let mutable s = 0
    for i in 0 .. arr.Length - 1 do
        s <- s + arr.[i]
    s
let s2 = print ("array sum = " + "")
let s3 = print sumIt
let bye = print "=== done ==="
