type P = { X : int; Y : int }
type Shape =
    | Dot
    | Line of int
    | Rect of int * int
let area (s : Shape) : int =
    match s with
    | Dot -> 0
    | Line n -> n
    | Rect (w, h) -> w * h
let go =
    let p = { X = 3; Y = 4 }
    print (string (p.X + p.Y))
    let p2 = { p with Y = 40 }
    print (string (p2.X + p2.Y))
    let shapes = [ Dot; Line 5; Rect (3, 4) ]
    let mutable total = 0
    for s in shapes do total <- total + area s
    print (string total)
    let t = (1, "two", 3.5)
    let (a, b, c) = t
    print (string a)
    print b
    print (string c)
    let arr = [| 10; 20; 30 |]
    arr.[1] <- 25
    print (string (arr.[0] + arr.[1] + arr.[2]))
    print (string (Array.length arr))
    let xs = [ 1; 2; 3; 4 ]
    let rec sum (l : list<int>) : int =
        match l with
        | [] -> 0
        | h :: t -> h + sum t
    print (string (sum xs))
    let add (a : int) (b : int) = a + b
    let inc = add 1
    print (string (inc 41))
    let twice (f : int -> int) (x : int) = f (f x)
    print (string (twice inc 5))
    print (string (List.map (fun x -> x * 2) xs |> List.length))
    if { X = 1; Y = 2 } = { X = 1; Y = 2 } then print "reqeq" else print "reqNO"
    if Rect (2, 3) = Rect (2, 3) then print "dueq" else print "duNO"
    // compare on tuples traps in the wasm-GC backend too (oracle gap,
    // 2026-08): both backends learn it together, later
    if compare 3 4 < 0 then print "cmp" else print "cmpNO"
    if compare "aa" "ab" < 0 then print "scmp" else print "scmpNO"
