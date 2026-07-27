module Fpp.Bootstrap.PreludeDrive

// Driver for the stage-0 harness: exercises the F++ side of the bootstrap
// seam (`stdlib/bootstrap.fpp`) so the gate proves behaviour, not just that
// the module instantiates.

open Fpp.Prelude

let v = vecNew<int> ()
let fill =
    let mutable i = 0
    while i < 40 do
        vecAdd v (i * i)
        i <- i + 1
let p1 = print (string (vecLen v))
let p2 = print (string (vecGet v 39))
let ins = vecInsert v 0 999
let p3 = print (string (vecGet v 0) + " " + string (vecGet v 1) + " " + string (vecLen v))
let p4 = print (string (List.length (vecToList v)))
let vl = vecOfList [ 1; 2; 3 ]
let p5 = print (String.concat "," (List.map (fun x -> string x) (vecToList vl)))

let d = dictNew<string, int> ()
let dfill =
    let mutable i = 0
    while i < 50 do
        dictSet d ("k" + string i) i
        i <- i + 1
let p6 = print (string d.Count)
let p7 =
    match dictTryFind d "k37" with
    | Some x -> print ("found " + string x)
    | None -> print "MISSING"
let p8 =
    match dictTryFind d "nope" with
    | Some x -> print ("BAD " + string x)
    | None -> print "absent"
let upd = dictSet d "k37" 1000
let p9 =
    match dictTryFind d "k37" with
    | Some x -> print ("updated " + string x)
    | None -> print "MISSING"
let p10 = print (string (List.length (dictPairs d)))
let p11 = print (String.concat "," (List.map (fun (k, _) -> k) (List.filter (fun (_, x) -> x < 3) (dictPairs d))))
let p12 = print (substr "hello world" 6 5)
let p13 = print (string (strLen "abc") + " " + string (charAt "abc" 1))
let p14 = print (stringOfChars [ 'f'; 'p'; 'p' ])
let p15 = print (string (isDigit '7') + " " + string (isHexDigit 'f') + " " + string (isLetter 'q') + " " + string (isLetter '-'))
