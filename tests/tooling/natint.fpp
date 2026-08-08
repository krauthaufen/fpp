// nativeint: pointer-wide address integer, unboxed on the tagged rail.
// Everything here is target-independent (sizeof is NOT printed: it is 4 on
// the oracle and 8 native, by design).
module NatInt

[<Struct>]
type Slot = { mutable Addr : nativeint; mutable Len : int }

let apply (f : nativeint -> nativeint) (x : nativeint) = f x

let go =
    let a = nativeint 40
    let b = a + nativeint 2
    print (int b)                          // 42
    print (int (b - a))                    // 2
    print (int (a * nativeint 3))          // 120
    print (int (b / nativeint 5))          // 8
    print (int (b % nativeint 5))          // 2
    print (int (-a))                       // -40
    print (int (a &&& nativeint 24))       // 8
    print (int (a ||| nativeint 7))        // 47
    print (int (a ^^^ nativeint 60))       // 20
    print (int (a <<< 2))                  // 160
    print (int (a >>> 3))                  // 5
    if a < b then print 1 else print 0     // 1
    if a = nativeint 40 then print 1 else print 0  // 1
    print (int (min a b))                  // 40
    print (int (max a b))                  // 42
    // conversions, both directions
    print (int64 b)                        // 42
    print (int (nativeint 7L))             // 7
    print (nativeint 3 + nativeint 4)      // 7 (prints as its integer)
    // through the uniform world: closures, options, lists
    let f = apply (fun p -> p + nativeint 1)
    print (int (f a))                      // 41
    let opt = Some (nativeint 9)
    (match opt with
     | Some p -> print (int p)             // 9
     | None -> print 0)
    let xs = [ nativeint 1; nativeint 2; nativeint 3 ]
    let mutable s = nativeint 0
    for x in xs do s <- s + x
    print (int s)                          // 6
    // a struct FIELD holds one
    let mutable slot = { Addr = nativeint 0; Len = 0 }
    slot.Addr <- nativeint 512
    slot.Len <- 16
    print (int slot.Addr + slot.Len)       // 528
    print "ok"
