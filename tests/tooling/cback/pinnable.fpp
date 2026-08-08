module PinTest
[<Struct>]
type V2 = { X : float; Y : float }

extern let c_sum2 : nativeint -> int -> float
extern let c_first : nativeint -> int
extern let c_bump : nativeint -> unit

let go =
    let a = [| { X = 1.0; Y = 2.0 }; { X = 3.0; Y = 4.0 } |]
    // scoped pinning through the class: unpins on scope exit
    use p = fixed a
    print (c_sum2 p 2)
    // strings pin like byte arrays
    let s = "Hi"
    use ps = fixed s
    print (c_first ps)
    // `fixed &target`: pointer-wide addresses — a stack struct is
    // addressed DIRECTLY (no bounce), array elements pin in place
    let mutable v = { X = 1.0; Y = 2.0 }
    (use bp = fixed &v
     c_bump bp)
    print (int v.X)
    let ba = [| { X = 5.0; Y = 0.0 }; { X = 7.0; Y = 0.0 } |]
    (use bq = fixed &ba.[1]
     c_bump bq
     print (int ba.[1].X))
    print "ok"

type Color =
    | Red = 1
    | Green = 2
let sz = sizeof<Color>
