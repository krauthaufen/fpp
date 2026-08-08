module PinTest
[<Struct>]
type V2 = { X : float; Y : float }

extern let c_sum2 : int -> int -> float

let go =
    let a = [| { X = 1.0; Y = 2.0 }; { X = 3.0; Y = 4.0 } |]
    // scoped pinning through the class: unpins on scope exit
    use p = fixed a
    print (c_sum2 p 2)
    print "ok"
