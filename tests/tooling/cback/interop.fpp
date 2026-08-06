module Interop
// The C-interop gate program. Blittable structs, flat arrays, pinning and
// EXTERN calls into a separately-compiled C file (interop-native.c) that
// declares the SAME structs independently — the byte layout is the
// contract, checked from both sides at runtime.

[<Struct>]
type V2d = { X : float; Y : float }
[<Struct>]
type V3f = { A : float32; B : float32; C : float32 }
[<Struct>]
type C3b = { R : byte; G : byte; B3 : byte }
[<Struct>]
type Mixed = { M : float; T : byte }
[<Struct>]
type Ray = { O : V2d; D : V2d }

// the C side: sizes checked against sizeof there; sums/mutations through
// pinned pointers prove the bytes are the wire format
extern let c_check_sizes : int -> int -> int -> int -> int -> int
extern let c_sum_v2d : int -> int -> float
extern let c_scale_v2d : int -> int -> float -> unit
extern let c_sum_i32 : int -> int -> int
extern let c_ray_len : int -> float

let go =
    // strides, F++ side (byteSize / count = C stride)
    let a2 = [| { X = 1.0; Y = 2.0 }; { X = 3.0; Y = 4.0 } |]
    let a3 = [| { A = 1.0f; B = 2.0f; C = 3.0f }; { A = 4.0f; B = 5.0f; C = 6.0f } |]
    let cb : C3b[] = Array.zeroCreate 2
    let mx : Mixed[] = Array.zeroCreate 2
    let ry = [| { O = { X = 3.0; Y = 0.0 }; D = { X = 0.0; Y = 4.0 } } |]
    print (Array.byteSize a2 / 2)
    print (Array.byteSize a3 / 2)
    print (Array.byteSize cb / 2)
    print (Array.byteSize mx / 2)
    print (Array.byteSize ry)
    // C confirms every stride against its own sizeof (1 = all agree)
    print (c_check_sizes (Array.byteSize a2 / 2) (Array.byteSize a3 / 2)
                         (Array.byteSize cb / 2) (Array.byteSize mx / 2)
                         (Array.byteSize ry))
    // pin, let C READ the flat image
    let p2 = Array.pin a2
    print (c_sum_v2d p2 2)                 // 1+2+3+4 = 10
    // C WRITES through the pointer; unpin copies back; F++ sees the writes
    c_scale_v2d p2 2 10.0
    Array.unpin a2
    print a2.[1].Y                          // 4 * 10 = 40
    // int arrays: same contract on a plain scalar array
    let ints = [| 10; 20; 30; 40 |]
    let pi = Array.pin ints
    print (c_sum_i32 pi 4)                  // 100
    // nested struct through the same wire format
    let pr = Array.pin ry
    print (c_ray_len pr)                    // |(0,4)-(3,0)| = 5
    print "done"
