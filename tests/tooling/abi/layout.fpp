module Stride2
[<Struct>]
type V3f = { F1 : float32; F2 : float32; F3 : float32 }
[<Struct>]
type V2d = { D1 : float; D2 : float }
[<Struct>]
type V2f = { G1 : float32; G2 : float32 }
[<Struct>]
type V3i = { I1 : int; I2 : int; I3 : int }
[<Struct>]
type V3d = { E1 : float; E2 : float; E3 : float }
let a3 = [| { F1 = 1.0f; F2 = 2.0f; F3 = 3.0f }; { F1 = 4.0f; F2 = 5.0f; F3 = 6.0f } |]
let a2 = [| { D1 = 1.0; D2 = 2.0 }; { D1 = 3.0; D2 = 4.0 } |]
let f2 = [| { G1 = 1.0f; G2 = 2.0f }; { G1 = 3.0f; G2 = 4.0f } |]
let i3 = [| { I1 = 1; I2 = 2; I3 = 3 }; { I1 = 4; I2 = 5; I3 = 6 } |]
let d3 = [| { E1 = 1.0; E2 = 2.0; E3 = 3.0 }; { E1 = 4.0; E2 = 5.0; E3 = 6.0 } |]
let go =
    print (Array.byteSize a3 / 2)
    print (Array.byteSize a2 / 2)
    print (Array.byteSize f2 / 2)
    print (Array.byteSize i3 / 2)
    print (Array.byteSize d3 / 2)
