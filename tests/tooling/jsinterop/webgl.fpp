// The WebGL showcase: a triangle rendered from a PINNED F++ vertex array —
// the bufferData upload reads the array's real storage through a zero-copy
// Float32Array view — then readPixels lands in another pinned array, and
// F++ checks the color without a single explicit copy in between.
module GlDemo

[<Struct>]
type V2f = { mutable X : float32; mutable Y : float32 }
[<Struct>]
type Rgba = { mutable R : byte; mutable G : byte; mutable B : byte; mutable A : byte }

let verts = [| { X = -1.0f; Y = -1.0f }; { X = 3.0f; Y = -1.0f }; { X = -1.0f; Y = 3.0f } |]
let pixel : Rgba[] = Array.zeroCreate 1

let n (v : float) : JsObj = Js.ofNum v
let ni (v : int) : JsObj = Js.ofNum (float v)

let compile (gl : JsObj) (kind : int) (src : string) : JsObj =
    let sh = Js.call1 gl "createShader" (ni kind)
    Js.call2 gl "shaderSource" sh (Js.ofString src) |> ignore
    Js.call1 gl "compileShader" sh |> ignore
    sh

let go =
    let doc = Js.global_ "document"
    let canvas = Js.call1 doc "createElement" (Js.ofString "canvas")
    Js.setNum canvas "width" 64.0
    Js.setNum canvas "height" 64.0
    let gl = Js.call1 canvas "getContext" (Js.ofString "webgl")
    if Js.isNull gl then print "no webgl" else
    // shaders: full-screen triangle, solid orange
    let vs = compile gl 35633 "attribute vec2 p; void main() { gl_Position = vec4(p, 0.0, 1.0); }"
    let fs = compile gl 35632 "void main() { gl_FragColor = vec4(1.0, 0.5, 0.0, 1.0); }"
    let prog = Js.call0 gl "createProgram"
    Js.call2 gl "attachShader" prog vs |> ignore
    Js.call2 gl "attachShader" prog fs |> ignore
    Js.call1 gl "linkProgram" prog |> ignore
    Js.call1 gl "useProgram" prog |> ignore
    // THE upload: bufferData reads the pinned array through the view
    let buf = Js.call0 gl "createBuffer"
    Js.call2 gl "bindBuffer" (ni 34962) buf |> ignore
    let view = Js.viewF32 (Array.pin verts) 6
    Js.call3 gl "bufferData" (ni 34962) view (ni 35044) |> ignore
    let loc = Js.call2 gl "getAttribLocation" prog (Js.ofString "p")
    Js.call1 gl "enableVertexAttribArray" loc |> ignore
    Js.call6 gl "vertexAttribPointer" loc (ni 2) (ni 5126) (Js.ofNum 0.0) (ni 0) (ni 0) |> ignore
    Js.call3 gl "drawArrays" (ni 4) (ni 0) (ni 3) |> ignore
    // read one pixel BACK into a pinned byte array — zero-copy landing
    let pv = Js.viewU8 (Array.pin pixel) 4
    Js.call7 gl "readPixels" (ni 32) (ni 32) (ni 1) (ni 1) (ni 6408) (ni 5121) pv |> ignore
    print (int pixel.[0].R)
    print (int pixel.[0].G)
    print (int pixel.[0].B)
    print "gl-done"
