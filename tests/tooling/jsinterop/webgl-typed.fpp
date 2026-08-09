// The TYPED WebGL gate: the same triangle as the raw-primitives leg, through
// the generated WebGl surface — real GLenum, int handles, zero-copy views.
module GlTyped
open Dom
open WebGl

[<Struct>]
type V2f = { mutable X : float32; mutable Y : float32 }
[<Struct>]
type Rgba = { mutable R : byte; mutable G : byte; mutable B : byte; mutable A : byte }

let verts = [| { X = -1.0f; Y = -1.0f }; { X = 3.0f; Y = -1.0f }; { X = -1.0f; Y = 3.0f } |]
let pixel : Rgba[] = Array.zeroCreate 1

let compile (gl : WebGLRenderingContext) (kind : GLenum) (src : string) : WebGLShader =
    let sh = gl.CreateShader kind
    gl.ShaderSource (sh, src)
    gl.CompileShader sh
    sh

let go =
    let doc = Dom.Document ()
    let canvas = doc.CreateElement "canvas"
    canvas.SetAttribute ("width", "64")
    canvas.SetAttribute ("height", "64")
    let gl = WrapWebGLRenderingContext (Js.register ((HTMLCanvasElement canvas.Handle).GetContext "webgl"))
    let vs = compile gl GLenum.VertexShader "attribute vec2 p; void main() { gl_Position = vec4(p, 0.0, 1.0); }"
    let fs = compile gl GLenum.FragmentShader "void main() { gl_FragColor = vec4(1.0, 0.5, 0.0, 1.0); }"
    let prog = gl.CreateProgram ()
    gl.AttachShader (prog, vs)
    gl.AttachShader (prog, fs)
    gl.LinkProgram prog
    gl.UseProgram prog
    let buf = gl.CreateBuffer ()
    gl.BindBuffer (GLenum.ArrayBuffer, buf)
    gl.BufferData (GLenum.ArrayBuffer, Js.viewF32 (Array.pin verts) 6, GLenum.StaticDraw)
    let loc = gl.GetAttribLocation (prog, "p")
    gl.EnableVertexAttribArray loc
    gl.VertexAttribPointer (loc, 2, GLenum.Float, false, 0, 0.0)
    gl.DrawArrays (GLenum.Triangles, 0, 3)
    let pv = Js.viewU8 (Array.pin pixel) 4
    gl.ReadPixels (32, 32, 1, 1, GLenum.Rgba, GLenum.UnsignedByte, pv)
    print (int pixel.[0].R)
    print (int pixel.[0].G)
    print (int pixel.[0].B)
    print "gl-typed-done"
