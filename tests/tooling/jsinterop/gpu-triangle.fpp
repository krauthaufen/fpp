// The WebGPU acceptance gate: the classic hello-triangle, ported from the
// JS sample with NAMING CHANGES ONLY — future{} for the awaits, records
// for the dictionaries, real enums for the strings. Renders a fullscreen
// orange triangle, copies the texture into a mappable buffer, and asserts
// the pixels from F++.
module GpuTriangle
open Dom
open WebGpu

let shaderCode =
    "@vertex fn vs(@builtin(vertex_index) i : u32) -> @builtin(position) vec4f {\n" +
    "  let p = array<vec2f, 3>(vec2f(-1.0, -1.0), vec2f(3.0, -1.0), vec2f(-1.0, 3.0));\n" +
    "  return vec4f(p[i], 0.0, 1.0);\n" +
    "}\n" +
    "@fragment fn fs() -> @location(0) vec4f { return vec4f(1.0, 0.5, 0.0, 1.0); }\n"

let mutable result = "pending"

[<Export>]
let ok (_x : int) : int = if result = "pass" then 1 else 0

let go =
    (future {
        let gpu = WebGpu.Gpu ()
        let! adapter = gpu.RequestAdapter ()
        let! device = adapter.RequestDevice ()
        let doc = Dom.Document ()
        let canvas = doc.CreateElement "canvas"
        canvas.SetAttribute ("width", "64")
        canvas.SetAttribute ("height", "64")
        let context = WrapGPUCanvasContext (Js.register ((HTMLCanvasElement canvas.Handle).GetContext "webgpu"))
        let format = gpu.GetPreferredCanvasFormat ()
        context.Configure { Device = device; Format = format
                            Usage = GPUTextureUsage.RenderAttachment ||| GPUTextureUsage.CopySrc }
        let module_ = device.CreateShaderModule { Code = shaderCode }
        let pipeline =
            device.CreateRenderPipeline
                { Layout = GPUAutoLayoutMode.Auto
                  Vertex = { Module = module_; EntryPoint = "vs" }
                  Fragment = { Module = module_; EntryPoint = "fs"
                               Targets = [| { Format = format } |] } }
        let readback =
            device.CreateBuffer
                { Size = 16384.0
                  Usage = GPUBufferUsage.MapRead ||| GPUBufferUsage.CopyDst }
        let encoder = device.CreateCommandEncoder ()
        let target = context.GetCurrentTexture ()
        let pass =
            encoder.BeginRenderPass
                { ColorAttachments =
                    [| { View = target.CreateView ()
                         LoadOp = GPULoadOp.Clear
                         StoreOp = GPUStoreOp.Store
                         ClearValue = { R = 0.0; G = 0.0; B = 0.0; A = 1.0 } } |] }
        pass.SetPipeline pipeline
        pass.Draw 3
        pass.End ()
        encoder.CopyTextureToBuffer (
            { Texture = target },
            { Buffer = readback; BytesPerRow = 256 },
            { Width = 64; Height = 64 })
        device.Queue.Submit [| encoder.Finish () |]
        let! _u = readback.MapAsync GPUMapMode.Read
        let bytes = Js.new1 (Js.global_ "Uint8Array") (readback.GetMappedRange ())
        let px (i : int) : int = int (Js.toNum (Js.item bytes i))
        // center pixel, BGRA or RGBA depending on the preferred format
        let c = (32 * 64 + 32) * 4
        let r0 = px c
        let b0 = px (c + 2)
        let good (r : int) (b : int) = (r = 255 && b = 0) || (r = 0 && b = 255)
        result <-
            (if (px (c + 1) = 127 || px (c + 1) = 128) && good r0 b0 then "pass"
             else "fail " + string r0 + "," + string (px (c + 1)) + "," + string b0)
        print result
    }) |> ignore
    print "started"
