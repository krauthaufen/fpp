// The compute sample: bind groups, storage buffers, a ZERO-COPY WriteBuffer
// upload straight from pinned F++ memory, dispatch, and mapped readback.
module GpuCompute
open WebGpu

let mutable result = "pending"

[<Export>]
let ok (_x : int) : int = if result = "pass" then 1 else 0

let shaderCode =
    "@group(0) @binding(0) var<storage, read_write> data : array<f32>;\n" +
    "@compute @workgroup_size(64)\n" +
    "fn main(@builtin(global_invocation_id) id : vec3u) {\n" +
    "  if (id.x < arrayLength(&data)) { data[id.x] = data[id.x] * 2.0 + 1.0; }\n" +
    "}\n"

[<Struct>]
type F1 = { mutable V : float32 }

let input = [| { V = 1.0f }; { V = 2.0f }; { V = 3.0f }; { V = 4.0f }
               { V = 5.0f }; { V = 6.0f }; { V = 7.0f }; { V = 8.0f } |]

let verify (v : int -> float) : bool =
    let mutable okAll = true
    let mutable i = 0
    while i < 8 do
        if v i <> float (i + 1) * 2.0 + 1.0 then okAll <- false
        i <- i + 1
    okAll

let go =
    (future {
        let gpu = WebGpu.Gpu ()
        let! adapter = gpu.RequestAdapter ()
        let! device = adapter.RequestDevice ()
        let storage =
            device.CreateBuffer
                { Size = 32.0
                  Usage = GPUBufferUsage.Storage ||| GPUBufferUsage.CopyDst ||| GPUBufferUsage.CopySrc }
        // ZERO-COPY upload: the view aliases the pinned array's real storage
        device.Queue.WriteBuffer (storage, 0.0, input)
        let module_ = device.CreateShaderModule { Code = shaderCode }
        let pipeline =
            device.CreateComputePipeline
                { Layout = GPUAutoLayoutMode.Auto
                  Compute = { Module = module_; EntryPoint = "main" } }
        let bindGroup =
            device.CreateBindGroup
                { Layout = pipeline.GetBindGroupLayout 0
                  Entries = [| { Binding = 0
                                 Resource = Marshal.GPUBufferBindingJs ({ Buffer = storage } : GPUBufferBinding) } |] }
        let readback =
            device.CreateBuffer
                { Size = 32.0
                  Usage = GPUBufferUsage.MapRead ||| GPUBufferUsage.CopyDst }
        let encoder = device.CreateCommandEncoder ()
        let pass = encoder.BeginComputePass ()
        pass.SetPipeline pipeline
        pass.SetBindGroup (0, bindGroup)
        pass.DispatchWorkgroups 1
        pass.End ()
        encoder.CopyBufferToBuffer (storage, readback)
        device.Queue.Submit [| encoder.Finish () |]
        let! _u = readback.MapAsync GPUMapMode.Read
        let out = Js.new1 (Js.global_ "Float32Array") (readback.GetMappedRange ())
        let v (i : int) : float = Js.toNum (Js.item out i)
        // expect x*2+1: 3, 5, 7, ... 17
        result <- (if verify v then "pass" else "fail " + string (v 0) + "," + string (v 7))
        print result
    }) |> ignore
    print "started"
