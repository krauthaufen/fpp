// Boundary-overhead benchmark against a NOP WebGPU: the page provides
// no-op pass/device/buffer objects, so every measured nanosecond is call
// machinery — F++'s binary command stream, F++ per-call Js.callN, and the
// page's own JS loop over the SAME nops as the native floor.
module GpuBench
open WebGpu

let now () : float = Js.toNum (Js.call0 (Js.global_ "performance") "now")

let nop (name : string) : int = Js.register (Js.get (Js.global_ "nops") name)

// wrapped once at startup; handles resolve to the page's nop objects
let mutable passH = 0
let mutable deviceH = 0
let mutable bufferH = 0
let mutable bgH = 0
let mutable layoutH = 0

[<Export>]
let setup (_x : int) : int =
    passH <- nop "pass"
    deviceH <- nop "device"
    bufferH <- nop "buffer"
    bgH <- nop "bg"
    layoutH <- nop "layout"
    1

/// batched: N stencil refs through the stream, ONE crossing at the flush
[<Export>]
let vmStencil (n : int) : int =
    let pass = WrapGPURenderPassEncoder passH
    let buffer = WrapGPUBuffer bufferH
    let t0 = now ()
    for i in 0 .. n - 1 do pass.SetStencilReference i
    buffer.Unmap ()   // immediate: flushes the stream
    int ((now () - t0) * 1000.0)

/// batched: N bind+draw pairs through the stream
[<Export>]
let vmBindDraw (n : int) : int =
    let pass = WrapGPURenderPassEncoder passH
    let bg = WrapGPUBindGroup bgH
    let buffer = WrapGPUBuffer bufferH
    let t0 = now ()
    for _i in 0 .. n - 1 do
        pass.SetBindGroup (0, bg)
        pass.Draw 3
    buffer.Unmap ()
    int ((now () - t0) * 1000.0)

/// immediate: N crossings, one per call
[<Export>]
let vmUnmap (n : int) : int =
    let buffer = WrapGPUBuffer bufferH
    let t0 = now ()
    for _i in 0 .. n - 1 do buffer.Unmap ()
    int ((now () - t0) * 1000.0)

/// immediate with a RECORD: descriptor encoded binary, decoded JS-side
[<Export>]
let vmCreateBindGroup (n : int) : int =
    let device = WrapGPUDevice deviceH
    let layout = WrapGPUBindGroupLayout layoutH
    let buffer = WrapGPUBuffer bufferH
    let t0 = now ()
    for _i in 0 .. n - 1 do
        device.CreateBindGroup
            { Layout = layout
              Entries = [| { Binding = 0
                             Resource = Marshal.GPUBufferBindingJs ({ Buffer = buffer } : GPUBufferBinding) } |] }
        |> ignore
    int ((now () - t0) * 1000.0)

/// the OLD style: one Js.callN crossing per command
[<Export>]
let directStencil (n : int) : int =
    let t0 = now ()
    for i in 0 .. n - 1 do
        Js.call1 (Js.handle passH) "setStencilReference" (Js.ofNum (float i)) |> ignore
    int ((now () - t0) * 1000.0)

[<Export>]
let directBindDraw (n : int) : int =
    let t0 = now ()
    for _i in 0 .. n - 1 do
        Js.call2 (Js.handle passH) "setBindGroup" (Js.ofNum 0.0) (Js.handle bgH) |> ignore
        Js.call1 (Js.handle passH) "draw" (Js.ofNum 3.0) |> ignore
    int ((now () - t0) * 1000.0)

[<Export>]
let directUnmap (n : int) : int =
    let t0 = now ()
    for _i in 0 .. n - 1 do
        Js.call0 (Js.handle bufferH) "unmap" |> ignore
    int ((now () - t0) * 1000.0)

[<Export>]
let directCreateBindGroup (n : int) : int =
    let device = Js.handle deviceH
    let t0 = now ()
    for _i in 0 .. n - 1 do
        let entry = Js.newObj ()
        Js.set entry "binding" (Js.ofNum 0.0)
        Js.set entry "resource" (Marshal.GPUBufferBindingJs ({ Buffer = WrapGPUBuffer bufferH } : GPUBufferBinding))
        let entries = Js.newArr ()
        Js.push entries entry
        let d = Js.newObj ()
        Js.set d "layout" (Js.handle layoutH)
        Js.set d "entries" entries
        Js.call1 device "createBindGroup" d |> ignore
    int ((now () - t0) * 1000.0)

let go = print "bench-ready"
