module Gpu

let vbase = 4096
let spokes = 24

let putv (i : int) (x : float) (y : float) (r : float) (g : float) (b : float) =
    let a = vbase + i * 20
    let s0 = memStoreF32 a x
    let s1 = memStoreF32 (a + 4) y
    let s2 = memStoreF32 (a + 8) r
    let s3 = memStoreF32 (a + 12) g
    let s4 = memStoreF32 (a + 16) b
    0

let generate () =
    let mutable px = 0.9
    let mutable py = 0.0
    let mutable qx = 0.62160997
    let mutable qy = 0.23861918
    let mutable i = 0
    let mutable k = 0
    while k < spokes do
        let shade = 0.3 + 0.7 * (if k % 2 = 0 then 1.0 else 0.35)
        let d0 = putv i 0.0 0.0 0.1 0.1 0.2
        let d1 = putv (i + 1) px py shade (0.25 + 0.5 * shade) (1.0 - 0.5 * shade)
        let d2 = putv (i + 2) (qx * 0.45) (qy * 0.45) (1.0 - shade) 0.4 shade
        i <- i + 3
        let nx = px * 0.86602540 - py * 0.5
        let ny = px * 0.5 + py * 0.86602540
        px <- nx
        py <- ny
        let mx = qx * 0.86602540 - qy * 0.5
        let my = qx * 0.5 + qy * 0.86602540
        qx <- mx
        qy <- my
        k <- k + 1
    i

let count = generate ()
let report = print count
