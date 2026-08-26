// Was the worst F++/C ratio in the suite at 3.0x, and the cause was not
// where any of the obvious guesses pointed: `sqrt` is a Floating class
// member with no body in the instance, so Link generated a wrapper
// `fun x -> sqrtf x` and every call paid three times over — the call
// itself, a 16-byte GC BOX for the result (30M allocations across this
// run), and, because a call is a safepoint, the loop-invariant hoist for
// the whole enclosing loop, so every array base was re-read from its root
// slot per access. Inlining one-instruction wrappers took it to 1.4x.
//
// The five-body simulation from the benchmark game: pairwise force
// accumulation over parallel float arrays, dominated by sqrt and by the
// dependency chain through each body's velocity. Float-heavy in a way the
// array benchmarks are not — they stream, this one recurses on its own
// results.
//
// The bodies are PARALLEL ARRAYS rather than an array of structs, so the
// three twins index identically and nothing here measures struct layout —
// `shapes` and `vertices` already do that.
module Nbody

let pi = 3.141592653589793
let solarMass = 4.0 * pi * pi
let daysPerYear = 365.24
let nb = 5

let bx : float[] = Array.zeroCreate nb
let by : float[] = Array.zeroCreate nb
let bz : float[] = Array.zeroCreate nb
let vx : float[] = Array.zeroCreate nb
let vy : float[] = Array.zeroCreate nb
let vz : float[] = Array.zeroCreate nb
let mass : float[] = Array.zeroCreate nb

let setup =
    bx.[0] <- 0.0
    by.[0] <- 0.0
    bz.[0] <- 0.0
    vx.[0] <- 0.0
    vy.[0] <- 0.0
    vz.[0] <- 0.0
    mass.[0] <- solarMass

    bx.[1] <- 4.84143144246472090
    by.[1] <- -1.16032004402742839
    bz.[1] <- -0.103622044471123109
    vx.[1] <- 0.00166007664274403694 * daysPerYear
    vy.[1] <- 0.00769901118419740425 * daysPerYear
    vz.[1] <- -0.0000690460016972063023 * daysPerYear
    mass.[1] <- 0.000954791938424326609 * solarMass

    bx.[2] <- 8.34336671824457987
    by.[2] <- 4.12479856412430479
    bz.[2] <- -0.403523417114321381
    vx.[2] <- -0.00276742510726862411 * daysPerYear
    vy.[2] <- 0.00499852801234917238 * daysPerYear
    vz.[2] <- 0.0000230417297573763929 * daysPerYear
    mass.[2] <- 0.000285885980666130812 * solarMass

    bx.[3] <- 12.8943695621391310
    by.[3] <- -15.1111514016986312
    bz.[3] <- -0.223307578892655734
    vx.[3] <- 0.00296460137564761618 * daysPerYear
    vy.[3] <- 0.00237847173959480950 * daysPerYear
    vz.[3] <- -0.0000296589568540237556 * daysPerYear
    mass.[3] <- 0.0000436624404335156298 * solarMass

    bx.[4] <- 15.3796971148509165
    by.[4] <- -25.9193146099879641
    bz.[4] <- 0.179258772950371181
    vx.[4] <- 0.00268067772490389322 * daysPerYear
    vy.[4] <- 0.00162824170038242295 * daysPerYear
    vz.[4] <- -0.0000951592254519715870 * daysPerYear
    mass.[4] <- 0.0000515138902046611451 * solarMass

let advance (dt : float) : unit =
    let mutable i = 0
    while i < nb do
        let mutable j = i + 1
        while j < nb do
            let dx = bx.[i] - bx.[j]
            let dy = by.[i] - by.[j]
            let dz = bz.[i] - bz.[j]
            let d2 = dx * dx + dy * dy + dz * dz
            let mag = dt / (d2 * sqrt d2)
            vx.[i] <- vx.[i] - dx * mass.[j] * mag
            vy.[i] <- vy.[i] - dy * mass.[j] * mag
            vz.[i] <- vz.[i] - dz * mass.[j] * mag
            vx.[j] <- vx.[j] + dx * mass.[i] * mag
            vy.[j] <- vy.[j] + dy * mass.[i] * mag
            vz.[j] <- vz.[j] + dz * mass.[i] * mag
            j <- j + 1
        i <- i + 1
    let mutable k = 0
    while k < nb do
        bx.[k] <- bx.[k] + dt * vx.[k]
        by.[k] <- by.[k] + dt * vy.[k]
        bz.[k] <- bz.[k] + dt * vz.[k]
        k <- k + 1

let energy () : float =
    let mutable e = 0.0
    let mutable i = 0
    while i < nb do
        e <- e + 0.5 * mass.[i] * (vx.[i] * vx.[i] + vy.[i] * vy.[i] + vz.[i] * vz.[i])
        let mutable j = i + 1
        while j < nb do
            let dx = bx.[i] - bx.[j]
            let dy = by.[i] - by.[j]
            let dz = bz.[i] - bz.[j]
            e <- e - (mass.[i] * mass.[j]) / sqrt (dx * dx + dy * dy + dz * dz)
            j <- j + 1
        i <- i + 1
    e

let go =
    let mutable px = 0.0
    let mutable py = 0.0
    let mutable pz = 0.0
    let mutable i = 0
    while i < nb do
        px <- px + vx.[i] * mass.[i]
        py <- py + vy.[i] * mass.[i]
        pz <- pz + vz.[i] * mass.[i]
        i <- i + 1
    vx.[0] <- -px / solarMass
    vy.[0] <- -py / solarMass
    vz.[0] <- -pz / solarMass
    let mutable step = 0
    while step < 3000000 do
        advance 0.01
        step <- step + 1
    printfn "%.9f" (energy ())
