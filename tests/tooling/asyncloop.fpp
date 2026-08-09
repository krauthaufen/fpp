module AsyncDemo
// ping-pong through a channel: deterministic interleaving on one loop
let ch = Channel<int> ()
let out = Channel<string> ()
let producer =
    async {
        for i in [ 1; 2; 3 ] do
            ch.Send (i * 10)
            do! Async.switch
        ch.Send 0
    }
let consumer =
    async {
        let mutable go = true
        let mutable acc = 0
        while go do
            let! v = ch.Receive
            if v = 0 then go <- false
            else acc <- acc + v
        return acc
    }
let go =
    let root = CancellationToken None
    Async.start root producer
    let total = Async.runSynchronously consumer
    printfn "%d" total
    // timers order by due time
    let t0 = monoMs ()
    Async.start root (async {
        do! Async.sleep 20.0
        printfn "late"
    })
    Async.start root (async {
        do! Async.sleep 1.0
        printfn "early"
    })
    EventLoop.runUntilIdle ()
    printfn "%d" (if monoMs () - t0 >= 20.0 then 1 else 0)
    // structured cancellation: a cancelled child never resumes
    let scope = root.Child ()
    Async.start scope (async {
        do! Async.sleep 1.0
        printfn "never"
    })
    scope.Cancel ()
    EventLoop.runUntilIdle ()
    printfn "done"
