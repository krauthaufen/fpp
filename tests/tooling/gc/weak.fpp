// Weak references, ephemeron-keyed tables and explicit roots, over the
// collector the wasm-linear leg actually runs on (fpprt/Whippet).

type Cell(n : int) =
    member x.N = n

/// a value that points BACK at its key: a weak-key/strong-value table could
/// never collect this pair, an ephemeron does
type Deco(owner : Cell, tag : string) =
    member x.Owner = owner
    member x.Tag = tag

let weakClears () =
    let live = Cell 1
    let wLive = WeakReference<Cell> live
    let wDead =
        let tmp = Cell 2
        WeakReference<Cell> tmp
    GC.Collect ()
    printfn "live %b dead %b" wLive.IsAlive wDead.IsAlive
    match wLive.TryGetTarget () with
    | (true, c) -> printfn "target %d" c.N
    | _ -> printfn "target LOST"

let tableDropsDeadKeys () =
    let table = ConditionalWeakTable<Cell, Deco>()
    let kept = Cell 10
    table.Add (kept, Deco (kept, "kept"))
    let add () =
        let dead = Cell 11
        table.Add (dead, Deco (dead, "dead"))
    add ()
    printfn "entries %d" table.Count
    GC.Collect ()
    printfn "entries after %d" table.Count
    match table.TryGetValue kept with
    | (true, d) -> printfn "kept %s" d.Tag
    | _ -> printfn "kept LOST"

let rootsPin () =
    let w, h =
        let c = Cell 20
        WeakReference<Cell> c, GCRoot.Alloc (box c)
    GC.Collect ()
    printfn "rooted %b" w.IsAlive
    GCRoot.Free h
    GC.Collect ()
    printfn "freed %b" w.IsAlive

/// the cleanup registry has to hold far more than a handful of pending
/// watches: one per VALUE (the ported Index does exactly this) blows straight
/// past a small fixed area, and overflow used to corrupt the shadow stack
let manyPendingWatches () =
    let mutable fired = 0
    let keep = ResizeArray<Cell>()
    let mutable i = 0
    while i < 5000 do
        let c = Cell i
        keep.Add c
        GC.OnCleanup (box c) (fun () -> fired <- fired + 1)
        i <- i + 1
    GC.Collect ()
    printfn "pending %d fired %d" keep.Count fired
    keep.Clear ()
    GC.Collect ()
    printfn "drained %d" fired

let go =
    weakClears ()
    tableDropsDeadKeys ()
    rootsPin ()
    manyPendingWatches ()
