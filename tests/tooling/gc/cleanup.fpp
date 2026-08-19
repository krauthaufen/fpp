// The deterministic-cleanup gate program: GC.OnCleanup closures run exactly
// once, in registration order, at GC.Collect — never while the object lives.
module CleanupGate

let mutable freed = 0

// created in a helper so the object is dead the moment it returns
let spawn (n : int) : unit =
    let o = box [| n; n |]
    GC.OnCleanup o (fun () ->
        freed <- freed + 1
        print ("dead " + string n))

// keep one alive across a collection, then let it go
let mutable kept : obj = box [| 7 |]
let init =
    GC.OnCleanup kept (fun () -> print "dead kept")

let go =
    spawn 1
    spawn 2
    spawn 3
    print "before"
    GC.Collect ()
    print ("after " + string freed)
    // kept is still reachable: its cleanup must NOT have fired
    GC.Collect ()
    kept <- box [| 0 |]
    print "released"
    GC.Collect ()
    // a cleanup registered DURING a drain fires at the next collect
    let inner () : unit =
        let q = box [| 9 |]
        GC.OnCleanup q (fun () -> print "dead inner")
    inner ()
    GC.Collect ()
    print "end"
