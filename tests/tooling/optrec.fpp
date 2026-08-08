type Desc = { Label : string; ?Count : int; ?Tag : string }

let show (d : Desc) =
    print d.Label
    (match d.Count with
     | Some c -> print c
     | None -> print "count-none")
    (match d.Tag with
     | Some t -> print t
     | None -> print "tag-none")

let go =
    show { Label = "a" }                          // both omitted -> None
    show { Label = "b"; Count = 7 }               // bare value -> Some 7
    show { Label = "c"; Count = 1; Tag = "hi" }   // all set
    let maybe : option<int> = None
    show { Label = "d"; ?Count = maybe }          // option passes through
    let d0 = { Label = "e" }
    show { d0 with Count = 9 }                    // update wraps too
    print "ok"
