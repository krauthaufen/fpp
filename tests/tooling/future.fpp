module FutGate
let go =
    // sync chain
    let a =
        future {
            let! x = Future.Resolved 5
            let! y = Future.Resolved 7
            return x + y
        }
    print a.Result
    // async completion: resolve AFTER the chain is built
    let src = Future<int> ()
    let b =
        future {
            let! x = src
            let! y = Future.Resolved 100
            return x * y
        }
    print b.IsCompleted
    src.Resolve 3
    print b.IsCompleted
    print b.Result
    (future {
        let! q = Future.Failed "boom"
        return q + 1
     }) |> (fun bad -> print bad.IsFailed)
    print "ok"
