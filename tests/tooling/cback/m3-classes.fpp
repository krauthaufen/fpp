type Counter(start : int) =
    let mutable n = start
    member _.Bump () : int =
        n <- n + 1
        n
    member _.Value : int = n
type IShow =
    abstract member Show : unit -> string
type Box(v : int) =
    member _.Get : int = v
    interface IShow with
        member _.Show () = "box " + string v
let show (x : IShow) : string = x.Show ()
let go =
    let c = Counter 10
    print (string (c.Bump ()))
    print (string (c.Bump ()))
    print (string c.Value)
    let b = Box 7
    print (string b.Get)
    print (show b)
    let xs : list<IShow> = [ Box 1; Box 2 ]
    for x in xs do print (show x)
