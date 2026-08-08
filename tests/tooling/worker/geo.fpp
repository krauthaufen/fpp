module Geo
[<Struct>]
type V2d = { X : float; Y : float }

instance Serialize<V2d>
    static write (b : Buffer) (v : V2d) =
        b.WriteFloat v.X
        b.WriteFloat v.Y
    static read (r : Reader) =
        let x = r.ReadFloat ()
        let y = r.ReadFloat ()
        { X = x; Y = y }
    static writeArray (b : Buffer) (xs : V2d[]) =
        let n = xs.Length
        b.WriteInt n
        b.WriteBlock (Array.pin xs) (n * 16)
    static readArray (r : Reader) =
        let n = r.ReadInt ()
        let xs : V2d[] = Array.zeroCreate n
        Memory.copy (Array.pin xs) (r.Block (n * 16)) (n * 16)
        xs

// what the worker is asked to do, and what it answers
type Job =
    | Sum of V2d[]
    | Scale of V2d[] * float
type Answer =
    | Total of V2d
    | Scaled of V2d[]

instance Serialize<Job>
    static write (b : Buffer) (j : Job) =
        match j with
        | Sum pts ->
            b.WriteByte 0
            write b pts
        | Scale (pts, k) ->
            b.WriteByte 1
            write b pts
            b.WriteFloat k
    static read (r : Reader) =
        if r.ReadByte () = 0 then Sum (read r)
        else
            let pts : V2d[] = read r
            Scale (pts, r.ReadFloat ())
    static writeArray (b : Buffer) (xs : Job[]) = failwith "no"
    static readArray (r : Reader) = failwith "no"

instance Serialize<Answer>
    static write (b : Buffer) (a : Answer) =
        match a with
        | Total v ->
            b.WriteByte 0
            write b v
        | Scaled pts ->
            b.WriteByte 1
            write b pts
    static read (r : Reader) =
        if r.ReadByte () = 0 then Total (read r) else Scaled (read r)
    static writeArray (b : Buffer) (xs : Answer[]) = failwith "no"
    static readArray (r : Reader) = failwith "no"

type Geometry = { Calls : int }

instance Worker<Geometry>
    type Command = Job
    type Reply = Answer
    static create () = { Calls = 0 }
    static handle (w : Geometry) (j : Job) =
        match j with
        | Sum pts ->
            let mutable sx = 0.0
            let mutable sy = 0.0
            let mutable i = 0
            while i < pts.Length do
                sx <- sx + pts.[i].X
                sy <- sy + pts.[i].Y
                i <- i + 1
            Total { X = sx; Y = sy }
        | Scale (pts, k) ->
            let out : V2d[] = Array.zeroCreate pts.Length
            let mutable i = 0
            while i < pts.Length do
                out.[i] <- { X = pts.[i].X * k; Y = pts.[i].Y * k }
                i <- i + 1
            Scaled out
    static writeCommand (h : WorkerHandle<Geometry>) (b : Buffer) (j : Job) = write b j
    static readCommand (h : WorkerHandle<Geometry>) (r : Reader) = read r
    static writeReply (h : WorkerHandle<Geometry>) (b : Buffer) (a : Answer) = write b a
    static readReply (h : WorkerHandle<Geometry>) (r : Reader) = read r

// the worker side: one exported entry, one line
let theWorker : Geometry = create ()
let selfHandle : WorkerHandle<Geometry> = WorkerHandle 0
[<Export>]
let dispatch (p : nativeint) : nativeint = Worker.serve selfHandle theWorker p

// the host side
let h : WorkerHandle<Geometry> = WorkerHandle 1
let pts = [| { X = 1.0; Y = 2.0 }; { X = 3.0; Y = 4.0 }; { X = 10.0; Y = 20.0 } |]


// ---- what the host and the worker expose to JavaScript ----
// Every crossing is an address into linear memory, which the host reads and
// writes directly: `memory` is exported, so a message never has to be
// described to JS at all.

/// Host: build a `Sum` command over `n` generated points; the message's
/// address. The points are a POD struct array, so the command carries their
/// image rather than a per-element encoding.
[<Export>]
let makeSum (n : int) : nativeint =
    let pts : V2d[] = Array.zeroCreate n
    let mutable i = 0
    while i < n do
        pts.[i] <- { X = float (i + 1); Y = float ((i + 1) * 2) }
        i <- i + 1
    (Worker.encodeCommand h (Sum pts)).Pointer

/// Host: build a `Scale` command over `n` points.
[<Export>]
let makeScale (n : int) : nativeint =
    let pts : V2d[] = Array.zeroCreate n
    let mutable i = 0
    while i < n do
        pts.[i] <- { X = float (i + 1); Y = float ((i + 1) * 2) }
        i <- i + 1
    (Worker.encodeCommand h (Scale (pts, 3.0))).Pointer

/// How many bytes at that address belong to the message.
[<Export>]
let msgLength (p : nativeint) : int = Worker.messageLength p

/// Room for an incoming message.
[<Export>]
let reserve (n : int) : nativeint = Memory.alloc n

/// Host: read a reply and report it as an integer a test can check —
/// x + y for a total, and the scaled count times the last x for an array.
[<Export>]
let readAnswer (p : nativeint) : int =
    let a : Answer = Worker.decodeReply h p
    match a with
    | Total v -> int (v.X + v.Y)
    | Scaled out -> out.Length * 1000 + int out.[out.Length - 1].X
