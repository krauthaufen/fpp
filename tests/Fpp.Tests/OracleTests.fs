module Fpp.Tests.OracleTests

open Expecto
open Fpp

// The oracle harness: the shared subset is real F#, so every program can run
// twice — under dotnet fsi and under fpp+wasmtime — and the outputs must
// match. A machine-checked conformance suite for the inherited semantics.

let private wasmtime =
    System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    + "/.wasmtime/bin/wasmtime"

let private run (exe : string) (args : string) : string * int =
    let psi = System.Diagnostics.ProcessStartInfo(exe, args)
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    use p = System.Diagnostics.Process.Start psi
    let out = p.StandardOutput.ReadToEnd()
    p.StandardError.ReadToEnd() |> ignore
    p.WaitForExit()
    out, p.ExitCode

let private fppRun (src : string) : string =
    let ws = Workspace()
    ws.SetFileText "prog.fpp" src
    let wat, errors = ws.EmitProgram ()
    Expect.isEmpty errors "emission errors"
    let tmp = System.IO.Path.GetTempFileName() + ".wat"
    System.IO.File.WriteAllText(tmp, wat)
    let out, code = run wasmtime ("-W exceptions=y " + tmp)
    System.IO.File.Delete tmp
    Expect.equal code 0 "wasmtime failed"
    out

let private fsiRun (src : string) : string =
    // strip the module header; provide the F# side of `print`
    let body =
        src.Split '\n'
        |> Array.filter (fun l -> not (l.StartsWith "module "))
        |> String.concat "\n"
    let prelude =
        "let print (x : obj) =\n"
        + "    match x with\n"
        + "    | :? string as s -> printfn \"%s\" s\n"
        + "    | :? int as i -> printfn \"%d\" i\n"
        + "    | other -> printfn \"%O\" other\n"
    let tmp = System.IO.Path.GetTempFileName() + ".fsx"
    System.IO.File.WriteAllText(tmp, prelude + body)
    let out, code = run "dotnet" ("fsi " + tmp)
    System.IO.File.Delete tmp
    Expect.equal code 0 "fsi failed"
    out

let private oracle (name : string) (srcLines : string list) =
    test name {
        let src = String.concat "\n" ("module M" :: srcLines) + "\n"
        let expected = fsiRun src
        let actual = fppRun src
        Expect.equal actual expected "F++ output must match F# (the oracle)"
    }

[<Tests>]
let oracleTests =
    testList "oracle: F# vs F++" [
        oracle "factorial including beyond-i31 range" [
            "let rec fact n ="
            "    if n <= 1 then 1"
            "    else n * fact (n - 1)"
            "let a = print (fact 10)"
            "let b = print (fact 13)"   // 1932053504 — needs full int32
            "let c = print \"done\""
        ]
        oracle "tail recursion at depth 1000000" [
            "let rec loop i acc ="
            "    if i = 0 then acc"
            "    else loop (i - 1) (acc + 1)"
            "let a = print (loop 1000000 0)"
        ]
        oracle "imperative: while, range-for, mutables" [
            "let sumTo n ="
            "    let mutable acc = 0"
            "    let mutable i = 1"
            "    while i <= n do"
            "        acc <- acc + i"
            "        i <- i + 1"
            "    acc"
            "let a = print (sumTo 100)"
            "let countFor () ="
            "    let mutable s = 0"
            "    for i in 1 .. 10 do"
            "        s <- s + i * i"
            "    s"
            "let b = print (countFor ())"
        ]
        oracle "arrays: literals, indexing, mutation, Length" [
            "let xs = [| 10; 20; 30 |]"
            "let a = print (xs.[0] + xs.[2])"
            "let doIt () ="
            "    xs.[1] <- 99"
            "    xs.[1]"
            "let b = print (doIt ())"
            "let c = print (xs.Length)"
            "let d = print (\"hello\".Length)"
            "let sumArr (arr : int[]) ="
            "    let mutable s = 0"
            "    for i in 0 .. arr.Length - 1 do"
            "        s <- s + arr.[i]"
            "    s"
            "let e = print (sumArr [| 1; 2; 3; 4 |])"
        ]
        oracle "string concatenation" [
            "let greet name ="
            "    \"Hello, \" + name + \"!\""
            "let a = print (greet \"F++\")"
            "let b = print (1 + 2 + 3)"
        ]
        oracle "floats: arithmetic, comparison, printing" [
            "let a = print (1.5 + 2.25)"
            "let b = print (10.0 / 4.0)"
            "let c = print (3.5 * 2.0 - 0.5)"
            "let d = print (if 2.5 > 2.25 then 1 else 0)"
            "let area (r : float) = r * r * 3.140625"
            "let e = print (area 2.0)"
        ]
        oracle "int64: wide arithmetic" [
            "let big = 5000000000L"
            "let a = print (big + big)"
            "let b = print (big * 3L)"
            "let c = print (9000000000L / 4L)"
            "let d = print (if 5000000001L > big then 1 else 0)"
        ]
        oracle "float32 arithmetic" [
            "let x = 0.5f + 0.25f"
            "let a = print (x * 2.0f)"
        ]
        oracle "struct V2d: array of structs, field sums" [
            "[<Struct>]"
            "type V2d = { X : float; Y : float }"
            "let pts = [| { X = 1.5; Y = 2.5 }; { X = 3.25; Y = 0.75 }; { X = 10.0; Y = 20.0 } |]"
            "let total ="
            "    let mutable s = 0.0"
            "    for i in 0 .. pts.Length - 1 do"
            "        s <- s + pts.[i].X + pts.[i].Y"
            "    s"
            "let a = print total"
            "let b = print (pts.[2].X * pts.[0].Y)"
            "let dot (u : V2d) (v : V2d) = u.X * v.X + u.Y * v.Y"
            "let c = print (dot pts.[0] pts.[1])"
        ]
        oracle "exceptions: failwith, try/with, rethrow-free paths" [
            "let risky n ="
            "    if n < 0 then failwith \"negative\""
            "    else n * 2"
            "let safe n ="
            "    try risky n"
            "    with"
            "    | Failure msg ->"
            "        let x = print (\"caught: \" + msg)"
            "        0 - 1"
            "let a = print (safe 21)"
            "let b = print (safe (0 - 5))"
            "let c = print (safe 100)"
        ]
        oracle "heterogeneous struct arrays (SoA columns per field)" [
            "[<Struct>]"
            "type Particle = { X : float; Y : float; Id : int; Tag : string }"
            "let ps = [| { X = 1.5; Y = 2.5; Id = 7; Tag = \"a\" }; { X = 3.0; Y = 4.0; Id = 9; Tag = \"b\" } |]"
            "let sums ="
            "    let mutable s = 0.0"
            "    for i in 0 .. ps.Length - 1 do"
            "        s <- s + ps.[i].X * ps.[i].Y"
            "    s"
            "let a = print sums"
            "let b = print (ps.[0].Id + ps.[1].Id)"
            "let c = print (ps.[1].Tag + ps.[0].Tag)"
        ]
        oracle "mixed-POD struct arrays (C-image words: f64 + i32 + f32)" [
            "[<Struct>]"
            "type Cell = { V : float; N : int; W : float32 }"
            "let cs = [| { V = 1.5; N = 3; W = 0.25f }; { V = 2.5; N = 4; W = 0.5f } |]"
            "let a = print (cs.[0].V + cs.[1].V)"
            "let b = print (cs.[0].N + cs.[1].N)"
            "let c = print (cs.[1].W + cs.[0].W)"
            "let upd = cs.[0] <- { V = 9.0; N = 7; W = 1.0f }"
            "let d = print (cs.[0].V)"
            "let e = print (cs.[0].N)"
            "let grown = Array.create 3 { V = 0.5; N = 2; W = 2.0f }"
            "let f = print (grown.[2].V + grown.[1].V)"
            "let h = print (grown.[1].W + grown.[0].W)"
            "let g = print grown.Length"
        ]
        oracle "nested POD structs (recursive C layout, dotted leaf fusion)" [
            "[<Struct>]"
            "type V2d = { X : float; Y : float }"
            "[<Struct>]"
            "type Box = { Min : V2d; Max : V2d; Tag : int }"
            "let bs = [| { Min = { X = 1.0; Y = 2.0 }; Max = { X = 3.0; Y = 4.5 }; Tag = 7 };"
            "            { Min = { X = 0.5; Y = 0.25 }; Max = { X = 10.0; Y = 20.0 }; Tag = 9 } |]"
            "let a = print (bs.[0].Min.X + bs.[0].Max.Y)"
            "let b = print (bs.[1].Max.X + bs.[1].Min.Y)"
            "let c = print (bs.[0].Tag + bs.[1].Tag)"
            "let upd = bs.[0] <- { Min = { X = 100.0; Y = 0.0 }; Max = { X = 1.0; Y = 1.0 }; Tag = 42 }"
            "let d = print bs.[0].Min.X"
            "let e = print bs.[0].Tag"
            "let f = print bs.Length"
        ]
        oracle "for-in over arrays (structs and primitives)" [
            "[<Struct>]"
            "type V2d = { X : float; Y : float }"
            "let pts = [| { X = 1.5; Y = 2.5 }; { X = 3.0; Y = 4.0 } |]"
            "let ints = [| 1; 2; 3; 4 |]"
            "let s ="
            "    let mutable acc = 0.0"
            "    for p in pts do"
            "        acc <- acc + p.X + p.Y"
            "    acc"
            "let a = print s"
            "let t ="
            "    let mutable n = 0"
            "    for i in ints do"
            "        n <- n + i * i"
            "    n"
            "let b = print t"
        ]
        oracle "inner let rec (recursive local functions, closures over params)" [
            "let sumTo (n : int) ="
            "    let rec go (acc : int) (i : int) ="
            "        if i > n then acc"
            "        else go (acc + i) (i + 1)"
            "    go 0 1"
            "let a = print (sumTo 10)"
            "let b = print (sumTo 100)"
            "let countDown (start : int) ="
            "    let rec loop (i : int) (acc : int list) ="
            "        if i = 0 then acc"
            "        else loop (i - 1) (i :: acc)"
            "    loop start []"
            "let rec len (xs : int list) ="
            "    match xs with"
            "    | h :: t -> 1 + len t"
            "    | [] -> 0"
            "let c = print (len (countDown 7))"
            "let mapped (xs : int list) ="
            "    let rec go (acc : int list) (ys : int list) ="
            "        match ys with"
            "        | h :: t -> go ((h * 2) :: acc) t"
            "        | [] -> acc"
            "    go [] xs"
            "let d = print (len (mapped (countDown 5)))"
        ]
        oracle "stateless classes: members as callable methods" [
            "type B() ="
            "    member _.Bind (x : int, f : int -> int) = f (x + 1)"
            "    member _.Return (v : int) = v"
            "    member _.Twice (v : int) = v * 2"
            "let b = B()"
            "let r = b.Bind (1, fun x -> b.Return (x * 10))"
            "let a = print r"
            "let c = print (b.Twice 21)"
        ]
        oracle "classes: constructor state, properties, methods, mutation" [
            "type Counter(seed : int) ="
            "    let start = seed * 2"
            "    let mutable n = start"
            "    member _.Start = start"
            "    member _.Plus (a : int) = start + a"
            "    member this.Bump () ="
            "        n <- n + 1"
            "        n"
            "    member this.Twice () = this.Bump () + this.Bump ()"
            "let c = Counter(5)"
            "let a = print c.Start"
            "let b = print (c.Plus 7)"
            "let d = print (c.Bump ())"
            "let e = print (c.Twice ())"
        ]
        oracle "classes: same member names on different types stay distinct" [
            "type Pair(x : int, y : int) ="
            "    let sum = x + y"
            "    member _.Sum = sum"
            "    member _.X = x"
            "    member _.Scale (k : int) = Pair(x * k, y * k)"
            "type Named(label : string, x : int) ="
            "    do print \"building\""
            "    member _.X = x"
            "    member _.Sum = x"
            "    member _.Label = label"
            "type Util ="
            "    static member Add (a : int) (b : int) = a + b"
            "let p = Pair(3, 4)"
            "let q = p.Scale 10"
            "let n = Named(\"hi\", 7)"
            "let r1 = print p.Sum"
            "let r2 = print p.X"
            "let r3 = print q.Sum"
            "let r4 = print n.X"
            "let r5 = print n.Sum"
            "let r6 = print n.Label"
            "let r7 = print (Util.Add 2 3)"
        ]
        oracle "classes: generic, mutable state, instances as values" [
            "type Box<'a>(value : 'a) ="
            "    member _.Value = value"
            "    member _.Map (f : 'a -> 'b) = Box<'b>(f value)"
            "type Acc(init : int) ="
            "    let mutable total = init"
            "    member _.Add (v : int) ="
            "        total <- total + v"
            "        total"
            "    member _.Total = total"
            "let describe (a : Acc) = a.Total"
            "let b = Box(21)"
            "let b2 = b.Map (fun v -> v * 2)"
            "let r1 = print b.Value"
            "let r2 = print b2.Value"
            "let bs = Box(\"hey\")"
            "let r3 = print bs.Value"
            "let acc = Acc(100)"
            "let r4 = print (acc.Add 5)"
            "let r5 = print (acc.Add 5)"
            "let r6 = print (describe acc)"
        ]
        oracle "interfaces: vtable dispatch across implementations" [
            "type IShape ="
            "    abstract member Area : int"
            "    abstract member Scaled : int -> int"
            "type INamed ="
            "    abstract member Name : string"
            "type Sq(side : int) ="
            "    member _.Side = side"
            "    interface IShape with"
            "        member _.Area = side * side"
            "        member _.Scaled k = side * k"
            "    interface INamed with"
            "        member _.Name = \"square\""
            "type Rect(w : int, h : int) ="
            "    interface IShape with"
            "        member _.Area = w * h"
            "        member _.Scaled k = w * h * k"
            "    interface INamed with"
            "        member _.Name = \"rect\""
            "let describe (s : IShape) (n : INamed) = n.Name"
            "let areaOf (s : IShape) = s.Area"
            "let scaled (s : IShape) (k : int) = s.Scaled k"
            "let rec sumAreas (xs : IShape list) ="
            "    match xs with"
            "    | h :: t -> areaOf h + sumAreas t"
            "    | [] -> 0"
            "let sq = Sq(3)"
            "let r = Rect(2, 5)"
            "let shapes = [ (sq :> IShape); (r :> IShape) ]"
            "let a = print (sumAreas shapes)"
            "let b = print (scaled (sq :> IShape) 4)"
            "let c = print (describe (sq :> IShape) (sq :> INamed))"
            "let d = print (describe (r :> IShape) (r :> INamed))"
            "let e = print ((sq :> IShape).Area)"
        ]
        oracle "inheritance: prefix layout, virtual dispatch, inherited members" [
            "type Animal(name : string) ="
            "    member _.Name = name"
            "    abstract member Speak : string"
            "    default _.Speak = \"...\""
            "    member this.Describe = this.Name"
            "type Dog(name : string) ="
            "    inherit Animal(name)"
            "    override _.Speak = \"woof\""
            "type Cat(name : string, lives : int) ="
            "    inherit Animal(name)"
            "    member _.Lives = lives"
            "    override _.Speak = \"meow\""
            "let speakOf (a : Animal) = a.Speak"
            "let nameOf (a : Animal) = a.Name"
            "let d = Dog(\"rex\")"
            "let c = Cat(\"tom\", 9)"
            "let a1 = print (speakOf (d :> Animal))"
            "let a2 = print (speakOf (c :> Animal))"
            "let a3 = print (nameOf (c :> Animal))"
            "let a4 = print d.Name"
            "let a5 = print c.Lives"
            "let a6 = print d.Describe"
            "let a7 = print (Animal(\"generic\")).Speak"
        ]
        oracle "inheritance: three levels, overrides, checked downcasts" [
            "type Base(tag : int) ="
            "    member _.Tag = tag"
            "    abstract member Kind : string"
            "    default _.Kind = \"base\""
            "type Mid(tag : int, extra : int) ="
            "    inherit Base(tag)"
            "    member _.Extra = extra"
            "    override _.Kind = \"mid\""
            "type Leaf(tag : int) ="
            "    inherit Mid(tag, tag * 10)"
            "    override _.Kind = \"leaf\""
            "let kindOf (b : Base) = b.Kind"
            "let tagOf (b : Base) = b.Tag"
            "let l = Leaf(7)"
            "let m = Mid(1, 2)"
            "let a1 = print (kindOf (l :> Base))"
            "let a2 = print (tagOf (l :> Base))"
            "let a3 = print ((l :> Base) :?> Mid).Extra"
            "let a4 = print (kindOf (m :> Base))"
            "let a5 = print l.Extra"
            "let a6 = print (((l :> Base) :?> Leaf).Tag)"
        ]
        oracle "object expressions: anonymous classes that capture" [
            "type IMonoid ="
            "    abstract member Zero : int"
            "    abstract member Combine : int -> int -> int"
            "let adder (bias : int) (scale : int) ="
            "    { new IMonoid with"
            "        member _.Zero = bias"
            "        member _.Combine a b = (a + b) * scale }"
            "let maxer ="
            "    { new IMonoid with"
            "        member _.Zero = 0"
            "        member _.Combine a b = if a > b then a else b }"
            "let rec foldWith (m : IMonoid) (xs : int list) ="
            "    match xs with"
            "    | h :: t -> m.Combine h (foldWith m t)"
            "    | [] -> m.Zero"
            "let xs = [1; 2; 3; 4]"
            "let a = print (foldWith (adder 0 1) xs)"
            "let b = print (foldWith (adder 100 1) xs)"
            "let c = print (foldWith maxer xs)"
            "let d = print (foldWith (adder 0 2) [1; 2])"
        ]
        oracle "type tests: :? against classes and their subclasses" [
            "type Base(tag : int) ="
            "    member _.Tag = tag"
            "type Derived(tag : int) ="
            "    inherit Base(tag)"
            "    member _.Extra = tag * 2"
            "type Other(tag : int) ="
            "    inherit Base(tag)"
            "let classify (b : Base) ="
            "    if b :? Derived then \"derived\""
            "    elif b :? Other then \"other\""
            "    else \"base\""
            "let a = print (classify (Derived(1) :> Base))"
            "let b = print (classify (Other(2) :> Base))"
            "let c = print (classify (Base(3)))"
            "let d = print (if (Derived(4) :> Base) :? Base then \"yes\" else \"no\")"
        ]
        oracle "generic classes specialize per element type" [
            "[<Struct>]"
            "type V2d = { X : float; Y : float }"
            "type Buf<'a>(n : int, init : 'a) ="
            "    let data = Array.create n init"
            "    member _.Get (i : int) = data.[i]"
            "    member _.Set (i : int) (v : 'a) = data.[i] <- v"
            "    member _.Length = data.Length"
            "let vb = Buf(2, { X = 1.0; Y = 2.0 })"
            "let s1 = vb.Set 1 { X = 3.0; Y = 4.0 }"
            "let ib = Buf(2, 7)"
            "let s2 = ib.Set 1 9"
            "let a = print (vb.Get 1).X"
            "let b = print (ib.Get 1)"
            "let c = print vb.Length"
        ]
        oracle "string equality and chars" [
            "let pick s ="
            "    if s = \"yes\" then 1 else 0"
            "let a = print (pick \"yes\")"
            "let b = print (pick \"no\")"
        ]
        oracle "lists, matches, recursion" [
            "let rec sum xs ="
            "    match xs with"
            "    | h :: t -> h + sum t"
            "    | [] -> 0"
            "let rec rev acc xs ="
            "    match xs with"
            "    | h :: t -> rev (h :: acc) t"
            "    | [] -> acc"
            "let a = print (sum [1; 2; 3; 4; 5])"
            "let b = print (sum (rev [] [10; 20; 30]))"
        ]
        oracle "tuples, guards, negatives, arithmetic" [
            "let classify t ="
            "    match t with"
            "    | a, b when a > b -> \"first\""
            "    | a, b when a < b -> \"second\""
            "    | _ -> \"same\""
            "let x = print (classify (2, 1))"
            "let y = print (classify (1, 2))"
            "let z = print (0 - 42)"
            "let w = print ((0 - 7) * (0 - 6))"
            "let v = print (100000 * 30000)"   // int32 wraparound semantics
        ]
    ]
