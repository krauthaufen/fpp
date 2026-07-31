module Fpp.Tests.BinBattery

open Expecto

// End-to-end battery for the direct binary backend: each case is a small F++
// program compiled through Workspace.EmitProgramWasm (pure bytes, no wat),
// executed under wasmtime, and pinned to its exact stdout. Every program
// class the binary driver claims to support must have a case here — this is
// the regression gate the porting loop runs against.

let private wasmtime =
    let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    home + "/.wasmtime/bin/wasmtime"

let private runProgram (lines : string list) : string =
    let src = String.concat "\n" lines + "\n"
    let ws = Fpp.Workspace ()
    ws.SetFileText "p.fpp" src
    let bytes, errs = ws.EmitProgramWasm ()
    Expect.isEmpty errs "compile errors"
    let path = System.IO.Path.GetTempFileName () + ".wasm"
    System.IO.File.WriteAllBytes (path, bytes)
    let psi = System.Diagnostics.ProcessStartInfo (wasmtime, "run -W gc=y,exceptions=y " + path)
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    use p = System.Diagnostics.Process.Start psi
    let out = p.StandardOutput.ReadToEnd ()
    let err = p.StandardError.ReadToEnd ()
    p.WaitForExit ()
    System.IO.File.Delete path
    Expect.equal p.ExitCode 0 (sprintf "wasmtime failed: %s" err)
    out

let private expects (name : string) (src : string list) (stdout : string) =
    test name { Expect.equal (runProgram src) stdout "program stdout" }

[<Tests>]
let binBattery =
    testList "binary battery" [
        expects "recursion: factorial"
            [ "let rec fact (n : int) : int ="
              "    if n <= 1 then 1 else n * fact (n - 1)"
              "let go = print (fact 10)" ]
            "3628800\n"

        expects "DU construction and match"
            [ "type Shape ="
              "    | Dot"
              "    | Box of int"
              "let size (s : Shape) : int ="
              "    match s with"
              "    | Dot -> 0"
              "    | Box n -> n"
              "let go ="
              "    print (size Dot)"
              "    print (size (Box 7))" ]
            "0\n7\n"

        expects "list literal and cons recursion"
            [ "let rec total (xs : int list) : int ="
              "    match xs with"
              "    | [] -> 0"
              "    | h :: t -> h + total t"
              "let go = print (total [1; 2; 3; 4])" ]
            "10\n"

        expects "tuple construction and pattern"
            [ "let swap (p : int * int) : int * int ="
              "    match p with"
              "    | (a, b) -> (b, a)"
              "let go ="
              "    match swap (3, 9) with"
              "    | (x, y) -> print (x * 100 + y)" ]
            "903\n"

        expects "record with mutable field"
            [ "type P = { X : int; mutable Y : int }"
              "let go ="
              "    let p = { X = 3; Y = 4 }"
              "    p.Y <- p.Y + 10"
              "    print (p.X * 100 + p.Y)" ]
            "314\n"

        expects "closures capture locals, prelude higher-order"
            [ "let go ="
              "    let k = 10"
              "    let addk = fun x -> x + k"
              "    print (addk 5)"
              "    let xs = List.map (fun x -> x * x) [1; 2; 3]"
              "    print (List.sum xs)" ]
            "15\n14\n"

        expects "captured mutable lives in a cell"
            [ "let counter () ="
              "    let mutable n = 0"
              "    let bump = fun () -> n <- n + 1"
              "    bump ()"
              "    bump ()"
              "    bump ()"
              "    n"
              "let go = print (counter ())" ]
            "3\n"

        expects "local let rec ties its own knot"
            [ "let go ="
              "    let base_ = 100"
              "    let rec walk (n : int) : int ="
              "        if n <= 0 then base_ else 1 + walk (n - 1)"
              "    print (walk 5)" ]
            "105\n"

        expects "mutually recursive local functions"
            [ "let go ="
              "    let rec even (n : int) : bool ="
              "        if n = 0 then true else odd (n - 1)"
              "    and odd (n : int) : bool ="
              "        if n = 0 then false else even (n - 1)"
              "    if even 10 then print 1 else print 0"
              "    if odd 7 then print 1 else print 0" ]
            "1\n1\n"

        expects "partial application of a top-level function"
            [ "let add3 (a : int) (b : int) (c : int) : int = a + b + c"
              "let go ="
              "    let f = add3 100"
              "    let g = f 20"
              "    print (g 3)"
              "    print (g 4)" ]
            "123\n124\n"

        expects "top-level function passed first-class"
            [ "let double (x : int) : int = x * 2"
              "let go = print (List.sum (List.map double [1; 2; 3]))" ]
            "12\n"

        expects "string concat, ordering, Length, indexing"
            [ "let go ="
              "    let s = \"hello\" + \" \" + \"world\""
              "    print s"
              "    print s.Length"
              "    if \"abc\" < \"abd\" then print 1 else print 0"
              "    print s.[4]" ]
            "hello world\n11\n1\no\n"

        expects "float arithmetic and printing"
            [ "let go ="
              "    let x = 1.5 + 2.25"
              "    print x"
              "    print (x * 2.0)"
              "    if 1.5 < 2.5 then print 1 else print 0" ]
            "3.75\n7.5\n1\n"

        expects "conversions: int-of-string, string-of-int, float, truncation"
            [ "let go ="
              "    print (int \"42\")"
              "    print (string 7)"
              "    print (float 3)"
              "    print (int 9.7)"
              "    print (int64 5)" ]
            "42\n7\n3\n9\n5\n"

        expects "compare, max, min"
            [ "let go ="
              "    print (compare \"ab\" \"ac\")"
              "    print (compare 7 3)"
              "    print (max 3 9)"
              "    print (min 2.5 1.5)" ]
            "-1\n1\n9\n1.5\n"

        expects "string builtins: Substring, IndexOf"
            [ "let go ="
              "    let s = \"hello world\""
              "    print (s.Substring (6, 5))"
              "    print (s.IndexOf 'w')"
              "    print (s.Substring 6)" ]
            "world\n6\nworld\n"

        expects "sprintf compile-time expansion"
            [ "let go ="
              "    print (sprintf \"%d-%s\" 5 \"x\")" ]
            "5-x\n"

        expects "for-loop over a list (seq protocol)"
            [ "let go ="
              "    let mutable s = 0"
              "    for x in [1; 2; 3] do"
              "        s <- s + x"
              "    print s" ]
            "6\n"

        expects "class: constructor and member call"
            [ "type Calc(bias : int) ="
              "    member x.Add(a : int) = a + bias"
              "let go ="
              "    let c = Calc(100)"
              "    print (c.Add 5)" ]
            "105\n"

        expects "records are structural, classes are reference-equal"
            [ "type P = { X : int; Y : int }"
              "type Box(v : int) ="
              "    member x.V = v"
              "let go ="
              "    if { X = 1; Y = 2 } = { X = 1; Y = 2 } then print 1 else print 0"
              "    let a = Box(7)"
              "    if a = Box(7) then print 1 else print 0"
              "    if a = a then print 1 else print 0" ]
            "1\n0\n1\n"

        expects "interface dispatch through the vtable"
            [ "type IShape ="
              "    abstract member Area : unit -> int"
              "type Sq(s : int) ="
              "    interface IShape with"
              "        member x.Area () = s * s"
              "let go ="
              "    let sh = Sq(4) :> IShape"
              "    print (sh.Area ())" ]
            "16\n"

        expects "type tests read the descriptor id"
            [ "type A() ="
              "    member x.N = 1"
              "type B() ="
              "    member x.N = 2"
              "let go ="
              "    let o = box (A())"
              "    if (o :? A) then print 1 else print 0"
              "    if (o :? B) then print 1 else print 0" ]
            "1\n0\n"

        expects "inheritance: base field, virtual override"
            [ "type Animal(n : int) ="
              "    member x.Legs = n"
              "    abstract member Sound : unit -> int"
              "    default x.Sound () = 0"
              "type Dog() ="
              "    inherit Animal(4)"
              "    override x.Sound () = 7"
              "let go ="
              "    let d = Dog()"
              "    print d.Legs"
              "    print (d.Sound ())" ]
            "4\n7\n"

        expects "downcast succeeds or throws InvalidCast, try/with catches"
            [ "type A() ="
              "    member x.N = 1"
              "type B() ="
              "    member x.N = 2"
              "let go ="
              "    let o = box (A())"
              "    print (o :?> A).N"
              "    try"
              "        print (o :?> B).N"
              "    with _ -> print 99" ]
            "1\n99\n"

        // MapExt/HashMap/HashSet have no F# counterpart, so the oracle cannot
        // judge them — these pin the combinators and delta operations against
        // hand-computed answers instead.
        expects "Map: MapExt combinators and deltas"
            [ "let m = Map.ofList [ (1, \"a\"); (2, \"b\"); (3, \"c\") ]"
              "let n = Map.ofList [ (2, \"B\"); (4, \"d\") ]"
              "let sm (t : Map<int, string>) = String.concat \",\" (List.map (fun (k, v) -> string k + v) (Map.toList t))"
              "let go ="
              "    print (sm (Map.unionWith (fun k a b -> a + b) m n))"
              "    print (sm (Map.union m n))"
              "    print (sm (Map.difference m n))"
              "    print (sm (Map.choose (fun k v -> if k > 1 then Some v else None) m))"
              "    print (sm (Map.alter 2 (fun o -> None) m))"
              "    print (sm (Map.choose2 (fun k x y -> match x, y with Some a, Some b -> Some (a + b) | Some a, None -> Some a | None, Some b -> Some b | _ -> None) m n))"
              "    let d = Map.computeDelta m n"
              "    print (String.concat \",\" (List.map (fun (k, op) -> string k + (match op with SetOp v -> \":=\" + v | RemoveOp -> \":del\")) (Map.toList d)))"
              "    let st, eff = Map.applyDelta m d"
              "    print (sm st + \" | \" + string (Map.count eff))"
              "    let lo, at, hi = Map.split 2 m"
              "    print (sm lo + \" | \" + (match at with Some v -> v | None -> \"-\") + \" | \" + sm hi)"
              "    print (sm (Map.range 2 3 m))" ]
            "1a,2bB,3c,4d\n1a,2B,3c,4d\n1a,3c\n2b,3c\n1a,3c\n1a,2bB,3c,4d\n1:del,2:=B,3:del,4:=d\n2B,4d | 4\n1a | b | 3c\n2b,3c\n"

        // the shape the original HashMap/HashSet use: an abstract base with
        // virtual members, dispatched through a base-typed reference, with
        // GENERIC and mutually recursive node classes
        // the FsCheck shape: generators are values, properties run over 200
        // cases with a fixed seed, and HashMap/HashSet are checked against the
        // ORDERED collections as reference models
        expects "property tests: the collections against reference models"
            [
              "let kg = Gen.intRange 0 20"
              "let hm = Gen.hashMap kg Gen.int"
              "let hs = Gen.hashSet kg"
              "let norm (m : HashNode<int, int>) = List.sortBy fst (HashMap.toList m)"
              "let keysOf (m : HashNode<int, int>) = Set.ofList (HashMap.keys m)"
              "let setOf (s : HashNode<int, int>) = Set.ofList (HashSet.toList s)"
              "let go ="
              "    Check.quick \"ofList agrees with Map\" (Gen.list (Gen.pair kg Gen.int)) (fun kvs -> norm (HashMap.ofList kvs) = Map.toList (Map.ofList kvs))"
              "    Check.quick \"add then tryFind\" (Gen.triple kg Gen.int hm) (fun t -> HashMap.tryFind (fst t) (HashMap.add (fst t) (fst (snd t)) (snd (snd t))) = Some (fst (snd t)))"
              "    Check.quick \"remove then absent\" (Gen.pair kg hm) (fun t -> not (HashMap.containsKey (fst t) (HashMap.remove (fst t) (snd t))))"
              "    Check.quick \"count is the distinct keys\" hm (fun m -> HashMap.count m = Set.count (keysOf m))"
              "    Check.quick \"union agrees with the model\" (Gen.pair hm hm) (fun t -> norm (HashMap.union (fst t) (snd t)) = Map.toList (Map.ofList (HashMap.toList (fst t) @ HashMap.toList (snd t))))"
              "    Check.quick \"intersect keys agree\" (Gen.pair hm hm) (fun t -> keysOf (HashMap.intersect (fst t) (snd t)) = Set.intersect (keysOf (fst t)) (keysOf (snd t)))"
              "    Check.quick \"difference keys agree\" (Gen.pair hm hm) (fun t -> keysOf (HashMap.difference (fst t) (snd t)) = Set.difference (keysOf (fst t)) (keysOf (snd t)))"
              "    Check.quick \"filter agrees with the list\" hm (fun m -> norm (HashMap.filter (fun k v -> k % 2 = 0) m) = List.filter (fun (k, v) -> k % 2 = 0) (norm m))"
              "    Check.quick \"keySet matches keys\" hm (fun m -> setOf (HashMap.keySet m) = keysOf m)"
              "    Check.quick \"hashset union agrees with Set\" (Gen.pair hs hs) (fun t -> setOf (HashSet.union (fst t) (snd t)) = Set.union (setOf (fst t)) (setOf (snd t)))"
              "    Check.quick \"hashset isSubset agrees with Set\" (Gen.pair hs hs) (fun t -> HashSet.isSubset (fst t) (snd t) = Set.isSubset (setOf (fst t)) (setOf (snd t)))"
              "    Check.quick \"hashmap delta round-trip\" (Gen.pair hm hm) (fun t -> fst (HashMap.applyDelta (fst t) (HashMap.computeDelta (fst t) (snd t))) = snd t)"
              "    Check.quick \"hashset delta round-trip\" (Gen.pair hs hs) (fun t -> fst (HashSet.applyDelta (fst t) (HashSet.computeDelta (fst t) (snd t))) = snd t)"
              "    Check.quick \"Map delta round-trip\" (Gen.pair (Gen.map kg Gen.int) (Gen.map kg Gen.int)) (fun t -> fst (Map.applyDelta (fst t) (Map.computeDelta (fst t) (snd t))) = snd t)"
              "    Check.quick \"computeDelta with self is empty\" hm (fun m -> HashMap.count (HashMap.computeDelta m m) = 0)" ]
            "ofList agrees with Map: ok (200 cases)\nadd then tryFind: ok (200 cases)\nremove then absent: ok (200 cases)\ncount is the distinct keys: ok (200 cases)\nunion agrees with the model: ok (200 cases)\nintersect keys agree: ok (200 cases)\ndifference keys agree: ok (200 cases)\nfilter agrees with the list: ok (200 cases)\nkeySet matches keys: ok (200 cases)\nhashset union agrees with Set: ok (200 cases)\nhashset isSubset agrees with Set: ok (200 cases)\nhashmap delta round-trip: ok (200 cases)\nhashset delta round-trip: ok (200 cases)\nMap delta round-trip: ok (200 cases)\ncomputeDelta with self is empty: ok (200 cases)\n"

        // a falsified property reports the SMALLEST case shrinking can reach,
        // not the random one that first failed
        expects "a falsified property shrinks its counterexample"
            [
              "let go ="
              "    Check.quick \"ints are small\" Gen.int (fun x -> x < 100)"
              "    Check.quick \"lists are short\" (Gen.list Gen.int) (fun xs -> List.length xs < 3)"
              "    Check.quick \"no key is 7\" (Gen.hashMap (Gen.intRange 0 9) Gen.int) (fun m -> not (HashMap.containsKey 7 m))" ]
            "ints are small: falsified by 127\nlists are short: falsified by [0; -9; -19]\nno key is 7: falsified by hashMap [7 -> 14]\n"

        // Map/Set are AVL trees and HashMap/HashSet are classes, so DERIVED
        // equality would compare tree shape and object identity: both would
        // call equal contents unequal. F# compares content, and so do these.
        expects "collection equality is content-based, not shape or identity"
            [
              "let go ="
              "    print (Map.ofList [ (1, 1); (2, 2); (3, 3) ] = Map.ofList [ (3, 3); (2, 2); (1, 1) ])"
              "    print (Set.ofList [ 1; 2; 3; 4; 5 ] = Set.ofList [ 5; 4; 3; 2; 1 ])"
              "    print (HashMap.ofList [ (1, 1); (2, 2) ] = HashMap.ofList [ (2, 2); (1, 1) ])"
              "    print (HashSet.ofList [ 1; 2; 3 ] = HashSet.ofList [ 3; 2; 1 ])"
              "    print (Map.ofList [ (1, 1) ] = Map.ofList [ (1, 2) ])"
              "    print (Map.empty = Map.ofList [ (1, 1) ])"
              "    Check.quick \"set equality ignores insertion order\" (Gen.list Gen.int) (fun xs -> Set.ofList xs = Set.ofList (List.rev xs))"
              "    Check.quick \"map equality ignores insertion order\" (Gen.list (Gen.pair Gen.int Gen.int)) (fun kvs -> Map.ofList kvs = Map.ofList (List.rev (List.rev kvs)))" ]
            "True\nTrue\nTrue\nTrue\nFalse\nFalse\nset equality ignores insertion order: ok (200 cases)\nmap equality ignores insertion order: ok (200 cases)\n"

        // a GENERIC instance head (`Sized<list<'a>>`) has to resolve from a
        // generic function too, not only from a concrete call site
        expects "a generic instance head resolves through a generic function"
            [
              "class Sized<'a>"
              "    static size : 'a -> int"
              "instance Sized<int>"
              "    static size (x : int) = 1"
              "instance Sized<list<'a>>"
              "    when Sized<'a>"
              "    static size (xs : list<'a>) = List.fold (fun acc x -> acc + size x) 0 xs"
              "let total (xs : 'a) : int = size xs"
              "let go ="
              "    print (size 3)"
              "    print (size [ 1; 2; 3 ])"
              "    print (total [ 1; 2 ])" ]
            "1\n3\n2\n"

        // The same instance head at SEVERAL element types. One shared body
        // per generic instance is unsound: `size` at a float list must run
        // the float instance, not whichever one resolved first. This is the
        // shape that silently ran the `int` body for every element type.
        expects "a generic instance dispatches per element type"
            [
              "class Sized<'a>"
              "    static size : 'a -> int"
              "instance Sized<int>"
              "    static size (x : int) = 1"
              "instance Sized<float>"
              "    static size (x : float) = 2"
              "instance Sized<string>"
              "    static size (s : string) = 3"
              "instance Sized<list<'a>>"
              "    when Sized<'a>"
              "    static size (xs : list<'a>) = List.fold (fun acc x -> acc + size x) 0 xs"
              "let go ="
              "    print (size [ 1; 2; 3 ])"
              "    print (size [ 1.0; 2.0; 3.0 ])"
              "    print (size [ \"a\"; \"b\" ])"
              "    print (size [ [ 1.0 ]; [ 2.0; 3.0 ] ])" ]
            "3\n6\n6\n6\n"

        // ...and through an instance over ARRAYS, where the element type also
        // decides the REPRESENTATION: a generic body cannot ask a POD struct
        // array for its length, so the instance must be stamped per element.
        expects "a generic array instance dispatches per element type"
            [
              "class Sized<'a>"
              "    static size : 'a -> int"
              "instance Sized<int>"
              "    static size (x : int) = 1"
              "instance Sized<float>"
              "    static size (x : float) = 2"
              "instance Sized<'a[]>"
              "    when Sized<'a>"
              "    static size (xs : 'a[]) = size xs.[0]"
              "let go ="
              "    print (size [| 1; 2 |])"
              "    print (size [| 1.0; 2.0 |])"
              "    print (size [| [| 1.0 |] |])" ]
            "1\n2\n2\n"

        // The wire format the compiler writes both ends of. A pinned array of
        // an all-scalar struct is already a C-layout image, so `writeArray`
        // ships it with one memory.copy — and the reader lays it back down
        // the same way. 4 length bytes + 3 * 16 = 52.
        expects "a POD struct array serializes as a blit"
            [
              "[<Struct>]"
              "type V2d = { X : float; Y : float }"
              "instance Serialize<V2d>"
              "    static write (b : Buffer) (v : V2d) ="
              "        b.WriteFloat v.X"
              "        b.WriteFloat v.Y"
              "    static read (r : Reader) ="
              "        let x = r.ReadFloat ()"
              "        let y = r.ReadFloat ()"
              "        { X = x; Y = y }"
              "    static writeArray (b : Buffer) (xs : V2d[]) ="
              "        let n = xs.Length"
              "        b.WriteInt n"
              "        b.WriteBlock (Array.pin xs) (n * 16)"
              "    static readArray (r : Reader) ="
              "        let n = r.ReadInt ()"
              "        let xs : V2d[] = Array.zeroCreate n"
              "        let p = Array.pin xs"
              "        Memory.copy p (r.Block (n * 16)) (n * 16)"
              "        xs"
              "let go ="
              "    let pts = [| { X = 1.5; Y = 2.25 }; { X = 10.0; Y = 0.5 }; { X = -3.0; Y = 7.0 } |]"
              "    let b = Buffer 128"
              "    write b pts"
              "    print b.Length"
              "    let got : V2d[] = read (Reader b.Pointer)"
              "    print got.Length"
              "    print got.[0].X"
              "    print got.[2].Y" ]
            "52\n3\n1.5\n7\n"

        // Scalars, strings and nested arrays through the one generic array
        // instance, which never touches an array's representation itself.
        expects "the wire format round-trips scalars, strings and arrays"
            [
              "let go ="
              "    let b = Buffer 64"
              "    write b 42"
              "    write b 3.5"
              "    write b \"hello\""
              "    write b [| 10; 20; 30 |]"
              "    let r = Reader b.Pointer"
              "    print (read r : int)"
              "    print (read r : float)"
              "    print (read r : string)"
              "    let xs : int[] = read r"
              "    print xs.[2]"
              "    print b.Length" ]
            "42\n3.5\nhello\n30\n37\n"

        // A typed worker: `Command` and `Reply` are associated types, so one
        // declaration generates both ends of the crossing and they cannot
        // disagree. The message is 4 length + 1 tag + 4 count + 3 * 16 = 57
        // bytes — the V2d[] rides as its own image, nothing per element.
        expects "a worker exchanges typed messages as bytes"
            [
              "[<Struct>]"
              "type V2d = { X : float; Y : float }"
              "instance Serialize<V2d>"
              "    static write (b : Buffer) (v : V2d) ="
              "        b.WriteFloat v.X"
              "        b.WriteFloat v.Y"
              "    static read (r : Reader) ="
              "        let x = r.ReadFloat ()"
              "        let y = r.ReadFloat ()"
              "        { X = x; Y = y }"
              "    static writeArray (b : Buffer) (xs : V2d[]) ="
              "        b.WriteInt xs.Length"
              "        b.WriteBlock (Array.pin xs) (xs.Length * 16)"
              "    static readArray (r : Reader) ="
              "        let n = r.ReadInt ()"
              "        let xs : V2d[] = Array.zeroCreate n"
              "        Memory.copy (Array.pin xs) (r.Block (n * 16)) (n * 16)"
              "        xs"
              "type Job = Sum of V2d[]"
              "type Answer = Total of V2d"
              "instance Serialize<Job>"
              "    static write (b : Buffer) (j : Job) ="
              "        match j with"
              "        | Sum pts ->"
              "            b.WriteByte 0"
              "            write b pts"
              "    static read (r : Reader) ="
              "        let tag = r.ReadByte ()"
              "        Sum (read r)"
              "    static writeArray (b : Buffer) (xs : Job[]) = failwith \"n/a\""
              "    static readArray (r : Reader) = failwith \"n/a\""
              "instance Serialize<Answer>"
              "    static write (b : Buffer) (a : Answer) ="
              "        match a with"
              "        | Total v ->"
              "            b.WriteByte 0"
              "            write b v"
              "    static read (r : Reader) ="
              "        let tag = r.ReadByte ()"
              "        Total (read r)"
              "    static writeArray (b : Buffer) (xs : Answer[]) = failwith \"n/a\""
              "    static readArray (r : Reader) = failwith \"n/a\""
              "type Geometry = { Calls : int }"
              "instance Worker<Geometry>"
              "    type Command = Job"
              "    type Reply = Answer"
              "    static create () = { Calls = 0 }"
              "    static handle (w : Geometry) (j : Job) ="
              "        match j with"
              "        | Sum pts ->"
              "            let mutable sx = 0.0"
              "            let mutable sy = 0.0"
              "            let mutable i = 0"
              "            while i < pts.Length do"
              "                sx <- sx + pts.[i].X"
              "                sy <- sy + pts.[i].Y"
              "                i <- i + 1"
              "            Total { X = sx; Y = sy }"
              "    static writeCommand (h : WorkerHandle<Geometry>) (b : Buffer) (j : Job) = write b j"
              "    static readCommand (h : WorkerHandle<Geometry>) (r : Reader) = read r"
              "    static writeReply (h : WorkerHandle<Geometry>) (b : Buffer) (a : Answer) = write b a"
              "    static readReply (h : WorkerHandle<Geometry>) (r : Reader) = read r"
              "let theWorker : Geometry = create ()"
              "let selfHandle : WorkerHandle<Geometry> = WorkerHandle 0"
              "[<Export>]"
              "let dispatch (p : int) : int = Worker.serve selfHandle theWorker p"
              "let h : WorkerHandle<Geometry> = WorkerHandle 1"
              "let go ="
              "    let pts = [| { X = 1.0; Y = 2.0 }; { X = 3.0; Y = 4.0 }; { X = 10.0; Y = 20.0 } |]"
              "    let msg = Worker.encodeCommand h (Sum pts)"
              "    print msg.Length"
              "    let answer : Answer = Worker.decodeReply h (dispatch msg.Pointer)"
              "    match answer with"
              "    | Total v -> print (v.X + v.Y)" ]
            "57\n40\n"

        // Raw linear memory: the store the wire format is written into, and
        // the one a pinned array already lives in — so a blit between them is
        // a single instruction.
        expects "raw memory stores, loads and blits"
            [
              "[<Struct>]"
              "type V2d = { X : float; Y : float }"
              "let go ="
              "    let p = Memory.alloc 64"
              "    Memory.storeInt p 42"
              "    Memory.storeFloat (p + 8) 3.5"
              "    Memory.storeByte (p + 16) 200"
              "    Memory.storeInt64 (p + 24) 1234567890123L"
              "    print (Memory.loadInt p)"
              "    print (Memory.loadFloat (p + 8))"
              "    print (Memory.loadByte (p + 16))"
              "    print (Memory.loadInt64 (p + 24))"
              "    let pts = [| { X = 1.5; Y = 2.25 }; { X = 10.0; Y = 0.5 } |]"
              "    let dst = Memory.alloc 32"
              "    Memory.copy dst (Array.pin pts) 32"
              "    print (Memory.loadFloat dst)"
              "    print (Memory.loadFloat (dst + 24))" ]
            "42\n3.5\n200\n1234567890123\n1.5\n0.5\n"

        // a lambda INSIDE a function's own parameter lambda is a real closure,
        // so a scalar parameter it reads cannot live on a raw rail — the env
        // slot is anyref. Getting this wrong did not even produce a module
        // that validated.
        // A quotation survives to run time as a TREE, not as text: a splice
        // grafts a SUBTREE, so composition cannot be reinterpreted by
        // precedence and nothing is ever parsed a second time.
        expects "quotations are trees, and a splice grafts a subtree"
            [
              "let baseName (n : string) ="
              "    let mutable r = \"\""
              "    let mutable i = 0"
              "    let mutable stop = false"
              "    while i < n.Length do"
              "        if n.[i] = '_' && i + 1 < n.Length && n.[i + 1] = 'q' then stop <- true"
              "        elif not stop then r <- r + string n.[i]"
              "        i <- i + 1"
              "    if stop then r + \"*\" else r"
              "let rec shape (c : CodeTree) ="
              "    match c with"
              "    | CInt v -> \"Int(\" + string v + \")\""
              "    | CStr v -> \"Str\""
              "    | CBool v -> \"Bool\""
              "    | CName n -> \"Name(\" + baseName n + \")\""
              "    | CBin (op, l, r) -> \"Bin(\" + op + \",\" + shape l + \",\" + shape r + \")\""
              "    | CApp (f, args) -> \"App(\" + shape f + \",\" + string (List.length args) + \")\""
              "    | CLet (n, v, b) -> \"Let(\" + baseName n + \",\" + shape v + \",\" + shape b + \")\""
              "    | CIf (c2, t, e) -> \"If(\" + shape c2 + \",\" + shape t + \",\" + shape e + \")\""
              "let n = 41"
              "let f (x : int) = x"
              "let a = <@ 1 @>"
              "let b = <@ %a + 2 @>"
              "let c = <@ %b * 3 @>"
              "let blk = <@ let y = f n"
              "             if y > 1 then y + 1 else 0 @>"
              "let go ="
              "    print (shape (<@ n + 1 @>).Raw)"
              "    print (shape c.Raw)"
              "    print (shape blk.Raw)" ]
            ("Bin(+,Name(n),Int(1))\n"
             + "Bin(*,Bin(+,Int(1),Int(2)),Int(3))\n"
             + "Let(y*,App(Name(f),1),If(Bin(>,Name(y*),Int(1)),Bin(+,Name(y*),Int(1)),Int(0)))\n")

        // HYGIENE: a binder inside a quotation is renamed per quotation site,
        // so a spliced fragment's free names cannot be captured by a binder
        // that merely spells the same
        // `: %ty` — a TYPE spliced into a quoted signature, which is what a
        // generator needs to emit one declaration per field
        // the shape a deriving plugin emits: a MEMBER whose signature carries a
        // spliced type, and a record TYPE with a spliced field type
        // splices reach every position: expression, TYPE, and PATTERN
        // both .NET overloads: a single char and a set of them
        expects "TrimStart and TrimEnd take a char or a set"
            [ "let go ="
              "    print (\"xxhixx\".TrimStart 'x')"
              "    print (\"xxhixx\".TrimStart [| 'x' |])"
              "    print (\"hixx\".TrimEnd 'x')"
              "    print (\"hixx\".TrimEnd [| 'x' |])" ]
            "hixx\nhixx\nhi\nhi\n"

        expects "patterns can be spliced into a quoted match"
            [ "let p : QPat = QCase (\"Some\", [ QVar \"v\" ])"
              "let q : Code<int> = <@ match Some 1 with"
              "                       | %p -> 1"
              "                       | None -> 0 @>"
              "let go = print (Code.render q.Raw)" ]
            "match (Some 1) with\n    | Some v -> 1\n    | None -> 0\n"

        expects "members and record types can be quoted, with spliced types"
            [ "let ty : QTy = QTyName \"int\""
              "let t : QTy = QTyName \"string\""
              "let m : Code<unit> = <@ member x.Bla (a : %ty) : %ty = a @>"
              "let r : Code<unit> = <@ type Row = { Id : int; Label : %t } @>"
              "let go ="
              "    (match m.Raw with"
              "     | CDMember (self, name, ps, ret, body) ->"
              "         print (self + \".\" + name)"
              "         print (Code.renderTy ret)"
              "         print (string (List.length ps))"
              "     | _ -> print \"?\")"
              "    (match r.Raw with"
              "     | CDRecord (n, fs) ->"
              "         print n"
              "         print (String.concat \",\" (List.map (fun (f, ft) -> f + \":\" + Code.renderTy ft) fs))"
              "     | _ -> print \"?\")" ]
            "x.Bla\nint\n1\nRow\nId:int,Label:string\n"

        expects "types can be spliced into a quoted signature"
            [ "let t : QTy = QTyName \"string\""
              "let r : QTy = QTyApp (\"list\", [ QTyName \"int\" ])"
              "let d : Code<unit> = <@ let f (x : %t) : %r = [ 1 ] @>"
              "let go ="
              "    match d.Raw with"
              "    | CDLet (n, ps, ret, body) ->"
              "        print n"
              "        print (Code.renderTy ret)"
              "        (match ps with"
              "         | [ (pn, pt) ] -> print (Code.renderTy pt)"
              "         | _ -> print \"?\")"
              "    | _ -> print \"?\"" ]
            "f\nlist<int>\nstring\n"

        expects "a quoted binder cannot capture a spliced name"
            [
              "let baseName (n : string) ="
              "    let mutable r = \"\""
              "    let mutable i = 0"
              "    let mutable stop = false"
              "    while i < n.Length do"
              "        if n.[i] = '_' && i + 1 < n.Length && n.[i + 1] = 'q' then stop <- true"
              "        elif not stop then r <- r + string n.[i]"
              "        i <- i + 1"
              "    if stop then r + \"*\" else r"
              "let rec shape (c : CodeTree) ="
              "    match c with"
              "    | CInt v -> string v"
              "    | CName n -> baseName n"
              "    | CBin (op, l, r) -> shape l + op + shape r"
              "    | CLet (n, v, b) -> \"let \" + baseName n + \"=\" + shape v + \" in \" + shape b"
              "    | _ -> \"?\""
              "let y = 99"
              "let body : Code<int> = <@ y + 1 @>"
              "let captured : Code<int> = <@ let y = 5"
              "                              %body @>"
              "let ownBody : Code<int> = <@ let z = 5"
              "                             z + 1 @>"
              "let go ="
              // the quoted binder is renamed (y*), the SPLICED y is not: no capture
              "    print (shape captured.Raw)"
              // and a binder is still visible to its own body
              "    print (shape ownBody.Raw)" ]
            "let y*=5 in y+1\nlet z*=5 in z*+1\n"

        expects "a returned closure captures a scalar parameter"
            [ "let addN (n : int) = (fun x -> x * 2 + n)"
              "let mulThen (a : int) (b : int) = (fun x -> x * a + b)"
              "let viaLet (n : int) ="
              "    (fun x ->"
              "        let doubled = x * 2"
              "        doubled + n)"
              "let go ="
              "    print (addN 10 5)"
              "    print (mulThen 3 4 5)"
              "    print (viaLet 7 5)"
              "    let f = addN 1"
              "    print (f 2)" ]
            "20\n19\n17\n5\n"

        expects "generic class hierarchy with virtual dispatch through the base"
            [ "[<AbstractClass>]"
              "type Node<'k>(kind : int) ="
              "    member x.Kind = kind"
              "    abstract member Count : unit -> int"
              "    abstract member Add : 'k -> Node<'k>"
              "type Leaf<'k>(key : 'k) ="
              "    inherit Node<'k>(1)"
              "    member x.Key = key"
              "    override x.Count () = 1"
              "    override x.Add (k : 'k) = Inner<'k>(Leaf<'k>(k) :> Node<'k>, x :> Node<'k>) :> Node<'k>"
              "and Inner<'k>(l : Node<'k>, r : Node<'k>) ="
              "    inherit Node<'k>(2)"
              "    override x.Count () = l.Count () + r.Count ()"
              "    override x.Add (k : 'k) = Inner<'k>(l.Add k, r) :> Node<'k>"
              "let go ="
              "    let a = Leaf<int>(1) :> Node<int>"
              "    print (a.Count ())"
              "    let b = a.Add 2"
              "    print (b.Count ())"
              "    print ((b.Add 3).Count ())"
              "    print b.Kind"
              "    let mutable total = 0"
              "    for n in [ a; b ] do total <- total + n.Count ()"
              "    print total" ]
            "1\n2\n3\n2\n3\n"

        expects "Set: the MapExt surface over a value-less AVL tree"
            [ "let s1 = Set.ofList [ 3; 1; 4; 1; 5 ]"
              "let s2 = Set.ofList [ 4; 5; 9 ]"
              "let ss (x : Set<int>) = String.concat \",\" (List.map (fun v -> string v) (Set.toList x))"
              "let go ="
              "    print (ss s1 + \" | \" + string (Set.count s1))"
              "    print (ss (Set.add 2 s1) + \" | \" + ss (Set.remove 3 s1))"
              "    print (ss (Set.union s1 s2) + \" | \" + ss (Set.intersect s1 s2) + \" | \" + ss (Set.difference s1 s2))"
              "    print (string (Set.minElement s1) + \" \" + string (Set.maxElement s1))"
              "    print (ss (Set.removeMin s1) + \" | \" + ss (Set.removeMax s1))"
              "    let lo, here, hi = Set.split 4 s1"
              "    print (ss lo + \" | \" + string here + \" | \" + ss hi)"
              "    print (ss (Set.range 3 5 s1))"
              "    let below, at, above = Set.neighbours 4 s1"
              "    print ((match below with Some v -> string v | None -> \"-\") + string at + (match above with Some v -> string v | None -> \"-\"))"
              "    let addd, remd = Set.computeDelta s1 s2"
              "    print (ss addd + \" | \" + ss remd)"
              "    let st, ea, er = Set.applyDelta s1 addd remd"
              "    print (ss st + \" | \" + ss ea + \" | \" + ss er)"
              "    print (ss (Map.keySet (Map.ofList [ (7, \"x\"); (2, \"y\") ])))"
              "    print (string (Set.isEmpty Set.empty) + string (Set.count (Set.singleton 1)))" ]
            "1,3,4,5 | 4\n1,2,3,4,5 | 1,4,5\n1,3,4,5,9 | 4,5 | 1,3\n1 5\n3,4,5 | 1,3,4\n1,3 | True | 5\n3,4,5\n3True5\n9 | 1,3\n4,5,9 | 9 | 1,3\n2,7\nTrue1\n"

        expects "HashMap and HashSet: combinators, deltas, O(1) keySet"
            [ "let h = HashMap.ofList [ (1, \"a\"); (2, \"b\"); (3, \"c\") ]"
              "let g = HashMap.ofList [ (2, \"B\"); (4, \"d\") ]"
              "let sh (t : HashNode<int, string>) = String.concat \",\" (List.map (fun (k, v) -> string k + v) (List.sortBy fst (HashMap.toList t)))"
              "let sl (x : HashNode<int, int>) = String.concat \",\" (List.map (fun v -> string v) (List.sort (HashSet.toList x)))"
              "let go ="
              "    print (sh (HashMap.union h g))"
              "    print (sh (HashMap.unionWith (fun k a b -> a + b) h g))"
              "    print (sh (HashMap.difference h g))"
              "    print (sh (HashMap.choose (fun k v -> if k > 1 then Some v else None) h))"
              "    let d = HashMap.computeDelta h g"
              "    print (String.concat \",\" (List.map (fun (k, op) -> string k + (match op with SetOp v -> \":=\" + v | RemoveOp -> \":del\")) (List.sortBy fst (HashMap.toList d))))"
              "    let st, eff = HashMap.applyDelta h d"
              "    print (sh st + \" | \" + string (HashMap.count eff))"
              "    print (sl (HashMap.keySet h))"
              "    let s1 = HashSet.ofList [ 1; 2; 3 ]"
              "    let s2 = HashSet.ofList [ 3; 4 ]"
              "    print (sl (HashSet.union s1 s2) + \" | \" + sl (HashSet.intersect s1 s2) + \" | \" + sl (HashSet.difference s1 s2))"
              "    print (string (HashSet.isSubset (HashSet.ofList [1;2]) s1) + string (HashSet.isProperSubset s1 s1))"
              "    let sd = HashSet.computeDelta s1 s2"
              "    print (String.concat \",\" (List.map (fun (k, op) -> string k + (match op with SetOp _ -> \":+\" | RemoveOp -> \":-\")) (List.sortBy fst (HashMap.toList sd))))" ]
            "1a,2B,3c,4d\n1a,2bB,3c,4d\n1a,3c\n2b,3c\n1:del,2:=B,3:del,4:=d\n2B,4d | 4\n1,2,3\n1,2,3,4 | 3 | 1,2\nTrueFalse\n1:-,2:-,4:+\n"

        expects "arrays: zeroCreate, index get/set, Length"
            [ "let go ="
              "    let a = Array.zeroCreate 3"
              "    a.[0] <- 10"
              "    a.[2] <- 32"
              "    print (a.[0] + a.[1] + a.[2])"
              "    print a.Length" ]
            "42\n3\n"
    ]
