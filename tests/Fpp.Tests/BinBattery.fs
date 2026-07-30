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

        // a lambda INSIDE a function's own parameter lambda is a real closure,
        // so a scalar parameter it reads cannot live on a raw rail — the env
        // slot is anyref. Getting this wrong did not even produce a module
        // that validated.
        // a quotation is CHECKED code that survives to run time as a Code
        // value; splices compose, including a splice of a spliced quote
        expects "quotations evaluate to code, and splices compose"
            [ "let n = 41"
              "let quoted = <@ n + 1 @>"
              "let a = <@ 1 @>"
              "let b = <@ %a + 2 @>"
              "let c = <@ %b * 3 @>"
              "let go ="
              "    print (Code.text quoted)"
              "    print (Code.text c)"
              "    print (Code.text (Code.ofText \"hand made\"))" ]
            // the splices are PARENTHESISED: composing code must not lose to
            // precedence, so `%b * 3` over `b = %a + 2` means (1 + 2) * 3
            "n + 1 \n((1 )+ 2 )* 3 \nhand made\n"

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
