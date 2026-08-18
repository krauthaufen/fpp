// Incremental (primary-constructor) classes, from dotnet/fsharp
// tests/fsharp/core/members/incremental/test.fsx in the common F#/F++
// subset. Dropped: the WinForms/Drawing Area modules, IEvent (no event
// surface), and the address-of-value-type modules. Runtime asserts added
// where the original only compiled (the fsc suite is mostly shape tests).
module Core_members_incremental

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

module AddressOfMutableRecordField =
    type Rect = { mutable X : int; mutable Y : int }
    type RectR = { mutable field : Rect }
    let f (x : RectR) = x.field.X <- 10
    let boxR = { field = { X = 0; Y = 0 } }
    test "recfield1" (boxR.field.X = 0)
    f boxR
    test "recfield2" (boxR.field.X = 10)

module MinorTest =
    type A<'a>(x : 'a) =
        class
            let (y : 'a) = x
            member this.X = y
        end
    let x1 = new A<string>("abc")
    let x2 = new A<int>(3)
    let x3 = new A<int64>(3L)
    test "minor1" (x1.X = "abc")
    test "minor2" (x2.X = 3)
    test "minor3" (x3.X = 3L)

module Misc =
    type AList(a : int) =
        class
            let x1 = a + 1
            let y2 = x1 + 1
            let y3 = 3
            member pairs_this.Pair () = x1, y2
        end
    let a = new AList(12)
    test "alist1" (a.Pair () = (13, 14))

module Wire =
    // the abstract wire over LISTENER LISTS, the object-expression factory
    // (the fsc original hangs this on IEvent, which has no counterpart)
    [<AbstractClass>]
    type Wire<'a>() =
        class
            abstract member Send : 'a -> unit
            abstract member Listen : ('a -> unit) -> unit
        end
    let createWire () =
        let listeners = ref [] in
        { new Wire<'a>() with
            member __.Send (x) = List.iter (fun f -> f x) (!listeners)
            member __.Listen (f) = listeners := f :: !listeners }
    let w : Wire<int> = createWire ()
    let acc = ref 0
    w.Listen (fun x -> acc := !acc + x)
    w.Listen (fun x -> acc := !acc + 100 * x)
    w.Send 3
    test "wire1" (!acc = 303)

module WireVariations =
    type Wire2(z : int) =
        class
            let z = z
            member this.Send (x : int) = 1 + z + x
        end
    test "w2" (Wire2(10).Send 5 = 16)

    type Wire3<'a>(z : 'a) =
        class
            let listeners = (z : 'a)
            member this.Send (x : 'a) = x
        end
    test "w3" (Wire3<string>("s").Send "t" = "t")

    type Wire4<'a>(z : 'a) =
        class
            let listeners = ref ([] : ('a -> unit) list)
            member this.Send (x : 'a) = List.iter (fun f -> f x) (!listeners)
            member this.Listen (f : 'a -> unit) = listeners := f :: !listeners
        end
    let w4 = Wire4<int>(0)
    let got = ref 0
    w4.Listen (fun x -> got := x)
    w4.Send 42
    test "w4" (!got = 42)

    type Wire6<'a>(z : 'a) =
        class
            let mutable listeners = ([] : ('a -> unit) list)
            member this.Send (x : 'a) = List.iter (fun f -> f x) listeners
            member this.Listen (f : 'a -> unit) = listeners <- f :: listeners
        end
    let w6 = Wire6<string>("")
    let sgot = ref ""
    w6.Listen (fun x -> sgot := x)
    w6.Send "hi"
    test "w6" (!sgot = "hi")

    type Wire7<'a>(z : 'a) =
        class
            let listeners = 12
            let zz : 'a = z
            member this.SendA (x : int) = this, listeners
            member this.SendB (x : int) = this, listeners
        end
    let w7 = Wire7<int>(1)
    test "w7" (snd (w7.SendA 0) = 12 && snd (w7.SendB 0) = 12)

    type Wire9<'a>(z : 'a) =
        class
            let mutable listeners = ([] : int list)
            let zz : 'a = z
            member this.Send (x : int) =
                let ls : int list = 1 :: 2 :: listeners in
                List.map (fun x -> x + 1) ls
        end
    test "w9" (Wire9<int>(0).Send 0 = [ 2; 3 ])

    type Wire10<'a>(z : 'a) =
        class
            let mutable listeners = ([] : int list)
            let zz : 'a = z
            member this.Send (x : int) =
                let ls : int list = listeners @ [ 1 ] in
                List.map (fun f -> f) ls
        end
    test "w10" (Wire10<int>(0).Send 0 = [ 1 ])

    type Wire14<'a>(z : int) =
        class
            let mutable listeners = let zz : int = z in ([] : int list)
            member this.Send (x : 'a) = listeners
        end
    test "w14" (Wire14<string>(1).Send "x" = [])

printfn "DONE tests=%d failures=%d" ntests failures
