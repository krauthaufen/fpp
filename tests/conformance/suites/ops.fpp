// Operator members, from dotnet/fsharp tests/fsharp/core/members/ops/test.fsx
// in the common F#/F++ subset. Dropped: DateTime/TimeSpan overload probing,
// `op_Addition` spelled by name, SRTP modules (statically resolved type
// parameters), enum-operator tests, and the subtype-widening module
// (`(x1 : D) + (x2 : C)` resolves through subsumption in F#; F++ operator
// members are typeclass instances and match the operand pair exactly).
module Core_members_ops

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

module FuncTest =

    type func =
        class
            val numCalls : int ref
            val impl : int -> int option
            member x.Invoke (y : int) = (x.numCalls := !x.numCalls + 1); x.impl y
            new (f : int -> int option) = { numCalls = ref 0; impl = f }
            static member (>>>>) ((f : func), (g : func)) =
                new func(fun x -> match f.Invoke x with None -> None | Some b -> g.Invoke b)
            static member (<<<<) ((f : func), (g : func)) =
                new func(fun x -> match g.Invoke x with None -> None | Some b -> f.Invoke b)
        end

    let konst (a : int) = new func(fun x -> Some a)
    let morph (f : int -> int) = new func(fun x -> Some (f x))

    let something = (morph (fun x -> x * x)) >>>> (morph (fun x -> x + x))
    let something2 = (morph (fun x -> x * x)) <<<< (morph (fun x -> x + x))

    test "cn39233" (something.Invoke 3 = Some 18)
    test "cn39233b" (something2.Invoke 3 = Some 36)
    test "cn39233c" (konst 7 |> (fun k -> k.Invoke 100) = Some 7)
    test "cn39233d" (!something.numCalls = 1)

module OverloadSamples =

    // simple overloading picked by the operand's type
    let f1 x = x + 1.0
    let f2 x = x + 1.0f
    let f3 x = x + 2
    test "ovl1" (f1 2.5 = 3.5)
    test "ovl2" (f2 2.0f = 3.0f)
    test "ovl3" (f3 40 = 42)

    // overloading on your own type
    type IntVector =
        | V of int array
        static member (+) (V x, V y) =
            if x.Length <> y.Length then invalidArg "arg" "IntVectorOps.add"
            V (Array.init x.Length (fun i -> x.[i] + y.[i]))

    let res6 = V [| 1; 2; 3 |] + V [| 3; 2; 1 |]
    test "iv1" (match res6 with V a -> a.Length = 3 && a.[0] = 4 && a.[1] = 4 && a.[2] = 4)

    // generic vectors carrying a dictionary of operations
    type NumberOps<'a> =
        { zero : 'a
          one : 'a
          add : 'a -> 'a -> 'a
          mul : 'a -> 'a -> 'a
          neg : 'a -> 'a }

    let intOps = { zero = 0; one = 1; add = (+); mul = ( * ); neg = (fun x -> -x) }
    let floatOps = { zero = 0.0; one = 1.0; add = (+); mul = ( * ); neg = (fun x -> -x) }

    // the fsc original attaches (+) through a type AUGMENTATION; a member
    // extension on a GENERIC type miscompiles here (pre-existing, see the
    // status doc known issues), so the member is declared with the type
    type GenericVector<'a> =
        { ops : NumberOps<'a>
          arr : 'a array }
        static member (+) ((x : GenericVector<'a>), (y : GenericVector<'a>)) =
            { ops = x.ops
              arr = Array.init x.arr.Length (fun i -> x.ops.add x.arr.[i] y.arr.[i]) }

    let create ops arr = { ops = ops; arr = arr }

    let IGV arr = create intOps arr
    let FGV arr = create floatOps arr

    let f8 (x : GenericVector<int>) = x + IGV [| 1; 2; 3 |]
    let f9 (x : GenericVector<float>) = x + FGV [| 1.0 |]
    let twice (x : GenericVector<'a>) (y : GenericVector<'a>) = x + y

    let r8 = f8 (IGV [| 10; 20; 30 |])
    test "gv1" (r8.arr.Length = 3 && r8.arr.[0] = 11 && r8.arr.[1] = 22 && r8.arr.[2] = 33)
    let r9 = f9 (FGV [| 1.5 |])
    test "gv2" (r9.arr.Length = 1 && r9.arr.[0] = 2.5)
    let r10 = twice (FGV [| 2.0; 3.0 |]) (FGV [| 4.0; 5.0 |])
    test "gv3" (r10.arr.[0] = 6.0 && r10.arr.[1] = 8.0)

module StateMonadTest =

    type IO<'a> =
        { impl : unit -> 'a }
        member f.Invoke () = f.impl ()
        static member Result (r : 'a) : IO<'a> = { impl = (fun () -> r) }
        member f.Bind (g : 'a -> IO<'b>) : IO<'b> = g (f.impl ())

    let (>>=) (f : IO<'a>) (g : 'a -> IO<'b>) = f.Bind g
    let result (x : 'a) : IO<'a> = { impl = (fun () -> x) }
    let mcons (p : IO<'a>) (q : IO<'a list>) = p >>= (fun x -> q >>= (fun y -> result (x :: y)))
    let sequence (l : IO<'a> list) : IO<'a list> =
        List.foldBack mcons l (result [])

    let r = (sequence [ result 1; result 2; result 3 ]).Invoke ()
    test "sm1" (r = [ 1; 2; 3 ])
    test "sm2" ((result 5 >>= (fun x -> result (x * 2))).Invoke () = 10)

module BasicOverloadTests =

    let f4 x = 1 + x
    let f5 x = 1 - x
    let f17 (x1 : float) x2 = x1 * x2
    let f18 (x1 : int) x2 = x1 * x2
    let f19 x1 (x2 : int) = x1 * x2
    let f20 x1 (x2 : float) = x1 * x2
    let f21 x1 (x2 : string) = x1 + x2
    let f22 (x1 : string) x2 = x1 + x2
    let f27 x = x + x
    let f28 x =
        let g x = x + x in
        g x
    let f29 x =
        let g x = x + 1.0 in
        g x
    let f30 x =
        let g x = x + "a" in
        g x + "3"

    test "bo1" (f4 41 = 42)
    test "bo2" (f5 43 = -42)
    test "bo3" (f17 2.0 3.0 = 6.0)
    test "bo4" (f18 6 7 = 42)
    test "bo5" (f19 6 7 = 42)
    test "bo6" (f20 2.5 2.0 = 5.0)
    test "bo7" (f21 "a" "b" = "ab")
    test "bo8" (f22 "c" "d" = "cd")
    test "bo9" (f27 21 = 42)
    test "bo10" (f28 "x" = "xx")
    test "bo11" (f29 1.5 = 2.5)
    test "bo12" (f30 "b" = "ba3")

module MiscOperatorOverloadTests =

    let rec findBounding2Power b tp = if b <= tp then tp else findBounding2Power b (tp * 2)
    let leastBounding2Power b = findBounding2Power b 1

    let inline sumfR f ((a : int), (b : int)) =
        let mutable res = 0.0 in
        for i = a to b do
            res <- res + f i
        res

    test "mo1" (leastBounding2Power 100 = 128)
    test "mo2" (leastBounding2Power 1 = 1)
    test "mo3" (leastBounding2Power 1000 = 1024)
    test "mo4" (sumfR (fun i -> float i) (1, 10) = 55.0)

printfn "DONE tests=%d failures=%d" ntests failures
