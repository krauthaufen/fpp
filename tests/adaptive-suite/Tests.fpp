// ==== FDA test suite, hand-ported ================================
// Appended to the ported library (port-adaptive.py output). Sources:
// src/Test/FSharp.Data.Adaptive.Tests/{AVal,Transaction}.fs — the plain
// [<Test>] cases; FsCheck properties are out of scope here (they need the
// reference implementation and a generator harness).
//
// Divergences from the originals are marked DIV; the harness reports
// FAIL lines and a final PASSED/FAILED count.

let mutable passedCount = 0
let mutable failedCount = 0

let test (name : string) (f : unit -> unit) : unit =
    let mutable ok = true
    (try f () with Failure msg ->
        ok <- false
        printfn "FAIL %s: %s" name msg)
    if ok then passedCount <- passedCount + 1
    else failedCount <- failedCount + 1

let check (msg : string) (b : bool) : unit =
    if not b then failwith msg

let checkInt (msg : string) (expected : int) (actual : int) : unit =
    if actual <> expected then
        failwith (msg + ": expected " + string expected + " got " + string actual)

let checkStr (msg : string) (expected : string) (actual : string) : unit =
    if actual <> expected then
        failwith (msg + ": expected " + expected + " got " + actual)

// EagerVal from AVal.fs: an AdaptiveObject that re-evaluates on MARK and
// swallows the change when the value is unchanged.
type EagerVal<'T>(input : aval<'T>) =
    inherit AdaptiveObject()

    let mutable last : Option<'T> = None

    override x.MarkObject() =
        let v = input.GetValue (AdaptiveToken(x :> IAdaptiveObject))
        match last with
        | Some old when DefaultEquality.equals old v -> false
        | _ -> true

    member x.GetValue(token : AdaptiveToken) : 'T =
        x.EvaluateAlways token (fun token ->
            let res = input.GetValue token
            last <- Some res
            res)

    interface IAdaptiveValue with
        member x.Accept (v : IAdaptiveValueVisitor<'R>) = v.Visit x
        member x.GetValueUntyped(t) = x.GetValue t :> obj
        member x.ContentType = typeof<'T>

    interface IAdaptiveValue<'T> with
        member x.GetValue(t) = x.GetValue t

let go =
    // ---- AVal.fs -------------------------------------------------
    test "[AVal] map constant" (fun () ->
        let a = AVal.constant 1
        let b = AVal.map id a
        check "IsConstant" b.IsConstant)

    test "[AVal] map2 constant" (fun () ->
        let a = AVal.constant 1
        let b = AVal.constant 2
        let t = AVal.map2 (fun a b -> (a, b)) a b
        check "IsConstant" t.IsConstant)

    test "[AVal] map3 constant" (fun () ->
        let a = AVal.constant 1
        let b = AVal.constant 2
        let c = AVal.constant 3
        let t = AVal.map3 (fun a b c -> (a, b, c)) a b c
        check "IsConstant" t.IsConstant)

    test "[AVal] bind content" (fun () ->
        let a = AVal.constant 10
        let b = AVal.init "b" |> AVal.map id
        let c = AVal.init "c" |> AVal.map id
        let t = a |> AVal.bind (fun va -> if va = 10 then b else c)
        check "bind returns b" (System.Object.ReferenceEquals (t, b)))

    test "[AVal] eager evaluation" (fun () ->
        let a = AVal.init 0
        let short = AVal.init "a"
        let long = AVal.init "a" |> AVal.map id |> AVal.map id |> AVal.map id
        let different = AVal.init "b" |> AVal.map id |> AVal.map id |> AVal.map id |> AVal.map id |> AVal.map id
        let dynamic =
            a |> AVal.bind (fun l ->
                if l = 0 then short :> aval<string>
                elif l = 1 then long
                else different)
        let eager = EagerVal(dynamic) :> aval<string>
        checkStr "initial" "a" (AVal.force eager)
        checkInt "initial level" 2 eager.Level
        // larger level (LevelChangedException inside), content unchanged
        transact (fun () -> a.Value <- 1)
        check "not out-of-date" (not eager.OutOfDate)
        checkStr "unchanged" "a" (AVal.force eager)
        check "level > long" (eager.Level > long.Level)
        // actually changes content
        transact (fun () -> a.Value <- 2)
        check "out-of-date" eager.OutOfDate
        checkStr "changed" "b" (AVal.force eager)
        check "level > different" (eager.Level > different.Level))

    test "[AVal] eager marking" (fun () ->
        let a = AVal.init 0
        let mod2 = a |> AVal.map (fun v -> v % 2)
        let eager = EagerVal(mod2) :> aval<int>
        let output = eager |> AVal.map id
        checkInt "initial" 0 (AVal.force output)
        transact (fun () -> a.Value <- 2)
        check "2: not out-of-date" (not output.OutOfDate)
        checkInt "2: value" 0 (AVal.force output)
        transact (fun () -> a.Value <- 1)
        check "1: out-of-date" output.OutOfDate
        checkInt "1: value" 1 (AVal.force output)
        transact (fun () -> a.Value <- 3)
        check "3: not out-of-date" (not output.OutOfDate)
        checkInt "3: value" 1 (AVal.force output)
        transact (fun () -> a.Value <- 0)
        check "0: out-of-date" output.OutOfDate
        checkInt "0: value" 0 (AVal.force output))

    test "[AVal] nop change evaluation" (fun () ->
        let input = AVal.init 5
        let a = AVal.map id input
        let b = AVal.map (fun v -> -v) input
        let c = AVal.map2 (fun x y -> x + y) a b
        let mutable mapCounter = 0
        let d = c |> AVal.map (fun v -> mapCounter <- mapCounter + 1; v)
        checkInt "force" 0 (AVal.force d)
        checkInt "evaluated once" 1 mapCounter
        mapCounter <- 0
        transact (fun () -> input.Value <- 10)
        check "out-of-date" d.OutOfDate
        checkInt "force after" 0 (AVal.force d)
        checkInt "not re-evaluated" 0 mapCounter)

    test "[AVal] ChangeableLazyVal working" (fun () ->
        let mutable computeCount = 0
        let compute (v : int) = fun () ->
            computeCount <- computeCount + 1
            v
        let sinceLast () =
            let v = computeCount
            computeCount <- 0
            v
        let v = ChangeableLazyVal(compute 1)
        let t = v |> AVal.map (fun v -> v + 2)
        checkInt "force" 3 (AVal.force t)
        checkInt "computed" 1 (sinceLast ())
        transact (fun () -> v.Update(compute 0))
        checkInt "update computes" 1 (sinceLast ())
        transact (fun () -> v.Update(compute 3))
        checkInt "pending update lazy" 0 (sinceLast ())
        checkInt "force new" 5 (AVal.force t)
        checkInt "computed once" 1 (sinceLast ())
        transact (fun () -> v.Update(compute 3))
        checkInt "same value computes" 1 (sinceLast ())
        check "not out-of-date" (not t.OutOfDate))

    test "[AVal] map non-adaptive and bind" (fun () ->
        let v = AVal.init true
        let a = AVal.constant 0
        let b = AVal.constant 1
        let output = v |> AVal.map id |> AVal.mapNonAdaptive id |> AVal.bind (fun flag -> if flag then a else b)
        checkInt "true" 0 (AVal.force output)
        transact (fun () -> v.Value <- false)
        checkInt "false" 1 (AVal.force output))

    // DIV: the original forces a GC between setup and change to prove the
    // non-adaptive link stays alive; there is no GC.Collect here, so this
    // checks the propagation only.
    test "[AVal] mapNonAdaptive GC correct" (fun () ->
        let v = cval 10
        let t = v |> AVal.mapNonAdaptive (fun x -> x + 1) |> AVal.map id
        checkInt "initial" 11 (AVal.force t)
        transact (fun () -> v.Value <- 100)
        checkInt "after" 101 (AVal.force t))

    test "[AVal] multi map non-adaptive and bind" (fun () ->
        let v = AVal.init true
        let a = AVal.constant 0
        let b = AVal.constant 1
        let output = v |> AVal.map id |> AVal.mapNonAdaptive id |> AVal.mapNonAdaptive id |> AVal.bind (fun flag -> if flag then a else b)
        checkInt "true" 0 (AVal.force output)
        transact (fun () -> v.Value <- false)
        checkInt "false" 1 (AVal.force output))

    // ---- Transaction.fs ------------------------------------------
    test "[Transaction] transact sets/restores current" (fun () ->
        transact (fun () ->
            let a = Transaction.Current
            transact (fun () ->
                let b = Transaction.Current
                let differ =
                    match a, b with
                    | ValueSome x, ValueSome y -> not (System.Object.ReferenceEquals (x, y))
                    | _ -> false
                check "inner differs" differ)
            let restored =
                match a, Transaction.Current with
                | ValueSome x, ValueSome y -> System.Object.ReferenceEquals (x, y)
                | _ -> false
            check "restored" restored)
        check "cleared" (match Transaction.Current with ValueNone -> true | ValueSome _ -> false))

    test "[Transaction] transact sets/restores current on exception" (fun () ->
        transact (fun () ->
            let a = Transaction.Current
            (try transact (fun () -> failwith "inner exn")
             with e -> ())
            let restored =
                match a, Transaction.Current with
                | ValueSome x, ValueSome y -> System.Object.ReferenceEquals (x, y)
                | _ -> false
            check "restored" restored))

    test "[AVal] callbacks" (fun () ->
        let f = cval true
        let a = cval 10
        let b = cval 5
        let b2 = b :> aval<int>
        let a2 = a |> AVal.map id |> AVal.map id |> AVal.map id
        let result = f |> AVal.bind (fun flag -> if flag then b2 else a2)
        let mutable wasrun = false
        let mutable expected = 5
        let sub = result.AddCallback(fun v ->
            wasrun <- true
            checkInt "callback value" expected v)
        check "initial ran" wasrun
        wasrun <- false
        let change (action : unit -> Option<int>) =
            let shouldRun =
                transact (fun () ->
                    wasrun <- false
                    match action () with
                    | Some e -> expected <- e; true
                    | None -> false)
            check "callback run matches" (wasrun = shouldRun)
            wasrun <- false
        change (fun () -> f.Value <- false; Some 10)
        change (fun () -> a.Value <- 7; Some 7)
        change (fun () -> b.Value <- 123; None)
        change (fun () -> f.Value <- true; Some 123)
        sub.Dispose()
        change (fun () -> b.Value <- 321; None))

    test "[CSet] no transaction add" (fun () ->
        let set = cset (HashSet.ofList [1; 2; 3; 4])
        set.Add(5) |> ignore
        set.Remove(1) |> ignore
        set |> ASet.force |> ignore
        set.Add(10) |> ignore)

    test "[CSet] no transaction remove" (fun () ->
        let set = cset (HashSet.ofList [1; 2; 3; 4])
        set.Remove(1) |> ignore
        set.Add(5) |> ignore
        set |> ASet.force |> ignore
        set.Remove(2) |> ignore)

    test "[CList] no transaction append" (fun () ->
        let list = clist (IndexList.ofList [1; 2; 3; 4])
        list.Append(5) |> ignore
        list.RemoveAt(0) |> ignore
        list |> AList.force |> ignore
        list.Append(10) |> ignore)

    test "[CList] no transaction remove" (fun () ->
        let list = clist (IndexList.ofList [1; 2; 3; 4])
        list.RemoveAt(0) |> ignore
        list.Append(5) |> ignore
        list |> AList.force |> ignore
        list.RemoveAt(0) |> ignore)

    test "[CVal] no transaction change" (fun () ->
        let v = cval 5
        v.Value <- 1
        v |> AVal.force |> ignore)

    printfn "PASSED %d FAILED %d" passedCount failedCount
