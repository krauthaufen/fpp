module Fpp.Tests.QueryTests

open Expecto
open Fpp.Query

[<Tests>]
let queryTests =
    testList "query engine" [
        test "memoizes derived queries" {
            let db = Db()
            db.SetInput "in" "x" (box 4)
            let mutable runs = 0
            let q () =
                db.MemoT "half" "x" (fun () ->
                    runs <- runs + 1
                    unbox<int> (db.GetInput "in" "x") / 2)
            Expect.equal (q ()) 2 "computes"
            Expect.equal (q ()) 2 "returns cached"
            Expect.equal runs 1 "computed exactly once"
        }
        test "recomputes when an input changes" {
            let db = Db()
            db.SetInput "in" "x" (box 4)
            let mutable runs = 0
            let q () =
                db.MemoT "half" "x" (fun () ->
                    runs <- runs + 1
                    unbox<int> (db.GetInput "in" "x") / 2)
            Expect.equal (q ()) 2 "initial"
            db.SetInput "in" "x" (box 10)
            Expect.equal (q ()) 5 "updated"
            Expect.equal runs 2 "recomputed once"
        }
        test "setting an equal input value invalidates nothing" {
            let db = Db()
            db.SetInput "in" "x" (box 4)
            let rev = db.Revision
            db.SetInput "in" "x" (box 4)
            Expect.equal db.Revision rev "revision unchanged for identical value"
        }
        test "early cutoff stops downstream recomputation" {
            let db = Db()
            db.SetInput "in" "x" (box 4)
            let mutable innerRuns = 0
            let mutable outerRuns = 0
            let inner () =
                db.MemoT "half" "x" (fun () ->
                    innerRuns <- innerRuns + 1
                    unbox<int> (db.GetInput "in" "x") / 2)
            let outer () =
                db.MemoT "tenfold" "x" (fun () ->
                    outerRuns <- outerRuns + 1
                    inner () * 10)
            Expect.equal (outer ()) 20 "initial"
            // 4 -> 5: half is 2 both times, so `tenfold` must not rerun
            db.SetInput "in" "x" (box 5)
            Expect.equal (outer ()) 20 "same result"
            Expect.equal innerRuns 2 "inner reran"
            Expect.equal outerRuns 1 "outer was cut off"
        }
        test "dependencies are tracked per revision" {
            let db = Db()
            db.SetInput "in" "a" (box 1)
            db.SetInput "in" "b" (box 2)
            let mutable runs = 0
            let q () =
                db.MemoT "pick" "k" (fun () ->
                    runs <- runs + 1
                    let a = unbox<int> (db.GetInput "in" "a")
                    if a > 0 then a else unbox<int> (db.GetInput "in" "b"))
            Expect.equal (q ()) 1 "reads only a"
            db.SetInput "in" "b" (box 99)
            Expect.equal (q ()) 1 "b is not a dependency"
            Expect.equal runs 1 "no recomputation on irrelevant change"
        }
    ]
