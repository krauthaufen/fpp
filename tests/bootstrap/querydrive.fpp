module Fpp.Bootstrap.QueryDrive

// Driver for the stage-0 harness: drives the query engine the compiler
// emitted from its own source — inputs, memoized queries, dependency
// tracking, invalidation on edit, and early cutoff. The hosted compiler
// runs the same program in BootstrapTests.

open Fpp.Prelude
open Fpp.Query

let db = Db()

let a1 = db.SetInput "src" "a" (box "hello")
let a2 = db.SetInput "src" "b" (box "world")

let lengthOf (k : string) : int =
    db.MemoT<int> "len" k (fun () ->
        let s = unbox<string> (db.GetInput "src" k)
        s.Length)

let both (u : unit) : int =
    db.MemoT<int> "both" "" (fun () -> lengthOf "a" + lengthOf "b")

let r1 = print (string (both ()))
let r2 = print ("computes " + string db.ComputeCount)
// nothing changed: the memo answers without recomputing
let r3 = print (string (both ()))
let r4 = print ("computes " + string db.ComputeCount)
// an edit to one input invalidates that chain
let e1 = db.SetInput "src" "a" (box "hi")
let r5 = print (string (both ()))
let r6 = print ("computes " + string db.ComputeCount)
// setting the SAME value again must not change the answer
let e2 = db.SetInput "src" "b" (box "world")
let r7 = print (string (both ()))
