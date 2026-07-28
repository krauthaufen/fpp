module Fpp.Bootstrap.RefDrive

// Driver for the stage-0 harness: exercises the reference-identity half of
// the seam. The .NET half runs the SAME program in BootstrapTests, so any
// disagreement between HashSet-over-ReferenceEquals and the open-addressed
// table over refEq shows up as a diff.

open Fpp.Prelude

// two structurally EQUAL but distinct objects must be different keys
type Node = { Tag : int; mutable Kid : Node option }

let shallow (n : Node) : int = n.Tag

let a : Node = { Tag = 1; Kid = None }
let b : Node = { Tag = 1; Kid = None }
let s = refSetNew<Node> shallow

let r1 = print (string (refSetAdd s a))
let r2 = print (string (refSetAdd s a))
let r3 = print (string (refSetAdd s b))
let r4 = print (string (refSetContains s a) + " " + string (refSetContains s b))
let c : Node = { Tag = 1; Kid = None }
let r5 = print (string (refSetContains s c))

// the hash must survive mutation of a NON-hashed field
let mut = a.Kid <- Some b
let r6 = print (string (refSetContains s a))

// many entries: forces rehash, all identities kept apart despite one bucket
let many =
    let mutable i = 0
    let mutable kept = 0
    while i < 40 do
        let n : Node = { Tag = 7; Kid = None }
        if refSetAdd s n then kept <- kept + 1
        i <- i + 1
    print ("added " + string kept)

let m = refMapNew<Node, string> shallow
let m1 = refMapSet m a "first"
let m2 = refMapSet m b "second"
let m3 = refMapSet m a "updated"
let m4 =
    match refMapTryFind m a with
    | Some v -> print v
    | None -> print "MISSING"
let m5 =
    match refMapTryFind m b with
    | Some v -> print v
    | None -> print "MISSING"
let m6 =
    match refMapTryFind m c with
    | Some v -> print ("BAD " + v)
    | None -> print "absent"

let ps = refPairSetNew<Node> shallow
let q1 = print (string (refPairSetAdd ps a b))
let q2 = print (string (refPairSetAdd ps a b))
let q3 = print (string (refPairSetAdd ps b a))
let q4 = print (string (refPairSetAdd ps a c))
