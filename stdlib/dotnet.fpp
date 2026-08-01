module Stdlib

// The .NET surface: ResizeArray, Dictionary, HashSet, StringBuilder, Math
// and the numeric statics, exercised through the SAME source under F# and
// F++. Every value printed here has to come out byte-identical, which is
// what pins the semantics — insertion order, what Add refuses, which way
// Round breaks a tie, what Length counts.
//
// Two things are deliberately not here, because F++ does not have them:
// TryGetValue and every other byref out-parameter, and a mutable HashSet
// under that name — ours is `MutableHashSet`, because `HashSet` belongs to
// the prelude's immutable one. Both are in DIVERGENCES.md.

open System
open System.Collections.Generic
open System.Text

// ---- ResizeArray --------------------------------------------------------

let ra = ResizeArray<int>()
let r0 =
    ra.Add 10
    ra.Add 30
    ra.Insert (1, 20)
    print ra.Count
let r1 = print ra.[0]
let r2 = print ra.[1]
let r3 = print ra.[2]
let r4 =
    ra.[0] <- 11
    print ra.[0]
let r5 = print (if ra.Contains 20 then 1 else 0)
let r6 = print (ra.IndexOf 30)
let r7 = print (ra.IndexOf 99)
let r8 =
    let mutable total = 0
    for v in ra do
        total <- total + v
    print total
let r9 =
    ra.RemoveAt 0
    print ra.Count
let r10 = print (if ra.Remove 30 then 1 else 0)
let r11 = print (if ra.Remove 30 then 1 else 0)
let r12 = print ra.Count
let r13 =
    ra.Add 40
    ra.Add 50
    ra.Reverse ()
    print ra.[0]
let r14 = print (Array.length (ra.ToArray ()))
let r15 =
    ra.Clear ()
    print ra.Count

let names = ResizeArray<string>()
let r16 =
    names.AddRange [ "beta"; "alpha" ]
    names.Add "gamma"
    print names.Count
let r17 = print names.[1]
let r18 = print (String.concat "," (List.ofArray (names.ToArray ())))

// growth past the initial capacity, which is where a resize bug lives
let big = ResizeArray<int>()
let r19 =
    for i in 1 .. 100 do
        big.Add (i * i)
    print big.Count
let r20 = print big.[99]
let r21 =
    let mutable s = 0
    for v in big do
        s <- s + v
    print s

// the collections ARE seqs: the whole Seq module applies to them
let q0 = print (Seq.sum (big :> seq<int>))
let q1 = print (Seq.length (names :> seq<string>))
let q2 = print (String.concat "," (List.ofSeq (names :> seq<string>)))
let q3 = print (Seq.sum (Seq.map (fun (x : int) -> x * 2) (big :> seq<int>)))
let q4 = print (Seq.length (Seq.filter (fun (x : int) -> x % 2 = 0) (big :> seq<int>)))

// ---- Dictionary ---------------------------------------------------------

let d = Dictionary<string, int>()
let d0 =
    d.["one"] <- 1
    d.["two"] <- 2
    d.Add ("three", 3)
    print d.Count
let d1 = print d.["two"]
let d2 =
    d.["two"] <- 22
    print d.["two"]
let d3 = print d.Count
let d4 = print (if d.ContainsKey "one" then 1 else 0)
let d5 = print (if d.ContainsKey "four" then 1 else 0)
let d6 = print (if d.ContainsValue 3 then 1 else 0)
// sorted, because only the CONTENTS are guaranteed to agree
let d7 = print (String.concat "," (List.sort (List.ofSeq d.Keys)))
let d8 = print (List.sum (List.ofSeq d.Values))
let d9 = print (if d.Remove "one" then 1 else 0)
let d10 = print (if d.Remove "one" then 1 else 0)
let d11 = print d.Count
let d12 = print (String.concat "," (List.sort (List.ofSeq d.Keys)))
let d13 =
    d.Clear ()
    print d.Count

// int keys: the packed-array path, and enough of them to force a rehash
let counts = Dictionary<int, int>()
let d14 =
    for i in 1 .. 50 do
        counts.[i] <- i * 3
    print counts.Count
let d15 = print counts.[50]
let d16 = print (List.sum (List.ofSeq counts.Values))
let d17 =
    let mutable removed = 0
    for i in 1 .. 25 do
        if counts.Remove i then removed <- removed + 1
    print removed
let d18 = print counts.Count
let d19 = print counts.[26]

// ---- MutableHashSet -----------------------------------------------------
//
// .NET's HashSet, under a name that is free here. The F# run gets the
// alias from the oracle harness' preamble, so this is one source again.

let hs = MutableHashSet<string>()
let h0 = print (if hs.Add "x" then 1 else 0)
let h1 = print (if hs.Add "x" then 1 else 0)
let h2 = print hs.Count
let h3 =
    hs.UnionWith [ "y"; "z"; "x" ]
    print hs.Count
let h4 = print (if hs.Contains "y" then 1 else 0)
let h5 = print (if hs.Remove "y" then 1 else 0)
let h6 = print (if hs.Remove "y" then 1 else 0)
let h7 = print (String.concat "," (List.sort (List.ofSeq (hs :> seq<string>))))
let h8 =
    hs.ExceptWith [ "x" ]
    print hs.Count
let h9 = print (if hs.IsSubsetOf [ "z"; "q" ] then 1 else 0)
let h10 = print (if hs.Overlaps [ "z"; "q" ] then 1 else 0)

let seen = MutableHashSet<int>()
let h11 =
    for i in 1 .. 200 do
        seen.Add (i % 37) |> ignore
    print seen.Count
let h12 = print (Seq.sum (seen :> seq<int>))

// ---- StringBuilder ------------------------------------------------------

let sb = StringBuilder()
let s0 =
    sb.Append "hello" |> ignore
    sb.Append " " |> ignore
    sb.Append "world" |> ignore
    print sb.Length
let s1 = print (sb.ToString ())
let s2 =
    sb.AppendLine "!" |> ignore
    print sb.Length
let s3 =
    sb.Clear () |> ignore
    print sb.Length
let s4 =
    for i in 1 .. 5 do
        sb.Append (string i) |> ignore
    print (sb.ToString ())
// the char overload, which character-at-a-time code lives on
let s5 =
    sb.Clear () |> ignore
    sb.Append 'a' |> ignore
    sb.Append 'b' |> ignore
    print (sb.ToString ())

// ---- System.Math --------------------------------------------------------

// bound through a typed let, not printed inline: `print` picks its
// conversion from the argument's kind, and a class-polymorphic argument
// does not have one until the binding fixes it
let mAbsI : int = Math.Abs -3
let m0 = print mAbsI
let mAbsF : float = Math.Abs -2.5
let m1 = print mAbsF
let m2 = print (Math.Sign -7)
let m3 = print (Math.Sign 0)
let mMaxI : int = Math.Max (3, 7)
let m4 = print mMaxI
let mMinF : float = Math.Min (1.5, 0.5)
let m5 = print mMinF
let m6 = print (Math.Sqrt 9.0)
let m7 = print (Math.Pow (2.0, 10.0))
let m8 = print (Math.Floor -1.5)
let m9 = print (Math.Ceiling -1.5)
// HALF-TO-EVEN, both of them
let m10 = print (Math.Round 2.5)
let m11 = print (Math.Round 3.5)
let m12 = print (Math.Truncate -1.7)
let m13 = print (Math.Exp 0.0)
let m14 = print (Math.Log 1.0)
let m15 = print (Math.Log10 100.0)
let m16 = print (Math.Atan2 (0.0, 1.0))
let m17 = print (sign -3)
let m18 = print (sign 4L)

// ---- the numeric statics ------------------------------------------------

let n0 = print Int32.MaxValue
let n1 = print Int32.MinValue
let n2 = print Int64.MaxValue
let n3 = print Int64.MinValue
let n4 = print (Int32.Parse "42")
let n5 = print (Int32.Parse "-17")
let n6 = print (Int32.Parse "  +5  ")
let n7 = print (Int64.Parse "9007199254740993")
let n8 = print (if Boolean.Parse "True" then 1 else 0)
let n9 = print (if Boolean.Parse "false" then 1 else 0)
let n10 = print (if Double.IsNaN (0.0 / 0.0) then 1 else 0)
let n11 = print (if Double.IsInfinity (1.0 / 0.0) then 1 else 0)
let n12 = print (if Single.IsNaN (0.0f / 0.0f) then 1 else 0)

// ---- the F# collection functions that were missing ----------------------

let c0 = print (List.compareWith compare [ 1; 2 ] [ 1; 2; 3 ])
let c1 = print (List.compareWith compare [ 2; 1 ] [ 1; 9 ])
let c2 = print (List.compareWith compare [ 1; 2 ] [ 1; 2 ])
let c3 = print (Array.compareWith compare [| 2; 1 |] [| 1; 9 |])
let c4 = print (Seq.compareWith compare (List.toSeq [ 1; 2 ]) (List.toSeq [ 1; 2; 3 ]))
let c5 = print (List.sum (Seq.toList (Seq.truncate 4 (Seq.initInfinite (fun i -> i * i)))))
let c6 = print (List.sum (Seq.toList (Seq.tail (List.toSeq [ 1; 2; 3; 4 ]))))
let c7 = print (Seq.findBack (fun x -> x < 3) (List.toSeq [ 1; 2; 3; 4 ]))
let c8 = print (Seq.findIndexBack (fun x -> x < 3) (List.toSeq [ 1; 2; 3; 4 ]))
let c9 = print (List.sum (Seq.toList (Seq.updateAt 1 99 (List.toSeq [ 1; 2; 3 ]))))
let c10 = print (List.sum (Seq.toList (Seq.insertAt 0 7 (List.toSeq [ 1; 2; 3 ]))))
let c11 = print (List.sum (Seq.toList (Seq.removeAt 1 (List.toSeq [ 1; 2; 3 ]))))
let c12 = print (Seq.reduceBack (fun a b -> a - b) (List.toSeq [ 1; 2; 3 ]))
