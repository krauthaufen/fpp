module Fpp.Bootstrap.FixCorpus

// The corpus for the stage-0/stage-1 fixpoint: a SELF-CONTAINED program,
// small enough that stage-1 can compile it inside wasm, wide enough that the
// compared .wat exercises the parts of emission most likely to drift —
// generics and stamping, a class with inheritance, a DU and a record, string
// and list work, a struct tuple, and a downcast.
//
// A driver like lexdrive.fpp is NOT usable here: it is a fragment that only
// compiles beside the compiler's own sources, so it would drag Parser.fs into
// every fixpoint run. Bigger corpora stay opt-in, as an argument.

open Fpp.Prelude

type Shape =
    | Dot
    | Line of int
    | Box of int * int

type Named = { Name : string; Size : int }

[<AllowNullLiteral>]
type Node(tag : int) =
    let mutable tag = tag
    member x.Tag
        with get () = tag
        and set v = tag <- v
    member x.Describe = "node " + string tag

[<AllowNullLiteral>]
type Leaf(tag : int, label : string) =
    inherit Node(tag)
    member x.Label = label

let area (s : Shape) : int =
    match s with
    | Dot -> 0
    | Line n -> n
    | Box (w, h) -> w * h

let rec sumList (xs : int list) : int =
    match xs with
    | [] -> 0
    | x :: rest -> x + sumList rest

let pairUp (a : 'a) (b : 'b) : struct ('a * 'b) = struct (a, b)

let describe (n : Node) : string =
    if isNull n then "none"
    else
        let l : Leaf = downcast n
        l.Label + "/" + n.Describe

let shapes = [ Dot; Line 4; Box (3, 5) ]

let named = { Name = "corpus"; Size = List.length shapes }

let p1 = print (string (List.sum (List.map area shapes)))
let p2 = print (string (sumList [ 1 .. 10 ]))
let p3 = print (named.Name + " " + string named.Size)
let p4 = print (describe (Leaf (7, "leaf")))
let p5 = print (String.concat "," (List.map (fun (s : Shape) -> string (area s)) shapes))

let sp = pairUp 2 "two"

let p6 =
    match sp with
    | struct (n, s) -> print (string n + s)

let p7 = print (String.concat "|" [ for s in shapes -> string (area s) ])
