module Fpp.Bootstrap.ParseDrive

// Driver for the stage-0 harness: parses a source string with the parser the
// compiler emitted from its OWN source, and prints a shape fingerprint of the
// tree. The hosted compiler runs the same program; the two must agree.
//
// The fingerprint is parentheses for nodes and `.` for tokens rather than
// node-kind names — it pins the tree's shape without a hundred-case name
// table, and any misparse moves it.

open Fpp.Prelude
open Fpp.Syntax

let src = "module M\n\nopen A.B\n\ntype T<'a> =\n    | One of int\n    | Two of 'a * string\n\ntype R = { X : int; mutable Y : float }\n\nlet rec fact (n : int) : int =\n    if n <= 1 then 1\n    else n * fact (n - 1)\n\nlet f xs =\n    let mutable acc = 0\n    for x in xs do\n        acc <- acc + x\n    match acc with\n    | 0 -> None\n    | v when v > 10 -> Some (v, \"big\")\n    | _ -> Some (acc, \"small\")\n\nlet g = fun a b -> a :: b @ [ 1; 2 ]\n"

let rec shape (g : Green) : string =
    match g with
    | GToken _ -> "."
    | GNode n -> "(" + String.concat "" (List.map shape n.Children) + ")"

let r = Parser.parse src
let p1 = print ("diagnostics " + string (List.length r.Diagnostics))
let p2 =
    print (String.concat "; " (List.map (fun (d : Diagnostic) -> string d.Offset + ":" + d.Message) r.Diagnostics))
let p3 = print (if Green.toText (GNode r.Root) = src then "roundtrip ok" else "ROUNDTRIP BROKEN")
let p4 = print ("width " + string r.Root.Width + " of " + string (strLen src))
let p5 = print ("tokens " + string (List.length (Green.tokens (GNode r.Root))))
let p6 = print ("lets " + string (List.length (Green.collectNodes LetDecl (GNode r.Root))))
let p7 = print ("types " + string (List.length (Green.collectNodes TypeDecl (GNode r.Root))))
let p8 = print ("cases " + string (List.length (Green.collectNodes MatchClause (GNode r.Root))))
let p9 = print ("errors " + string (List.length (Green.collectNodes ErrorNode (GNode r.Root))))
let p10 = print (shape (GNode r.Root))

// error tolerance: broken input must still round-trip
let bad = "let f x =\n  match x with\n  | -> )\ntype = {\n"
let rb = Parser.parse bad
let p11 = print (if Green.toText (GNode rb.Root) = bad then "bad roundtrip ok" else "BAD ROUNDTRIP BROKEN")
let p12 = print ("bad diagnostics " + string (List.length rb.Diagnostics))
let p13 = print (shape (GNode rb.Root))
