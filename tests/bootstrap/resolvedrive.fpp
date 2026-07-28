module Fpp.Bootstrap.ResolveDrive

// Driver for the stage-0 harness: runs the NAME RESOLVER the compiler emitted
// from its own source over a small program, and prints what it bound and what
// it resolved. The hosted compiler runs the same program; the two must agree.
//
// The source deliberately includes the shapes this stage fixed: an `and`
// group whose members reference each other forwards and backwards, a shadowed
// name, and a one-line `let ... in`.

open Fpp.Prelude
open Fpp.Syntax
open Fpp.Analysis

let src = "module T\n\nlet shadow = 1\n\nlet rec ping (n : int) : int =\n    if n = 0 then shadow else pong (n - 1)\n\nand pong (n : int) : int =\n    let shadow = 2\n    (let m = n - 1 in ping m + shadow)\n\nlet use = ping 3\n"

let r = Parser.parse src
let imports = dictNew<string, Resolve.Definition> ()
let b = Resolve.resolve "t.fpp" imports r.Root

let defText (d : Resolve.Definition) : string =
    d.Name + ":" + Resolve.kindLabel d.Kind + "@" + string d.Offset

let useText (u : Resolve.Resolution) : string =
    string u.UseOffset + "->" + u.Def.Name + "@" + string u.Def.Offset

let p1 = print ("diagnostics " + string (List.length r.Diagnostics))
let p2 = print ("definitions " + string (List.length b.Definitions))
let p3 = print (String.concat " " (List.map defText b.Definitions))
let p4 = print ("resolutions " + string (List.length b.Resolutions))
let p5 = print (String.concat " " (List.map useText b.Resolutions))
