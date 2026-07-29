module Fpp.Tests.BinBattery

open Expecto

// End-to-end battery for the direct binary backend: each case is a small F++
// program compiled through Workspace.EmitProgramWasm (pure bytes, no wat),
// executed under wasmtime, and pinned to its exact stdout. Every program
// class the binary driver claims to support must have a case here — this is
// the regression gate the porting loop runs against.

let private wasmtime =
    let home = System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    home + "/.wasmtime/bin/wasmtime"

let private runProgram (lines : string list) : string =
    let src = String.concat "\n" lines + "\n"
    let ws = Fpp.Workspace ()
    ws.SetFileText "p.fpp" src
    let bytes, errs = ws.EmitProgramWasm ()
    Expect.isEmpty errs "compile errors"
    let path = System.IO.Path.GetTempFileName () + ".wasm"
    System.IO.File.WriteAllBytes (path, bytes)
    let psi = System.Diagnostics.ProcessStartInfo (wasmtime, "run -W gc=y,exceptions=y " + path)
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    use p = System.Diagnostics.Process.Start psi
    let out = p.StandardOutput.ReadToEnd ()
    let err = p.StandardError.ReadToEnd ()
    p.WaitForExit ()
    System.IO.File.Delete path
    Expect.equal p.ExitCode 0 (sprintf "wasmtime failed: %s" err)
    out

let private expects (name : string) (src : string list) (stdout : string) =
    test name { Expect.equal (runProgram src) stdout "program stdout" }

[<Tests>]
let binBattery =
    testList "binary battery" [
        expects "recursion: factorial"
            [ "let rec fact (n : int) : int ="
              "    if n <= 1 then 1 else n * fact (n - 1)"
              "let go = print (fact 10)" ]
            "3628800\n"

        expects "DU construction and match"
            [ "type Shape ="
              "    | Dot"
              "    | Box of int"
              "let size (s : Shape) : int ="
              "    match s with"
              "    | Dot -> 0"
              "    | Box n -> n"
              "let go ="
              "    print (size Dot)"
              "    print (size (Box 7))" ]
            "0\n7\n"

        expects "list literal and cons recursion"
            [ "let rec total (xs : int list) : int ="
              "    match xs with"
              "    | [] -> 0"
              "    | h :: t -> h + total t"
              "let go = print (total [1; 2; 3; 4])" ]
            "10\n"

        expects "tuple construction and pattern"
            [ "let swap (p : int * int) : int * int ="
              "    match p with"
              "    | (a, b) -> (b, a)"
              "let go ="
              "    match swap (3, 9) with"
              "    | (x, y) -> print (x * 100 + y)" ]
            "903\n"

        expects "record with mutable field"
            [ "type P = { X : int; mutable Y : int }"
              "let go ="
              "    let p = { X = 3; Y = 4 }"
              "    p.Y <- p.Y + 10"
              "    print (p.X * 100 + p.Y)" ]
            "314\n"

        expects "closures capture locals, prelude higher-order"
            [ "let go ="
              "    let k = 10"
              "    let addk = fun x -> x + k"
              "    print (addk 5)"
              "    let xs = List.map (fun x -> x * x) [1; 2; 3]"
              "    print (List.sum xs)" ]
            "15\n14\n"

        expects "captured mutable lives in a cell"
            [ "let counter () ="
              "    let mutable n = 0"
              "    let bump = fun () -> n <- n + 1"
              "    bump ()"
              "    bump ()"
              "    bump ()"
              "    n"
              "let go = print (counter ())" ]
            "3\n"

        expects "local let rec ties its own knot"
            [ "let go ="
              "    let base_ = 100"
              "    let rec walk (n : int) : int ="
              "        if n <= 0 then base_ else 1 + walk (n - 1)"
              "    print (walk 5)" ]
            "105\n"

        expects "mutually recursive local functions"
            [ "let go ="
              "    let rec even (n : int) : bool ="
              "        if n = 0 then true else odd (n - 1)"
              "    and odd (n : int) : bool ="
              "        if n = 0 then false else even (n - 1)"
              "    if even 10 then print 1 else print 0"
              "    if odd 7 then print 1 else print 0" ]
            "1\n1\n"

        expects "partial application of a top-level function"
            [ "let add3 (a : int) (b : int) (c : int) : int = a + b + c"
              "let go ="
              "    let f = add3 100"
              "    let g = f 20"
              "    print (g 3)"
              "    print (g 4)" ]
            "123\n124\n"

        expects "top-level function passed first-class"
            [ "let double (x : int) : int = x * 2"
              "let go = print (List.sum (List.map double [1; 2; 3]))" ]
            "12\n"

        expects "string concat, ordering, Length, indexing"
            [ "let go ="
              "    let s = \"hello\" + \" \" + \"world\""
              "    print s"
              "    print s.Length"
              "    if \"abc\" < \"abd\" then print 1 else print 0"
              "    print s.[4]" ]
            "hello world\n11\n1\no\n"

        expects "float arithmetic and printing"
            [ "let go ="
              "    let x = 1.5 + 2.25"
              "    print x"
              "    print (x * 2.0)"
              "    if 1.5 < 2.5 then print 1 else print 0" ]
            "3.75\n7.5\n1\n"

        expects "conversions: int-of-string, string-of-int, float, truncation"
            [ "let go ="
              "    print (int \"42\")"
              "    print (string 7)"
              "    print (float 3)"
              "    print (int 9.7)"
              "    print (int64 5)" ]
            "42\n7\n3\n9\n5\n"

        expects "compare, max, min"
            [ "let go ="
              "    print (compare \"ab\" \"ac\")"
              "    print (compare 7 3)"
              "    print (max 3 9)"
              "    print (min 2.5 1.5)" ]
            "-1\n1\n9\n1.5\n"

        expects "string builtins: Substring, IndexOf"
            [ "let go ="
              "    let s = \"hello world\""
              "    print (s.Substring (6, 5))"
              "    print (s.IndexOf 'w')"
              "    print (s.Substring 6)" ]
            "world\n6\nworld\n"

        expects "sprintf compile-time expansion"
            [ "let go ="
              "    print (sprintf \"%d-%s\" 5 \"x\")" ]
            "5-x\n"

        expects "arrays: zeroCreate, index get/set, Length"
            [ "let go ="
              "    let a = Array.zeroCreate 3"
              "    a.[0] <- 10"
              "    a.[2] <- 32"
              "    print (a.[0] + a.[1] + a.[2])"
              "    print a.Length" ]
            "42\n3\n"
    ]
