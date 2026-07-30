module Fpp.Tests.SourceMapTests

open Expecto
open Fpp

/// decode a base64-VLQ run back to its integers
let private decodeVlq (s : string) : int list =
    let b64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
    let out = ResizeArray<int> ()
    let mutable v = 0
    let mutable shift = 0
    for ch in s do
        let d = b64.IndexOf ch
        v <- v ||| ((d &&& 31) <<< shift)
        if d &&& 32 <> 0 then shift <- shift + 5
        else
            out.Add (if v &&& 1 = 1 then -(v >>> 1) else v >>> 1)
            v <- 0
            shift <- 0
    List.ofSeq out

/// the map's segments as (byteOffset, sourceIndex, line, column), absolute
let private segments (map : string) : (int * int * int * int) list =
    let i = map.IndexOf "\"mappings\":\""
    let raw = map.Substring (i + 12, map.LastIndexOf '"' - i - 12)
    let mutable g = 0
    let mutable s = 0
    let mutable l = 0
    let mutable c = 0
    [ for seg in raw.Split ',' do
        match decodeVlq seg with
        | [ dg; ds; dl; dc ] ->
            g <- g + dg
            s <- s + ds
            l <- l + dl
            c <- c + dc
            yield g, s, l, c
        | _ -> () ]

[<Tests>]
let sourceMapTests =
    testList "source maps" [
        test "VLQ round-trips the values a mapping is made of" {
            for v in [ 0; 1; -1; 15; 16; -16; 1000; -1000; 123456 ] do
                Expect.equal (decodeVlq (Fpp.Backend.SourceMap.vlq v)) [ v ] ("VLQ of " + string v)
        }

        test "a byte offset maps to the .fpp file, line and column it came from" {
            let src = "module M\nlet addOne (x : int) =\n    let y = x + 1\n    y\nlet go = print (addOne 41)\n"
            let ws = Workspace()
            ws.SetFileText "m.fpp" src
            let bytes, map, errs = ws.EmitProgramWasmWithSourceMap "m.wasm.map"
            Expect.isEmpty errs "compiles"
            // the module tells a debugger where its map is
            let text = System.Text.Encoding.Latin1.GetString bytes
            Expect.stringContains text "sourceMappingURL" "the custom section is there"
            Expect.stringContains text "m.wasm.map" "naming the map"
            // the user's file is a source, with its text embedded so a debugger
            // needs nothing from disk
            Expect.stringContains map "\"m.fpp\"" "the .fpp file is a source"
            Expect.stringContains map "let addOne" "and its text travels with the map"
            // every mapping points at a real position in the file it names
            let sources =
                let i = map.IndexOf "\"sources\":["
                let j = map.IndexOf ']' 
                map.Substring(i + 11, j - i - 11).Split ',' |> Array.map (fun s -> s.Trim '"')
            let mine = segments map |> List.filter (fun (_, s, _, _) -> sources.[s] = "m.fpp")
            Expect.isNonEmpty mine "the user's code is mapped"
            let lines = src.Split '\n'
            for _, _, l, c in mine do
                Expect.isLessThan l lines.Length "a mapped line exists in the file"
                Expect.isLessThanOrEqual c lines.[l].Length "and the column is inside that line"
            // addOne's own body maps to the line it is written on
            let onAddOne =
                mine |> List.filter (fun (_, _, l, _) -> lines.[l].Contains "addOne (x : int)")
            Expect.isNonEmpty onAddOne "the function's code maps to its declaration"
        }

        test "debug names ride with the map, and only with it" {
            let src = "module M\ntype Point = { X : int; Y : int }\nlet dist (p : Point) = p.X + p.Y\nlet go = print (dist { X = 3; Y = 4 })\n"
            let dbg = Workspace()
            dbg.SetFileText "m.fpp" src
            let withNames, _, _ = dbg.EmitProgramWasmWithSourceMap "m.wasm.map"
            let plainWs = Workspace()
            plainWs.SetFileText "m.fpp" src
            let plain, _ = plainWs.EmitProgramWasm ()
            let dbgText = System.Text.Encoding.Latin1.GetString withNames
            let plainText = System.Text.Encoding.Latin1.GetString plain
            // a heap snapshot reads field names; a scope view reads parameter names
            Expect.stringContains dbgText "__desc" "field names travel with a debug build"
            Expect.isTrue (dbgText.Length > plainText.Length) "and they cost bytes"
            Expect.isFalse (plainText.Contains "__desc") "a plain build ships none of it"
        }

        test "no map is emitted unless one is asked for" {
            let ws = Workspace()
            ws.SetFileText "m.fpp" "module M\nlet go = print 1\n"
            let plain, _ = ws.EmitProgramWasm ()
            let text = System.Text.Encoding.Latin1.GetString plain
            Expect.isFalse (text.Contains "sourceMappingURL") "the default module carries no debug section"
        }
    ]

let private wasmtime =
    System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    + "/.wasmtime/bin/wasmtime"

let private runBytes (bytes : byte[]) : int * string =
    let tmp = System.IO.Path.GetTempFileName () + ".wasm"
    System.IO.File.WriteAllBytes (tmp, bytes)
    let psi = System.Diagnostics.ProcessStartInfo (wasmtime, "run -W gc=y,exceptions=y " + tmp)
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    use p = System.Diagnostics.Process.Start psi
    let o = p.StandardOutput.ReadToEnd ()
    p.StandardError.ReadToEnd () |> ignore
    p.WaitForExit ()
    System.IO.File.Delete tmp
    p.ExitCode, o

[<Tests>]
let stackTests =
    testList "the shadow stack" [
        // wasm gives the guest no view of its own call stack, so a debug build
        // keeps one. A plain build keeps none, and the same program still runs.
        let program =
            String.concat "\n"
                [ "module M"
                  // bound, not returned directly: a call in TAIL position
                  // replaces its caller's frame, which would make the count
                  // read oddly here
                  "let inner (x : int) ="
                  "    let d = Stack.depth ()"
                  "    d"
                  "let middle (x : int) = inner x + 0"
                  "let outer (x : int) = middle x + 0"
                  "let tailOuter (x : int) = inner x"
                  "let go ="
                  "    print (Stack.depth ())"
                  "    print (outer 1)"
                  "    print (tailOuter 1)"
                  "    print (Stack.depth ())"
                  "" ]

        test "a debug build can see its own call depth" {
            let ws = Workspace()
            ws.SetFileText "m.fpp" program
            let bytes, _, errs = ws.EmitProgramWasmWithSourceMap "m.wasm.map"
            Expect.isEmpty errs "compiles"
            let code, out = runBytes bytes
            Expect.equal code 0 "runs"
            // 1 at the top; 4 through three non-tail calls; a TAIL call
            // replaces its caller's frame rather than adding one, so that
            // chain is shallower; back to 1 afterwards
            Expect.equal out "1\n4\n2\n1\n" "depth tracks the real call chain, tail calls included"
        }

        test "a plain build carries no shadow stack, and still runs" {
            let ws = Workspace()
            ws.SetFileText "m.fpp" program
            let bytes, errs = ws.EmitProgramWasm ()
            Expect.isEmpty errs "compiles"
            let code, out = runBytes bytes
            Expect.equal code 0 "runs"
            Expect.equal out "0\n0\n0\n0\n" "no frames to report, and nothing breaks for asking"
        }

        test "frames are ids the name section resolves" {
            let ws = Workspace()
            ws.SetFileText "m.fpp"
                (String.concat "\n"
                    [ "module M"
                      "let deep (x : int) ="
                      "    let fs = Stack.frames ()"
                      "    List.length fs"
                      "let go = print (deep 1 > 0)"
                      "" ])
            let bytes, _, errs = ws.EmitProgramWasmWithSourceMap "m.wasm.map"
            Expect.isEmpty errs "compiles"
            let code, out = runBytes bytes
            Expect.equal code 0 "runs"
            Expect.equal out "True\n" "a frame list comes back with something in it"
        }
    ]
