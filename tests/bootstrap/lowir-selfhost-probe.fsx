// Emit the WHOLE compiler (its own sources + the binary driver) through the
// LowIR/GC backend and histogram the errors — the gap list for self-host.
#r "../../src/Fpp.Compiler/bin/Release/net10.0/Fpp.Compiler.dll"
open Fpp
let root = System.IO.Path.GetFullPath (__SOURCE_DIRECTORY__ + "/../..")
let readSource (path : string) =
    System.Text.Encoding.Latin1.GetString (System.IO.File.ReadAllBytes path)
let compilerFiles =
    let proj = root + "/src/Fpp.Compiler/Fpp.Compiler.fsproj"
    System.IO.File.ReadAllLines proj
    |> Array.choose (fun line ->
        let m = System.Text.RegularExpressions.Regex.Match(line, "Compile Include=\"(.+?)\"")
        if m.Success then Some (root + "/src/Fpp.Compiler/" + m.Groups.[1].Value.Replace('\\','/')) else None)
    |> Array.toList
    |> List.map (fun f -> if f.EndsWith "/Prelude.fs" then root + "/stdlib/bootstrap.fpp" else f)
let driver = root + "/tests/bootstrap/compiledrive-bin.fpp"
let files = compilerFiles @ [ driver ]
let ws = Workspace()
for f in files do ws.SetFileText (System.IO.Path.GetFileName f) (readSource f)
let bytes, errors = ws.EmitProgramWasmLinearWith true
printfn "=== %d bytes, %d errors ===" (Array.length bytes) (List.length errors)
errors
|> List.map (fun (e : string) -> System.Text.RegularExpressions.Regex.Replace(e, "[0-9]+", "N"))
|> List.countBy id
|> List.sortByDescending snd
|> List.truncate 40
|> List.iter (fun (e, n) -> printfn "%5d  %s" n e)
