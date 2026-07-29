// The bootstrap frontier: how far can the dotnet-built compiler emit its own
// sources? Grows the prefix one file at a time; each step must lower with no
// notes, emit with no errors, and instantiate under wasmtime.
//
//   dotnet fsi tests/bootstrap/frontier.fsx            # all files
//   dotnet fsi tests/bootstrap/frontier.fsx 6          # first 6 only
//
// `Prelude.fs` is the seam and is replaced by its F++ implementation.
//
// Emission alone is a WEAK gate: dead-code elimination drops every function
// the program never calls, so a file whose exports nobody uses can pass while
// most of it was never emitted at all (watch the wat line count). The strong
// gate is a driver that runs the emitted code and agrees with the hosted
// compiler — see tests/bootstrap/*drive.fpp and BootstrapTests.fs.

#r "../../src/Fpp.Compiler/bin/Release/net10.0/Fpp.Compiler.dll"

open Fpp

let root = System.IO.Path.GetFullPath (__SOURCE_DIRECTORY__ + "/../..")

let compilerFiles =
    let proj = root + "/src/Fpp.Compiler/Fpp.Compiler.fsproj"
    System.IO.File.ReadAllLines proj
    |> Array.choose (fun line ->
        let m = System.Text.RegularExpressions.Regex.Match(line, "Compile Include=\"(.+?)\"")
        if m.Success then Some (root + "/src/Fpp.Compiler/" + m.Groups.[1].Value.Replace('\\', '/'))
        else None)
    |> Array.toList
    |> List.map (fun f ->
        if f.EndsWith "/Prelude.fs" then root + "/stdlib/bootstrap.fpp" else f)

let limit =
    match System.Environment.GetCommandLineArgs() |> Array.tryLast |> Option.bind (fun a -> match System.Int32.TryParse a with | true, n -> Some n | _ -> None) with
    | Some n -> n
    | None -> compilerFiles.Length

let wasmtime =
    System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    + "/.wasmtime/bin/wasmtime"

let short (f : string) = f.Substring (root.Length + 1)

let mutable frontier = 0
let mutable stop = false
for k in 1 .. min limit compilerFiles.Length do
    if not stop then
        let files = compilerFiles |> List.truncate k
        let ws = Workspace()
        for f in files do ws.SetFileText f (System.IO.File.ReadAllText f)
        let bytes, errors = ws.EmitProgramWasm ()
        if not (List.isEmpty errors) then
            stop <- true
            printfn "%2d %-42s %d ERRORS" k (short (List.last files)) errors.Length
            errors
            |> List.countBy (fun (e : string) ->
                let i = e.IndexOf ": "
                let m = if i >= 0 then e.Substring (i + 2) else e
                String.concat " " (m.Split ' ' |> Array.truncate 6))
            |> List.sortByDescending snd
            |> List.truncate 12
            |> List.iter (fun (m, c) -> printfn "       %3d  %s" c m)
            for e in errors |> List.truncate 10 do printfn "       %s" e
        else
            let tmp = System.IO.Path.GetTempFileName() + ".wasm"
            System.IO.File.WriteAllBytes(tmp, bytes)
            let psi = System.Diagnostics.ProcessStartInfo(wasmtime, "run -W gc=y,exceptions=y " + tmp)
            psi.RedirectStandardOutput <- true
            psi.RedirectStandardError <- true
            let p = System.Diagnostics.Process.Start psi
            let err = p.StandardError.ReadToEnd()
            p.StandardOutput.ReadToEnd() |> ignore
            p.WaitForExit()
            System.IO.File.Delete tmp
            if p.ExitCode <> 0 then
                stop <- true
                printfn "%2d %-42s WASMTIME %d" k (short (List.last files)) p.ExitCode
                printfn "%s" (err.Substring (0, min 1500 err.Length))
            else
                frontier <- k
                printfn "%2d %-42s ok (%d bytes)" k (short (List.last files)) bytes.Length

printfn "frontier: %d of %d files" frontier compilerFiles.Length
