module Fpp.Project

open Fpp.Prelude

// A project file names the sources IN COMPILE ORDER. That order is
// semantic — exports flow forward, and a file only sees what came before it
// — so the format deliberately cannot glob. A directory listing would hide
// the one fact the file exists to state.
//
//   # comment
//   name demo
//   out  demo.wasm
//   lib  vendor/thing.fppir
//   src  util.fpp
//   src  main.fpp
//
// One directive per line, unknown directives are reported rather than
// ignored. No nesting, no conditionals, no variables: if a project needs
// those it needs a build script, not a richer manifest format.

type Project =
    { /// absolute path of the project file itself
      Path : string
      Name : string
      /// output wasm text file, relative to the project directory
      Out : string
      /// linked .fppir libraries, in order, as absolute paths
      Libs : string list
      /// sources in COMPILE ORDER, as absolute paths
      Sources : string list
      /// conditional-compilation symbols (`define WEBDEBUG`); the build
      /// target adds WASM or NATIVE by itself
      Defines : string list
      /// this project's own version (`version 1.2.3`) — what `fpp pack`
      /// stamps on the package; "" when unversioned
      Version : string
      /// package dependencies: name and range text (`package foo ^1.2`)
      Packages : (string * string) list
      /// package registries, URLs or directories, in lookup order
      Registries : string list }

type LoadResult =
    { Loaded : Project
      /// (line number, message), 1-based
      Errors : (int * string) list }

let extension = ".fppproj"

let private combine (dir : string) (rel : string) : string =
    if rel = "" then dir
    else hostCanonicalize (pathCombine dir rel)

/// Parse a project file's TEXT. Kept separate from reading it so the LSP can
/// parse an unsaved buffer.
let parse (projectPath : string) (text : string) : LoadResult =
    let dir =
        let d = pathDirectory projectPath
        if d = "" then "." else d
    let errors = vecNew<int * string> ()
    let libs = vecNew<string> ()
    let sources = vecNew<string> ()
    let mutable name = pathFileNameWithoutExtension projectPath
    let mutable out = ""
    let defines = vecNew<string> ()
    let mutable version = ""
    let packages = vecNew<string * string> ()
    let registries = vecNew<string> ()
    let lines = text.Replace("\r\n", "\n").Split '\n'
    for i in 0 .. lines.Length - 1 do
        let line = lines.[i].Trim()
        if line <> "" && not (line.StartsWith "#") then
            let spSpace = line.IndexOf ' '
            let spTab = line.IndexOf '\t'
            let sp =
                if spSpace < 0 then spTab
                elif spTab < 0 then spSpace
                elif spSpace < spTab then spSpace
                else spTab
            let directive = if sp < 0 then line else line.Substring (0, sp)
            let arg = if sp < 0 then "" else line.Substring(sp + 1).Trim()
            match directive with
            | "name" -> name <- arg
            | "out" -> out <- arg
            | "lib" -> vecAdd libs (combine dir arg)
            | "src" -> vecAdd sources (combine dir arg)
            | "define" -> vecAdd defines arg
            | "version" ->
                (match Fpp.Pkg.parseVersion arg with
                 | Some _ -> version <- arg
                 | None -> vecAdd errors (i + 1, "bad version: " + arg))
            | "package" ->
                // `package foo ^1.2` — the range defaults to * when only
                // the name is written
                let psp = arg.IndexOf ' '
                let pn = if psp < 0 then arg else arg.Substring (0, psp)
                let pr = if psp < 0 then "*" else arg.Substring(psp + 1).Trim()
                (match Fpp.Pkg.parseRange pr with
                 | Some _ -> vecAdd packages (pn, pr)
                 | None -> vecAdd errors (i + 1, "bad range on package " + pn + ": " + pr))
            | "registry" -> vecAdd registries arg
            | other -> vecAdd errors (i + 1, "unknown directive '" + other + "'")
            if arg = "" && directive <> "name" then
                vecAdd errors (i + 1, directive + " needs an argument")
    if vecLen sources = 0 then vecAdd errors (1, "project names no sources")
    { Loaded =
        { Path = hostCanonicalize projectPath
          Name = name
          Out = (if out = "" then name + ".wasm" else out)
          Libs = vecToList libs
          Sources = vecToList sources
          Defines = vecToList defines
          Version = version
          Packages = vecToList packages
          Registries = vecToList registries }
      Errors = vecToList errors }

/// A project that is not there is not an exception: the caller reports the
/// miss with the diagnostics it already owns.
let read (projectPath : string) : LoadResult =
    match hostReadText projectPath with
    | Some text -> parse projectPath text
    | None ->
        { Loaded = { Path = projectPath; Name = ""; Out = ""; Libs = []; Sources = []; Defines = []
                     Version = ""; Packages = []; Registries = [] }
          Errors = [ 0, "cannot read project file " + projectPath ] }

/// The project a source file belongs to: the nearest `*.fppproj` at or above
/// its directory. An editor opens a FILE, not a project, so this is how a
/// buffer finds its compile order.
let rec findFor (startDir : string) : string option =
    if startDir = "" || not (hostExists startDir) then None
    else
        match hostListDir startDir
              |> Array.filter (fun f -> f.EndsWith extension)
              |> Array.sort
              |> Array.tryHead with
        | Some p -> Some p
        | None ->
            let parent = pathDirectory startDir
            if parent = "" || parent = startDir then None
            else findFor parent

// ---- conditional compilation ----------------------------------------------
// `#if SYMBOL` / `#else` / `#endif`, nesting allowed, `!SYMBOL` negates.
// Inactive regions and every directive line are BLANKED to spaces: the text
// keeps its exact length, so byte offsets — the contract the whole pipeline
// is built on — never move. A strongly-typed program should not carry code
// for a target it is not being compiled for.

/// preprocess defines text -> (text', errors as (1-based line, message))
let preprocess (defines : string list) (text : string) : string * (int * string) list =
    if not (text.Contains "#if") then text, []
    else
        let errors = vecNew<int * string> ()
        let out = vecNew<string> ()
        let lines = text.Split '\n'
        // each frame: (this level is ACTIVE, some branch at this level taken)
        let mutable stack : (bool * bool) list = []
        let active () = stack |> List.forall (fun (a, _) -> a)
        let blanked (line : string) : string =
            let mutable b = ""
            for k in 0 .. line.Length - 1 do
                b <- b + (if line.[k] = '\r' then "\r" else " ")
            b
        lines |> Array.iteri (fun i line ->
            let t = line.Trim ()
            let isIf = t.StartsWith "#if" && (t.Length = 3 || t.[3] = ' ' || t.[3] = '\t')
            if isIf then
                let cond = t.Substring(3).Trim ()
                let value =
                    if cond.StartsWith "!" then not (List.contains (cond.Substring(1).Trim ()) defines)
                    else List.contains cond defines
                if cond = "" then vecAdd errors (i + 1, "#if needs a symbol")
                stack <- (value, value) :: stack
                vecAdd out (blanked line)
            elif t = "#else" then
                (match stack with
                 | (_, taken) :: rest -> stack <- (not taken, true) :: rest
                 | [] -> vecAdd errors (i + 1, "#else without #if"))
                vecAdd out (blanked line)
            elif t = "#endif" then
                (match stack with
                 | _ :: rest -> stack <- rest
                 | [] -> vecAdd errors (i + 1, "#endif without #if"))
                vecAdd out (blanked line)
            elif active () then vecAdd out line
            else vecAdd out (blanked line))
        if not (List.isEmpty stack) then
            vecAdd errors (lines.Length, "#if without #endif")
        String.concat "\n" (vecToList out), vecToList errors
