module Fpp.Project

open Fpp.Prelude

// A project file names the sources IN COMPILE ORDER. That order is
// semantic — exports flow forward, and a file only sees what came before it
// — so the format deliberately cannot glob. A directory listing would hide
// the one fact the file exists to state.
//
//   # comment
//   name demo
//   out  demo.wat
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
      Sources : string list }

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
            | other -> vecAdd errors (i + 1, "unknown directive '" + other + "'")
            if arg = "" && directive <> "name" then
                vecAdd errors (i + 1, directive + " needs an argument")
    if vecLen sources = 0 then vecAdd errors (1, "project names no sources")
    { Loaded =
        { Path = hostCanonicalize projectPath
          Name = name
          Out = (if out = "" then name + ".wat" else out)
          Libs = vecToList libs
          Sources = vecToList sources }
      Errors = vecToList errors }

/// A project that is not there is not an exception: the caller reports the
/// miss with the diagnostics it already owns.
let read (projectPath : string) : LoadResult =
    match hostReadText projectPath with
    | Some text -> parse projectPath text
    | None ->
        { Loaded = { Path = projectPath; Name = ""; Out = ""; Libs = []; Sources = [] }
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
