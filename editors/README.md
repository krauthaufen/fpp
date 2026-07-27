# Editor support

One language server (`src/Fpp.Lsp`, stdio LSP) behind every editor. It
offers diagnostics, hover types (rendered with their class constraints),
completion, go-to-definition across files, and document symbols; everything
below is a different way of launching the same process.

It runs wherever .NET does — macOS, Linux and Windows alike — since the
server is a plain stdio program and the extension only has to start it.

## Projects

An editor opens a *file*; the compiler needs a *project*, because compile
order is semantic — exports flow forward and a file only sees what came
before it. So a project is stated explicitly, in `<name>.fppproj`:

```
# order is the point of this file
name demo
out  demo.wat
lib  vendor/thing.fppir
src  util.fpp
src  main.fpp
```

The format cannot glob, deliberately: a directory listing would hide the one
fact the file exists to state. Unknown directives are errors, not ignored.

The server finds the manifest by walking up from the opened file, so no
editor has to be told where it is. `fpp check demo.fppproj` and
`fpp build demo.fppproj` use the same manifest, so the editor and the build
never disagree about the file set.

## VS Code

The extension lives in `editors/vscode`.

```bash
cd editors/vscode
npm install
npx tsc -p ./                       # or: npm run compile
npx @vscode/vsce package --allow-missing-repository
code --install-extension fpp-0.2.0.vsix
```

By default it launches the server with `dotnet run --project
src/Fpp.Lsp/Fpp.Lsp.fsproj -c Release`, resolved against the workspace root
— so working on the compiler and using it in the editor are the same
checkout. Point `fpp.server.path` at a published binary to skip the build.

Settings: `fpp.server.path`, `fpp.server.project`, `fpp.trace.server`.
Commands: **F++: Restart Language Server**, **F++: Build Project**.

Syntax highlighting is a TextMate grammar (`syntaxes/fpp.tmLanguage.json`),
which covers `class` / `instance` declarations, operator member names like
`(+)`, `when` constraints and type variables.

## Rider / IntelliJ

JetBrains IDEs do not load LSP servers on their own; the
[LSP4IJ](https://plugins.jetbrains.com/plugin/23257-lsp4ij) plugin does it
without a custom IDE plugin being written. Install it, then
**Settings → Languages & Frameworks → Language Servers → +** and register:

- **Name**: `F++`
- **Command**: `dotnet run --project /path/to/fpp/src/Fpp.Lsp/Fpp.Lsp.fsproj -c Release --`
  (or the path to a published `Fpp.Lsp` binary)
- **File name patterns**: `*.fpp`, mapped to a new language id `fpp`

LSP4IJ also consumes the TextMate grammar in `editors/vscode/syntaxes` if
you register it under **Editor → TextMate Bundles**, pointing at the
`editors/vscode` directory — the bundle layout is the same one VS Code uses.

A native JetBrains plugin (its own parser, its own PSI) would be a separate
project and is not planned: it would duplicate the compiler's front end,
which is the thing this design most wants to keep single.

## Visual Studio

VS 2022 speaks LSP, but only through a VSIX implementing `ILanguageClient` —
there is no configuration-only path like LSP4IJ. That VSIX is a small C#
project (a class with the server's start command, plus a `.vsixmanifest` and
a content-type definition for `.fpp`), but it can only be built on Windows
with the Visual Studio SDK, so it is not in this repo and has not been
written. If you want it, say so and it can be scaffolded — it is perhaps
100 lines, and it launches exactly the same server as the other two.

## What is and is not verified

Tested in CI: the manifest format, project discovery from an opened file,
cross-file go-to-definition, completion contents, and the server's stdio
framing.

Not tested automatically: the editors themselves. The VS Code extension
compiles and packages, and the server it launches is exercised directly over
stdio, but no test drives VS Code's UI.
