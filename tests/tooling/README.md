# Tooling checks

These two exercise the debug build through the tools people actually use. They
need a display, Chrome and VS Code, so they are NOT part of `dotnet test` — run
them by hand when the debug information changes.

## chrome-debug.js — breakpoints and locals in Chrome

Builds nothing itself: point it at a directory holding `prog.wasm`,
`prog.wasm.map` and `prog.fpp` (see `EmitProgramWasmWithSourceMap`), serve it,
then:

    python3 -m http.server 8731        # in that directory
    node tests/tooling/chrome-debug.js

It reads OUR source map, picks the byte offset for a chosen source line, sets a
breakpoint there over CDP, runs the program and prints the paused frame with its
locals. What it proves: the map's offsets land in the right function, and the
locals carry the names and values the source says they should.

Note: `Debugger.setBreakpointByUrl` against the `.fpp` URL does NOT bind from
raw CDP — resolving a source map to original locations is the DevTools
FRONTEND's job, not the backend's. Hence the breakpoint by byte offset, which is
what the frontend would compute anyway.

## vscode-hover — type hovers in real VS Code

Runs the editor's own extension-test host, so the whole pipeline is live:
VS Code -> our extension -> the LSP client -> `Fpp.Lsp` -> the compiler.

    code --extensionDevelopmentPath=tests/tooling/vscode-hover \
         --extensionTestsPath=tests/tooling/vscode-hover/test/index.js \
         --user-data-dir=/tmp/fpp-vscode --password-store=basic \
         --disable-workspace-trust playground

It opens `playground/main.fpp`, waits for the server, and writes the hovers it
got to `/tmp/.../hover-out.json`.

Two things that will waste an hour if you do not know them:
* `--password-store=basic`, or a GNOME keyring dialog blocks startup and the
  extension host never runs.
* the extension resolves the server relative to the WORKSPACE, so opening
  `playground` needs `fpp.server.path` set to a built `Fpp.Lsp` binary.
