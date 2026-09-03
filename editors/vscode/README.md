# F++ for VS Code

Diagnostics, hover types (with class constraints), go-to-definition across
files, and document symbols — all from the F++ language server.

Open a folder containing a `*.fppproj` manifest. The extension activates,
the server finds the manifest by walking up from whichever file you open,
and every file is then checked in the project's declared compile order.

See `editors/README.md` in the repository for the manifest format and for
the Rider and Visual Studio paths.

## Installing on a machine without a checkout

COPYING the extension folder into `~/.vscode/extensions/` does not install
it. VS Code's index is `~/.vscode/extensions/extensions.json`, and an
extension missing from it is invisible — no language server AND no syntax
highlighting, because the grammar is registered from the `package.json` of
a REGISTERED extension. A copied folder looks perfectly correct on disk and
does nothing at all.

Install it the way VS Code expects, with a `.vsix`:

```
code --install-extension fpp-0.2.0.vsix --force
```

`code` is not on `PATH` from a stock macOS install; the CLI lives at
`/Applications/Visual Studio Code.app/Contents/Resources/app/bin/code`.
This works while the editor is running — reload the window afterwards.

A `.vsix` is a zip of `[Content_Types].xml`, `extension.vsixmanifest` and
an `extension/` directory, so one can be built from an installed copy
without `vsce` if npm is not available.

Two things to set on a machine with no repository:

* `"fpp.server.path"` in user settings, pointing at a wrapper that execs
  the published `Fpp.Lsp`. Without it the extension falls back to
  `dotnet run --project src/Fpp.Lsp/Fpp.Lsp.fsproj`, which needs both a
  checkout and the .NET SDK.
* the extension activates on `workspaceContains:**/*.fppproj`, so open the
  FOLDER, not a lone `.fpp` file, or the server never starts. Highlighting
  works either way once the extension is registered.
