# F++ for VS Code

Diagnostics, hover types (with class constraints), go-to-definition across
files, and document symbols — all from the F++ language server.

Open a folder containing a `*.fppproj` manifest. The extension activates,
the server finds the manifest by walking up from whichever file you open,
and every file is then checked in the project's declared compile order.

See `editors/README.md` in the repository for the manifest format and for
the Rider and Visual Studio paths.
