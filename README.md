# F++

## Why

F# is a language worth keeping — the offside rule, unions and records,
pattern matching, computation expressions, a type system that stays out of
the way. But it is chained to a runtime that decides where it can go. A
web page carrying a .NET program starts by downloading and booting a
runtime; a command-line tool ships one or trusts the machine to have it;
startup pays for a JIT before the first line of user code runs. For the
places this project cares about — real-time graphics in the browser, small
native tools, wasm modules that start now — the runtime costs more than
the program.

F++ is F# rebuilt as its own language, the way OCaml is its own language:
compiled ahead of time to wasm and native, no CLR, no JIT, nothing to
install beside the binary. Cutting the tether also removes .NET's ceiling
on the type system — F++ adds typeclasses (`when Num<'a>`), higher-kinded
types, and GADTs, the features F# wanted and the CLR could not carry.

The browser is a first-class target, not a port: zero-copy `ArrayBuffer`
views over pinned arrays, UTF-16 strings on the engine's own `js-string`
builtins, a typed DOM, complete generated WebGPU and WebGL bindings
(extensions included), and a binary command stream that crosses the
wasm↔JS boundary once per render pass — a recorded GPU command costs
~30 ns of machinery, against ~95 ns for a call-per-crossing FFI.

## What

The syntax and semantics you know, extended with typeclasses and
higher-kinded types, compiled ahead of time. Two backends: wasm-GC, and C
over fpprt (an owned precise moving GC) for native binaries and
wasm-linear.

The proof of surface: **FSharp.Data.Adaptive compiles whole and runs** — a
100-test port of its own test suite is green under wasmtime, property
harnesses included (`PORT-ADAPTIVE.md`). The compiler compiles itself; the
self-host fixpoint is byte-identical and gates every change.

- **DESIGN.md** — the language, and why each decision went the way it did
- **STATUS.md** — where things stand, what is being worked towards, what is known broken
- **PLAN.md** — what is built, what is not, in the order it is being built
- **DIVERGENCES.md** — every deliberate departure from F#, with its reason
- **REPRESENTATION.md** — how values are laid out at run time
- **PLAN-CBACK.md** — the C backend and fpprt: value model, the TRUE-structs arc
- **PLAN-THREADS.md** — concurrency/parallelism design: virtual threads, barriers, the GC uniqueness query
- **CLAUDE.md** — how to work in this repo: the gates, and what they cost
- **editors/README.md** — VS Code, Rider, Visual Studio
- **tests/tooling/README.md** — the harnesses that measure rather than assume
- **tests/known-issues/** — the smallest program that shows each open bug
- **PORT-ADAPTIVE.md** — porting FSharp.Data.Adaptive whole, and what it needs

## Getting started

Works the same on Linux, macOS (Intel and Apple Silicon) and Windows —
everything below is .NET and a single wasm runtime.

**Prerequisites**

```bash
# .NET 10 SDK
#   macOS:  brew install --cask dotnet-sdk        (or the installer from
#           https://dotnet.microsoft.com/download)
#   Linux:  your distro's package, or the same installer
dotnet --version          # expect 10.x

# wasmtime, to run what the compiler emits
curl https://wasmtime.dev/install.sh -sSf | bash
# installs to ~/.wasmtime/bin/wasmtime, which is where the test suite looks
```

**Build and test**

```bash
git clone git@github.com:krauthaufen/fpp.git
cd fpp
dotnet build -c Release
dotnet test  -c Release          # 677 tests; exits non-zero if any fail
```

The suite includes the oracle gate: every program in it is also valid F#, so
it runs twice — once under `dotnet fsi`, once under `fpp` + wasmtime — and
the two outputs are diffed byte for byte.

**Compile and run a program**

```bash
cat > hello.fpp <<'EOF'
module Hello

let sq (x : 'a) : 'a when Num<'a> = x * x

let a = print (sq 7)
let b = print (sq 2.5)
let c = print (float32 (sq 1.5h))
EOF

cat > hello.fppproj <<'EOF'
name hello
out  hello.wat
src  hello.fpp
EOF

dotnet run --project src/Fpp.Cli -c Release -- build hello.fppproj
~/.wasmtime/bin/wasmtime -W exceptions=y hello.wat
# 49
# 6.25
# 2.25
```

One generic body, specialized at `int`, `float` and `float16`.

## Editor support

```bash
cd editors/vscode
npm install && npx tsc -p ./
npx @vscode/vsce package --allow-missing-repository
code --install-extension fpp-0.2.0.vsix
```

Then open a folder containing a `.fppproj`. You get diagnostics, hover types
(with their class constraints), completion, go to definition across files,
and an outline. The extension launches the language server out of the
checkout by default — `dotnet run --project src/Fpp.Lsp/Fpp.Lsp.fsproj` —
so editing the compiler and using it are the same tree. Point
`fpp.server.path` at a published binary to skip the rebuild.

See `editors/README.md` for the project-manifest format and for Rider and
Visual Studio.

## Layout

```
src/Fpp.Compiler   the compiler: syntax, analysis, core IR, wasm backend
src/Fpp.Lsp        language server (stdio LSP) over the same Workspace
src/Fpp.Cli        `fpp check` / `fpp build` over the same Workspace
tests/Fpp.Tests    Expecto suite, including the F# oracle gate
stdlib             library sources written in F++
editors/vscode     the VS Code extension
```

The LSP server and the CLI are deliberately thin clients of one `Workspace`
type, so an editor and a build can never disagree about what the program
means.

## License

MIT — see `LICENSE`.
