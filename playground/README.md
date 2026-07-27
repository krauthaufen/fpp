# Playground

A small two-file project for poking at the editor support.

## Setup

Install the extension once (see `editors/README.md`), then open the
**repository root** in VS Code and open `playground/main.fpp`. The language
server finds `playground.fppproj` by walking up from the file, so both
files are checked in their declared compile order — no configuration.

## Things to try

**Hover** — the signatures carry their class constraints:

- `double` in main.fpp → `'a -> 'b   when Add<'a, 'a> with Result = 'b`
- `sumOf` in vec.fpp → `array<'a> -> 'a -> 'a   when Num<'a>`
- `clamp` in vec.fpp → constrained by `MinMax<'a>` alone — no ordering
- `sqrt`, `min`, `compare` anywhere → the prelude classes behind them
- `p`, `q`, `halves` → concrete types (`V2d`, `array<float16>`)

**Go to definition (F12)** — `dot`, `lengthOf`, `clamp` in main.fpp jump
into vec.fpp; works on types (`V2d`) too.

**Completion** — type `Seq.` or `String.` or just start an identifier:
every entry shows its generalized type with constraints.

**Diagnostics** — uncomment the `bad1`/`bad2`/`bad3` lines at the bottom of
main.fpp and watch the errors appear as you type. Note the operator errors
name the missing instance (`no instance Add<int, string>`), not a
unification trace.

**Outline** — the symbols panel shows both modules' structure.

**Your own typeclasses** — `classes.fpp` declares `Show`, `Monoid` and
`Norm` (an associated type). Hover `describe` and `mconcat`: the
constraints ride the inferred signatures. `mconcat` folds ints, strings
and vectors from one body; `norm`'s result type is decided by the
instance, not written at the use.

## Build and run

```bash
./playground/run.sh
```

or by hand:


```bash
dotnet run --project src/Fpp.Cli -c Release -- build playground/playground.fppproj
~/.wasmtime/bin/wasmtime -W exceptions=y playground/playground.wat
```
