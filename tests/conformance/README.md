# fsc conformance — differential gate

Curated ports of dotnet/fsharp `tests/fsharp/core` suites into the common
F#/F++ subset (sparse checkout at `~/projects/fsharp-tests`). Each
`suites/<name>.fpp` is self-checking: silent on pass, `NO: <test>` per
failure, and a final `DONE tests=N failures=0` line — the test COUNT is part
of the contract, so a silently stubbed/dropped test shows up as a count
mismatch against the oracle.

The oracle is `dotnet fsi` (real F#), cached in `expected/`:

    ./run.sh                 # gate every suite (fpp build --gc + wasmtime vs expected)
    ./run.sh letrec          # one suite
    ./run.sh --regen [name]  # refresh expected/ from dotnet fsi (after editing a suite)

Porting rules: drop the parts outside the subset WITH an in-file `DROPPED:`
comment naming the feature; keep original test names; route output to stdout
(`stderr` in the originals); `!x` in argument position needs parens (`g (!x)`
— F++ parser gap); `List.map string`-style bare conversions are the known
backend stub (CLAUDE.md) — eta-expand them.

skip.txt lists whole suites that cannot fit, as `name: reason` lines.
