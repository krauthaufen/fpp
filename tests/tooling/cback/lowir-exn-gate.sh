#!/usr/bin/env bash
# Exceptions on the wasm-linear backend. `failwith msg` throws Failure(msg)
# through the module's one exception tag; `try … with` is a try_table whose
# catch routes the thrown value to a handler that pattern-matches it (re-throws
# on no match). The wasm-GC oracle does exceptions the same way (`Failure`
# payload, wasm EH), so this diffs against it. Custom `exception` types are not
# covered -- the oracle does not support them either.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
wt="$root/.wasmtime/bin/wasmtime"; [ -x "$wt" ] || wt="$HOME/.wasmtime/bin/wasmtime"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT

cat > "$out/p.fpp" <<'FPP'
module Exn
let f (n : int) : int =
    try
        if n < 0 then failwith "neg" else n * 2
    with
    | Failure msg -> 0 - 1
let g (n : int) : string =
    try
        if n = 0 then failwith "zero"
        elif n = 1 then failwith "one"
        else "big"
    with
    | Failure m -> "caught:" + m
let nested (n : int) : int =
    try
        try
            if n < 0 then failwith "inner" else n
        with
        | Failure m -> 0 - (10 + n)
    with
    | Failure m -> 0 - 1
let r1 = printfn "%d" (f 5)
let r2 = printfn "%d" (f (0 - 3))
let r3 = printfn "%s" (g 0)
let r4 = printfn "%s" (g 1)
let r5 = printfn "%s" (g 9)
let r6 = printfn "%d" (nested 4)
let r7 = printfn "%d" (nested (0 - 2))
FPP

"$fpp" build --lowir -o "$out/low.wasm" "$out/p.fpp"
"$wt" run "$out/low.wasm" > "$out/low.txt"
"$fpp" build -o "$out/gc.wasm" "$out/p.fpp"
"$HOME/.wasmtime/bin/wasmtime" run -W function-references=y,gc=y,exceptions=y "$out/gc.wasm" > "$out/gc.txt"
if diff -u "$out/gc.txt" "$out/low.txt"; then
    echo "LOWIR EXN OK (failwith/try/with == wasm-GC oracle, $(wc -l < "$out/low.txt") lines)"
else
    echo "LOWIR EXN MISMATCH"; exit 1
fi
