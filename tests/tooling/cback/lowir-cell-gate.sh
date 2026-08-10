#!/usr/bin/env bash
# Closure-captured mutables on the wasm-linear backend. A `let mutable` that a
# closure both reads and writes lives in a 1-word heap CELL; the closure
# captures the cell pointer, so mutation is shared. Diffed against the oracle.
set -e
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
wt="$root/.wasmtime/bin/wasmtime"; [ -x "$wt" ] || wt="$HOME/.wasmtime/bin/wasmtime"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
cat > "$out/p.fpp" <<'FPP'
module Cells
let counter () : unit -> int =
    let mutable n = 0
    fun () -> n <- n + 1; n
let mkAdder (start : int) : int -> int =
    let mutable acc = start
    fun x -> acc <- acc + x; acc
let c = counter ()
let r1 = printfn "%d" (c ())
let r2 = printfn "%d" (c ())
let r3 = printfn "%d" (c ())
let a = mkAdder 100
let r4 = printfn "%d" (a 5)
let r5 = printfn "%d" (a 10)
let d = counter ()
let r6 = printfn "%d" (d ())
FPP
"$fpp" build --lowir -o "$out/low.wasm" "$out/p.fpp"
"$wt" run "$out/low.wasm" > "$out/low.txt"
"$fpp" build -o "$out/gc.wasm" "$out/p.fpp"
"$HOME/.wasmtime/bin/wasmtime" run -W function-references=y,gc=y,exceptions=y "$out/gc.wasm" > "$out/gc.txt"
if diff -u "$out/gc.txt" "$out/low.txt"; then
    echo "LOWIR CELL OK (captured mutables == wasm-GC oracle, $(wc -l < "$out/low.txt") lines)"
else echo "LOWIR CELL MISMATCH"; exit 1; fi
