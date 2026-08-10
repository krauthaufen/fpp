#!/usr/bin/env bash
# The DIRECT wasm-linear backend (slice 1): `fpp build --linear` emits a
# wasm module over linear memory with NO C compiler and NO emscripten in
# the path. It runs under wasmtime with nothing but a wasm runtime, and
# its output must match the wasm-GC oracle for the same program — one
# meaning across two independent emitters. Covers the slice: integers,
# arithmetic, comparisons, let, top-level functions and recursion, while
# loops, mutable globals, string literals, int-to-string, concat, printfn.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT

cat > "$out/p.fpp" <<'FPP'
module WasmLin
let rec fib (n : int) : int = if n < 2 then n else fib (n - 1) + fib (n - 2)
let rec fact (n : int) : int = if n <= 1 then 1 else n * fact (n - 1)
let gcd (a : int) (b : int) : int =
    let mutable x = a
    let mutable y = b
    while y <> 0 do
        let t = y
        y <- x % y
        x <- t
    x
let r1 = printfn "%d" (fib 15)
let r2 = printfn "%d" (fact 7)
let r3 = printfn "%d" (gcd 1071 462)
let r4 = printfn "%s" ("F++ " + "direct wasm-linear")
let mutable acc = 0
let loop =
    let mutable i = 1
    while i <= 100 do
        acc <- acc + i
        i <- i + 1
let r5 = printfn "%d" acc
FPP

# the direct linear module — no C toolchain touched
"$fpp" build --linear -o "$out/lin.wasm" "$out/p.fpp"
"$root/.wasmtime/bin/wasmtime" run "$out/lin.wasm" > "$out/lin.txt" 2>/dev/null \
    || "$HOME/.wasmtime/bin/wasmtime" run "$out/lin.wasm" > "$out/lin.txt"

# the wasm-GC oracle for the same program
"$fpp" build -o "$out/gc.wasm" "$out/p.fpp"
"$HOME/.wasmtime/bin/wasmtime" run -W function-references=y,gc=y,exceptions=y "$out/gc.wasm" > "$out/gc.txt"

if diff -u "$out/gc.txt" "$out/lin.txt"; then
    echo "WASMLIN OK (direct linear == wasm-GC oracle, no C compiler, $(wc -l < "$out/lin.txt") lines)"
else
    echo "WASMLIN MISMATCH"; exit 1
fi
