#!/usr/bin/env bash
# The shared LowIR (Core/LowIR.fs) on the wasm-linear leg: `fpp build --lowir`
# lowers a function's body to LowIR — a small machine IR with tag/box expanded
# to plain shifts, loads and allocations — then emits wasm from THAT, instead
# of the hand-lowering `--linear` uses. A body outside the LowIR subset falls
# back to the hand path, so the two always agree; this program stays inside the
# subset (integers, arithmetic, comparisons, let/mutable, top-level functions
# and recursion, while loops, globals, string literals, int-to-string, concat,
# printfn) so EVERY function here is emitted through LowIR. Its output must
# match the wasm-GC oracle for the same program — one meaning, now across a
# THIRD emission path.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT

cat > "$out/p.fpp" <<'FPP'
module LowIRGate
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
let poly (n : int) : int = (n * n + 3 * n) - 7
let rec collatz (n : int) (steps : int) : int =
    if n <= 1 then steps
    elif n % 2 = 0 then collatz (n / 2) (steps + 1)
    else collatz (3 * n + 1) (steps + 1)
let r1 = printfn "%d" (fib 15)
let r2 = printfn "%d" (fact 7)
let r3 = printfn "%d" (gcd 1071 462)
let r4 = printfn "%d" (poly 9)
let r5 = printfn "%d" (collatz 27 0)
let r6 = printfn "%s" ("F++ " + "shared LowIR")
let mutable acc = 0
let loop =
    let mutable i = 1
    while i <= 100 do
        acc <- acc + i
        i <- i + 1
let r7 = printfn "%d" acc
FPP

# the LowIR emission path — no C toolchain, no hand-lowering for these bodies
"$fpp" build --lowir -o "$out/low.wasm" "$out/p.fpp"
"$root/.wasmtime/bin/wasmtime" run "$out/low.wasm" > "$out/low.txt" 2>/dev/null \
    || "$HOME/.wasmtime/bin/wasmtime" run "$out/low.wasm" > "$out/low.txt"

# the wasm-GC oracle for the same program
"$fpp" build -o "$out/gc.wasm" "$out/p.fpp"
"$HOME/.wasmtime/bin/wasmtime" run -W function-references=y,gc=y,exceptions=y "$out/gc.wasm" > "$out/gc.txt"

if diff -u "$out/gc.txt" "$out/low.txt"; then
    echo "LOWIR OK (Core->LowIR->wasm == wasm-GC oracle, $(wc -l < "$out/low.txt") lines)"
else
    echo "LOWIR MISMATCH"; exit 1
fi
