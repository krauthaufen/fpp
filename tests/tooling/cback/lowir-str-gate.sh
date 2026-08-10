#!/usr/bin/env bash
# String methods on the wasm-linear backend: StartsWith / EndsWith / Contains /
# IndexOf / Substring, hand-emitted runtime routines over the [cid][len][u16]
# layout. Diffed against the wasm-GC oracle.
set -e
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
wt="$root/.wasmtime/bin/wasmtime"; [ -x "$wt" ] || wt="$HOME/.wasmtime/bin/wasmtime"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
cat > "$out/p.fpp" <<'FPP'
module Str
let s = "hello world"
let r1 = printfn "%b" (s.StartsWith "hello")
let r2 = printfn "%b" (s.StartsWith "world")
let r3 = printfn "%b" (s.EndsWith "world")
let r4 = printfn "%b" (s.Contains "lo w")
let r5 = printfn "%b" (s.Contains "xyz")
let r6 = printfn "%d" (s.IndexOf "world")
let r7 = printfn "%d" (s.IndexOf "zzz")
let r8 = printfn "%s" (s.Substring 6)
let r9 = printfn "%s" (s.Substring (0, 5))
let r10 = printfn "%d" ((s.Substring 6).Length)
FPP
"$fpp" build --lowir -o "$out/low.wasm" "$out/p.fpp"
"$wt" run "$out/low.wasm" > "$out/low.txt"
"$fpp" build -o "$out/gc.wasm" "$out/p.fpp"
"$HOME/.wasmtime/bin/wasmtime" run -W function-references=y,gc=y,exceptions=y "$out/gc.wasm" > "$out/gc.txt"
if diff -u "$out/gc.txt" "$out/low.txt"; then
    echo "LOWIR STR OK (string methods == wasm-GC oracle, $(wc -l < "$out/low.txt") lines)"
else echo "LOWIR STR MISMATCH"; exit 1; fi
