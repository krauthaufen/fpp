#!/usr/bin/env bash
# Parity gate: compile <prog.fpp> through BOTH backends, run both, diff
# stdout. The wasm-GC backend is the oracle. Exit 0 only on identical output.
set -e
prog="$1"
[ -f "$prog" ] || { echo "usage: run.sh <prog.fpp>"; exit 2; }
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"

"$fpp" build -o "$out/p.wasm" "$prog"
"$HOME/.wasmtime/bin/wasmtime" run -W function-references=y,gc=y,exceptions=y "$out/p.wasm" > "$out/wasm.txt"

"$fpp" build -o "$out/p.c" "$prog"
gcc -O1 -g -I"$root/runtime" -I"$root/runtime/gc/api" \
    -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$root/runtime/gc/api/semi-attrs.h\"" \
    -DGC_EMBEDDER="\"$root/runtime/fpprt-embedder.h\"" \
    "$out/p.c" "$root/runtime/fpprt.c" "$root/runtime/fpprt-lang.c" \
    "$root/runtime/gc/src/gc-platform-gnu-linux.c" "$root/runtime/gc/src/gc-stack.c" \
    "$root/runtime/gc/src/gc-options.c" "$root/runtime/gc/src/gc-tracepoint.c" \
    "$root/runtime/gc/src/gc-ephemeron.c" "$root/runtime/gc/src/gc-finalizer.c" \
    "$root/runtime/gc/src/semi.c" \
    -I"$root/runtime/gc/src" -lm -lpthread -o "$out/p"
"$out/p" > "$out/c.txt"

if diff -u "$out/wasm.txt" "$out/c.txt"; then
    echo "PARITY OK ($(wc -l < "$out/c.txt") lines)"
else
    echo "PARITY FAILED: $prog"
    exit 1
fi
