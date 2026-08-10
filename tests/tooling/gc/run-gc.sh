#!/usr/bin/env bash
# Compile an .fpp through the GC (fpprt/Whippet) wasm-linear backend and run it.
# `fpp build --gc` now links the fpprt reactor itself (wasm-merge + wasm-tools),
# so this is a thin wrapper. Env: FPP, FPP_REACTOR, FPP_WASM_MERGE, FPP_WASM_TOOLS.
set -e
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../../.." && pwd)
fpp="${FPP:-$root/src/Fpp.Cli/bin/Release/net10.0/fpp}"
wt="$HOME/.wasmtime/bin/wasmtime"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
"$fpp" build --gc -o "$out/f.wasm" "$1"
"$wt" run -W gc=y,exceptions=y "$out/f.wasm"
