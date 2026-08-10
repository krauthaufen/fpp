#!/usr/bin/env bash
# Compile an .fpp through the GC (fpprt/Whippet) wasm-linear backend, link it
# with the fpprt reactor via wasm-merge, and run it under wasmtime.
#   run-gc.sh PROG.fpp            -> prints program output
# Env: FPP (compiler), REACTOR (fpprt_reactor.wasm). wasm-merge emits bytes
# wasmtime rejects, so its TEXT output is re-encoded through wasm-tools.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
fpp="${FPP:-$root/src/Fpp.Cli/bin/Release/net10.0/fpp}"
reactor="${REACTOR:-$HOME/projects/fpp/runtime/build/wasm/fpprt_reactor.wasm}"
wt="$HOME/.wasmtime/bin/wasmtime"
wm="$HOME/emsdk/upstream/bin/wasm-merge"
src="$1"; out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
"$fpp" build --gc -o "$out/prog.wasm" "$src"
"$wm" -all "$reactor" fpprt "$out/prog.wasm" mutator -S -o "$out/f.wat" 2>/dev/null
wasm-tools parse "$out/f.wat" -o "$out/f.wasm"
"$wt" run "$out/f.wasm"
