#!/usr/bin/env bash
# Compare F++'s pinned array stride against the one emscripten actually emits.
# The battery pins these numbers as constants; this is what verifies them
# against a real C compiler rather than against a reading of the ABI.
set -e
cd "$(dirname "$0")"
root=$(cd ../../.. && pwd)
out=$(mktemp -d)

source /opt/emsdk/emsdk_env.sh >/dev/null 2>&1
emcc -O0 layout.c -o "$out/layout.js" -s ENVIRONMENT=node >/dev/null 2>&1
echo "emscripten:"
node "$out/layout.js" | sed 's/^/  /'

dotnet run --no-build -c Release --project "$root/src/Fpp.Cli" -- \
    build -o "$out/layout.wasm" layout.fpp >/dev/null
echo "F++ (V3f V2d V2f V3i V3d C3b C4b Mixed strides):"
"$HOME/.wasmtime/bin/wasmtime" run -W gc=y,exceptions=y "$out/layout.wasm" | sed 's/^/  /'
rm -rf "$out"
