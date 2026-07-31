#!/usr/bin/env bash
# The same vertex loop in C and in F++, both compiled to wasm and run under
# wasmtime: fill a 1M-element V3f[], then sum every component 20 times.
set -e
cd "$(dirname "$0")"
root=$(cd ../../.. && pwd)
out=$(mktemp -d)
source /opt/emsdk/emsdk_env.sh >/dev/null 2>&1
emcc -O2 vertices.c -o "$out/c.wasm" -s STANDALONE_WASM -s PURE_WASI=1 >/dev/null 2>&1
dotnet run --no-build -c Release --project "$root/src/Fpp.Cli" -- \
    build -o "$out/f.wasm" vertices.fpp >/dev/null
for w in c f; do
    printf "%-5s " "$w"
    s=$(date +%s%N)
    r=$("$HOME/.wasmtime/bin/wasmtime" run -W gc=y,exceptions=y "$out/$w.wasm" 2>&1 | tail -1)
    e=$(date +%s%N)
    echo "$(( (e-s)/1000000 )) ms   (result $r)"
done
rm -rf "$out"
