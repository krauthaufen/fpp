#!/usr/bin/env bash
# The threaded runtime, on both hosts that can spawn threads today:
# NATIVE (pcc + mmc, via make test-threads: 6 mutators under GC churn,
# then the pool + monitor suite) and WASM-LINEAR via emcc -pthread —
# pthreads over workers + SharedArrayBuffer, run headless under node.
# (wasmtime dropped wasi-threads in v47; node is the headless host.)
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
rt="$root/runtime"

make -C "$rt" test-threads > /tmp/threads-native.log 2>&1 \
    || { tail -5 /tmp/threads-native.log; echo "THREADS FAILED (native)"; exit 1; }
grep -q "sum ok" /tmp/threads-native.log && grep -q "mon ok" /tmp/threads-native.log \
    || { echo "THREADS FAILED (native asserts)"; exit 1; }
echo "THREADS OK (native: pcc + mmc, mutators + pool + monitors)"

[ -f /opt/emsdk/emsdk_env.sh ] && . /opt/emsdk/emsdk_env.sh >/dev/null 2>&1
if command -v emcc >/dev/null 2>&1 && command -v node >/dev/null 2>&1; then
    out=$(mktemp -d)
    trap 'rm -rf "$out"' EXIT
    emcc "$rt/test/test_pool.c" "$rt/fpprt.c" "$rt/fpprt-lang.c" \
        "$rt/gc-platform-wasm.c" \
        "$rt/gc/src/gc-stack.c" "$rt/gc/src/gc-options.c" "$rt/gc/src/gc-tracepoint.c" \
        "$rt/gc/src/gc-ephemeron.c" "$rt/gc/src/gc-finalizer.c" "$rt/gc/src/mmc.c" \
        -O1 -pthread -I"$rt/gc/api" -I"$rt/gc/src" -I"$rt" \
        -DNDEBUG -DGC_PRECISE_ROOTS=1 -DGC_NO_BACKGROUND_THREAD=1 \
        -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
        -fwasm-exceptions -sSUPPORT_LONGJMP=wasm -sWASM_LEGACY_EXCEPTIONS=0 \
        -sSTACK_SIZE=8388608 -sPTHREAD_POOL_SIZE=8 -sINITIAL_MEMORY=268435456 \
        -o "$out/tp.js" 2>/dev/null
    got=$(node "$out/tp.js" 2>/dev/null)
    echo "$got" | grep -q "sum ok" && echo "$got" | grep -q "mon ok" \
        || { echo "THREADS FAILED (wasm-linear): $got"; exit 1; }
    echo "THREADS OK (wasm-linear: emcc -pthread under node, workers + SAB)"
else
    echo "THREADS wasm-linear: SKIP (no emcc/node)"
fi
