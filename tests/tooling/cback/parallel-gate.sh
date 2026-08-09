#!/usr/bin/env bash
# The parallel combinators, three ways from ONE program: the wasm-GC
# oracle runs the phases sequentially (P = 1), the native fpprt leg runs
# them across the pool (mmc collector — the pool is multithreaded), and
# the wasm-linear leg runs them under node with emcc -pthread. Identical
# output is the whole assertion: results are chunking-independent.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
rt="$root/runtime"
prog="$root/tests/tooling/parallel.fpp"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT

"$fpp" build --strict -o "$out/p.wasm" "$prog"
"$HOME/.wasmtime/bin/wasmtime" run -W function-references=y,gc=y,exceptions=y "$out/p.wasm" > "$out/wasm.txt"

"$fpp" build -o "$out/p.c" "$prog"
make -C "$rt" GC_COLLECTOR=mmc build/mmc/libwhippet.a build/mmc/fpprt.o >/dev/null
gcc -O2 -I"$rt" -I"$rt/gc/api" -I"$rt/gc/src" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    "$out/p.c" "$rt/build/mmc/fpprt.o" "$rt/fpprt-lang.c" \
    "$rt/build/mmc/libwhippet.a" -lm -lpthread -o "$out/p"
FPP_HEAP_MB=512 "$out/p" > "$out/native.txt"
diff -u "$out/wasm.txt" "$out/native.txt" \
    || { echo "PARALLEL MISMATCH (native)"; exit 1; }
echo "PARALLEL OK (oracle sequential == native pool, $(wc -l < "$out/native.txt") lines)"

[ -f /opt/emsdk/emsdk_env.sh ] && . /opt/emsdk/emsdk_env.sh >/dev/null 2>&1
if command -v emcc >/dev/null 2>&1 && command -v node >/dev/null 2>&1; then
    emcc "$out/p.c" "$rt/fpprt.c" "$rt/fpprt-lang.c" "$rt/gc-platform-wasm.c" \
        "$rt/gc/src/gc-stack.c" "$rt/gc/src/gc-options.c" "$rt/gc/src/gc-tracepoint.c" \
        "$rt/gc/src/gc-ephemeron.c" "$rt/gc/src/gc-finalizer.c" "$rt/gc/src/mmc.c" \
        -O1 -pthread -I"$rt/gc/api" -I"$rt/gc/src" -I"$rt" \
        -DNDEBUG -DGC_PRECISE_ROOTS=1 -DGC_NO_BACKGROUND_THREAD=1 \
        -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
        -fwasm-exceptions -sSUPPORT_LONGJMP=wasm -sWASM_LEGACY_EXCEPTIONS=0 \
        -sSTACK_SIZE=8388608 -sPTHREAD_POOL_SIZE=8 -sINITIAL_MEMORY=268435456 \
        -sEXIT_RUNTIME=1 -o "$out/p.js" 2>/dev/null
    FPP_HEAP_MB=512 node "$out/p.js" > "$out/linear.txt" 2>/dev/null
    diff -u "$out/wasm.txt" "$out/linear.txt" \
        || { echo "PARALLEL MISMATCH (wasm-linear)"; exit 1; }
    echo "PARALLEL OK (wasm-linear pthread pool matches)"
else
    echo "PARALLEL wasm-linear: SKIP (no emcc/node)"
fi
