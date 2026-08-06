#!/usr/bin/env bash
# REAL C interop: interop.fpp pins blittable-struct arrays and calls extern
# functions implemented in interop-native.c, which declares the same structs
# INDEPENDENTLY. The byte layout is the contract; both sides check it.
# Runs on mmc (the pinning collector).
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT

"$root/src/Fpp.Cli/bin/Release/net10.0/fpp" build -o "$out/interop.c" "$here/interop.fpp"

rt="$root/runtime"
make -C "$rt" GC_COLLECTOR=mmc build/mmc/libwhippet.a build/mmc/fpprt.o >/dev/null
gcc -O2 -g -I"$rt" -I"$rt/gc/api" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    -c "$rt/fpprt-lang.c" -o "$out/fpprt-lang.o"
gcc -O1 -g -I"$rt" -I"$rt/gc/api" -I"$rt/gc/src" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    "$out/interop.c" "$here/interop-native.c" "$rt/build/mmc/fpprt.o" \
    "$out/fpprt-lang.o" "$rt/build/mmc/libwhippet.a" -lm -lpthread -o "$out/interop"

"$out/interop" > "$out/got.txt"
cat > "$out/want.txt" <<'EOF'
16
12
3
16
32
1
10
40
100
5
done
EOF
if diff -u "$out/want.txt" "$out/got.txt"; then
    echo "C INTEROP OK (native/mmc)"
else
    echo "C INTEROP FAILED (native/mmc)"
    exit 1
fi

# ---- the same contract on wasm32 (emcc, optional) --------------------------
[ -f /opt/emsdk/emsdk_env.sh ] && . /opt/emsdk/emsdk_env.sh >/dev/null 2>&1
if command -v emcc >/dev/null 2>&1; then
    emcc "$out/interop.c" "$here/interop-native.c" "$rt/fpprt.c" \
        "$rt/fpprt-lang.c" "$rt/gc-platform-wasm.c" \
        "$rt/gc/src/gc-stack.c" "$rt/gc/src/gc-options.c" \
        "$rt/gc/src/gc-tracepoint.c" "$rt/gc/src/gc-ephemeron.c" \
        "$rt/gc/src/gc-finalizer.c" "$rt/gc/src/mmc.c" \
        -O1 -I"$rt/gc/api" -I"$rt/gc/src" -I"$rt" \
        -DNDEBUG -DGC_PRECISE_ROOTS=1 -DGC_NO_BACKGROUND_THREAD=1 \
        -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
        -fwasm-exceptions -sSUPPORT_LONGJMP=wasm -sWASM_LEGACY_EXCEPTIONS=0 \
        -sSTACK_SIZE=8388608 -s STANDALONE_WASM -s PURE_WASI=1 \
        -s ALLOW_MEMORY_GROWTH=1 -o "$out/interop.wasm"
    "$HOME/.wasmtime/bin/wasmtime" run -W exceptions=y "$out/interop.wasm" \
        > "$out/got-wasm.txt"
    if diff -u "$out/want.txt" "$out/got-wasm.txt"; then
        echo "C INTEROP OK (wasm-linear)"
    else
        echo "C INTEROP FAILED (wasm-linear)"
        exit 1
    fi
else
    echo "wasm-linear: SKIP (no emcc)"
fi
