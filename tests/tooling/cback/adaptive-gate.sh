#!/usr/bin/env bash
# The C-backend adaptive gate: the FSharp.Data.Adaptive port runs on fpprt
# NATIVELY (mmc collector), and — when emcc is available — as WASM-LINEAR
# under wasmtime (mmc single-threaded, longjmp via wasm EH). The suite's
# own "PASSED n FAILED 0" line is the assertion, same as the wasm-GC gate
# in Fpp.Tests. Without the FSharp.Data.Adaptive checkout it SKIPS loudly.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
adaptive="$HOME/projects/FSharp.Data.Adaptive/src/FSharp.Data.Adaptive"
[ -d "$adaptive" ] || { echo "SKIP: no FSharp.Data.Adaptive checkout"; exit 0; }
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT

python3 "$root/tests/port-adaptive.py" "$adaptive" "$out/lib.fpp"
cat "$out/lib.fpp" "$root/tests/adaptive-suite/Tests.fpp" > "$out/suite.fpp"
"$root/src/Fpp.Cli/bin/Release/net10.0/fpp" build -o "$out/suite.c" "$out/suite.fpp"

check() { # file, leg-name
    last=$(grep -E "^PASSED " "$1" | tail -1)
    case "$last" in
        PASSED\ *\ FAILED\ 0) echo "$2: $last" ;;
        *) echo "$2 FAILED: ${last:-no PASSED line}"; tail -5 "$1"; exit 1 ;;
    esac
}

# ---- native (mmc) ----------------------------------------------------------
rt="$root/runtime"
make -C "$rt" GC_COLLECTOR=mmc build/mmc/libwhippet.a build/mmc/fpprt.o >/dev/null
gcc -O2 -g -I"$rt" -I"$rt/gc/api" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    -c "$rt/fpprt-lang.c" -o "$out/fpprt-lang.o"
gcc -O1 -g -I"$rt" -I"$rt/gc/api" -I"$rt/gc/src" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    "$out/suite.c" "$rt/build/mmc/fpprt.o" "$out/fpprt-lang.o" \
    "$rt/build/mmc/libwhippet.a" -lm -lpthread -o "$out/suite"
FPP_HEAP_MB=1024 "$out/suite" > "$out/native.txt"
check "$out/native.txt" "native/mmc"

# ---- wasm-linear (emcc, optional) ------------------------------------------
[ -f /opt/emsdk/emsdk_env.sh ] && . /opt/emsdk/emsdk_env.sh >/dev/null 2>&1
if command -v emcc >/dev/null 2>&1; then
    emcc "$out/suite.c" "$rt/fpprt.c" "$rt/fpprt-lang.c" "$rt/gc-platform-wasm.c" \
        "$rt/gc/src/gc-stack.c" "$rt/gc/src/gc-options.c" "$rt/gc/src/gc-tracepoint.c" \
        "$rt/gc/src/gc-ephemeron.c" "$rt/gc/src/gc-finalizer.c" "$rt/gc/src/mmc.c" \
        -O1 -I"$rt/gc/api" -I"$rt/gc/src" -I"$rt" \
        -DNDEBUG -DGC_PRECISE_ROOTS=1 -DGC_NO_BACKGROUND_THREAD=1 \
        -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
        -fwasm-exceptions -sSUPPORT_LONGJMP=wasm -sWASM_LEGACY_EXCEPTIONS=0 \
        -sSTACK_SIZE=8388608 -s STANDALONE_WASM -s PURE_WASI=1 \
        -s ALLOW_MEMORY_GROWTH=1 -o "$out/suite.wasm"
    "$HOME/.wasmtime/bin/wasmtime" run -W exceptions=y \
        --env FPP_HEAP_MB=1024 "$out/suite.wasm" > "$out/wasm.txt"
    check "$out/wasm.txt" "wasm-linear/mmc"
else
    echo "wasm-linear: SKIP (no emcc)"
fi
