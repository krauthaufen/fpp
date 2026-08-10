#!/usr/bin/env bash
# Build the fpprt+Whippet runtime as an importable wasm REACTOR: exports its
# linear memory and the alloc/GC/root/frame API a GC-mode F++ module imports.
# Requires emscripten (~/emsdk). The mutator can't touch fpprt's thread-local
# top-frame or its static-inline helpers, so fpprt-wasm-shim.c re-exposes them
# (frame push/pop, scalar register_type, typeid read) as real functions.
set -e
rt="$HOME/projects/fpp/runtime"
source "$HOME/emsdk/emsdk_env.sh" >/dev/null 2>&1
cd "$rt"; mkdir -p build/wasm
SRCS="gc-platform-wasm.c gc/src/gc-stack.c gc/src/gc-options.c gc/src/gc-tracepoint.c gc/src/gc-ephemeron.c gc/src/gc-finalizer.c fpprt.c fpprt-wasm-shim.c gc/src/semi.c"
emcc $SRCS -O2 -Igc/api -Igc/src -I. -DNDEBUG -DGC_PRECISE_ROOTS=1 \
  -DGC_ATTRS=\""$rt/gc/api/semi-attrs.h"\" -DGC_EMBEDDER=\""$rt/fpprt-embedder.h"\" \
  --no-entry -s STANDALONE_WASM -s PURE_WASI=1 -s ALLOW_MEMORY_GROWTH=1 -s ERROR_ON_UNDEFINED_SYMBOLS=0 \
  -s EXPORTED_FUNCTIONS='_fpprt_init,_fpprt_alloc,_fpprt_alloc_array,_fpprt_register_type_s,_fpprt_write_ref,_fpprt_safepoint,_fpprt_add_static_roots,_fpprt_allocated_bytes,_fpprt_frame_push,_fpprt_frame_pop,_fpprt_tid_of,_fpprt_wasm_roots_base,_fpprt_wasm_roots_register' \
  -o build/wasm/fpprt_reactor.wasm
echo "reactor: $(ls -l build/wasm/fpprt_reactor.wasm | awk '{print $5}') bytes"
