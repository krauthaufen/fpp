#!/usr/bin/env bash
# Build the fpprt+Whippet runtime as importable wasm REACTORS: exports the
# linear memory and the alloc/GC/root/frame API a GC-mode F++ module imports.
# Requires emscripten (~/emsdk). The mutator can't touch fpprt's thread-local
# top-frame or its static-inline helpers, so fpprt-wasm-shim.c re-exposes them
# (frame push/pop, scalar register_type, typeid read) as real functions.
#
# TWO collectors, two artifacts:
#   fpprt_reactor.wasm      semi — moves EVERYTHING every collection, the
#                           shakeout collector the fixpoint battery runs on
#   fpprt_reactor_mmc.wasm  mmc — Immix-style mark-region with REAL per-object
#                           pinning (fpprt_pin), what the browser legs and the
#                           zero-copy views need; the product collector
set -e
rt="$HOME/projects/fpp/runtime"
source "$HOME/emsdk/emsdk_env.sh" >/dev/null 2>&1
cd "$rt"; mkdir -p build/wasm
COMMON="gc-platform-wasm.c gc/src/gc-stack.c gc/src/gc-options.c gc/src/gc-tracepoint.c gc/src/gc-ephemeron.c gc/src/gc-finalizer.c fpprt.c fpprt-wasm-shim.c"
EXPORTS='_fpprt_init,_fpprt_alloc,_fpprt_alloc_array,_fpprt_register_type_s,_fpprt_write_ref,_fpprt_safepoint,_fpprt_add_static_roots,_fpprt_allocated_bytes,_fpprt_frame_push,_fpprt_frame_pop,_fpprt_tid_of,_fpprt_wasm_roots_base,_fpprt_wasm_roots_register,_fpprt_tid2cid_base,_fpprt_wasm_refoffs_base,_fpprt_wasm_witness_base,_fpprt_tid_scans,_fpprt_watch,_fpprt_drain1,_fpprt_collect,_fpprt_pin,_fpprt_can_pin,_fpprt_idhash'
FLAGS="-O2 -Igc/api -Igc/src -I. -DNDEBUG -DGC_PRECISE_ROOTS=1 \
  --no-entry -s STANDALONE_WASM -s PURE_WASI=1 -s ALLOW_MEMORY_GROWTH=1 -s ERROR_ON_UNDEFINED_SYMBOLS=0"
emcc $COMMON gc/src/semi.c $FLAGS \
  -DGC_ATTRS=\""$rt/gc/api/semi-attrs.h"\" -DGC_EMBEDDER=\""$rt/fpprt-embedder.h"\" \
  -s EXPORTED_FUNCTIONS="$EXPORTS" \
  -o build/wasm/fpprt_reactor.wasm
emcc $COMMON gc/src/mmc.c $FLAGS -DGC_NO_BACKGROUND_THREAD=1 -DGC_PARALLEL=0 \
  -DGC_ATTRS=\""$rt/gc/api/mmc-attrs.h"\" -DGC_EMBEDDER=\""$rt/fpprt-embedder.h"\" \
  -s EXPORTED_FUNCTIONS="$EXPORTS" \
  -o build/wasm/fpprt_reactor_mmc.wasm
echo "semi: $(ls -l build/wasm/fpprt_reactor.wasm | awk '{print $5}') bytes"
echo "mmc:  $(ls -l build/wasm/fpprt_reactor_mmc.wasm | awk '{print $5}') bytes"

# refresh the repo copies the harness and the shipped CLI resolve
here=$(cd "$(dirname "$0")" && pwd)
cp build/wasm/fpprt_reactor.wasm build/wasm/fpprt_reactor_mmc.wasm "$here/"
echo "copied to $here"
