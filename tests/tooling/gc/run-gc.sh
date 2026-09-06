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
# FORWARD the runtime env to the guest. wasmtime does NOT inherit the host
# environment, so a bare `FPPRT_MOVING=1 run-gc.sh` was silently ignored and
# the reactor ran in its default mode — which made every "moving" test here
# actually a conservative one. Pass through the FPPRT_*/FPP_GC_LOG knobs the
# reactor reads (see the getenv list in mmc.c / fpprt.c / fpprt-embedder.h).
envfwd=()
for k in FPPRT_MOVING FPPRT_CONSERVATIVE FPPRT_TRACEDBG FPPRT_ROOTCHECK \
         FPPRT_HEAP_MB FPPRT_HEAP_FIXED FPPRT_HEAP_POLICY FPPRT_HEAP_EXPANSIVENESS \
         FPPRT_HEAP_THRESHOLD_MB FPP_GC_LOG; do
    if [ -n "${!k+x}" ]; then envfwd+=(--env "$k=${!k}"); fi
done
"$wt" run -W gc=y,exceptions=y "${envfwd[@]}" "$out/f.wasm"
