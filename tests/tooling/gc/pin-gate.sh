#!/usr/bin/env bash
# Real per-object pinning under moving GC (mmc): a pinned object keeps its
# address across a compacting collection; after Array.unpin it may move again.
set -euo pipefail
cd "$(dirname "$0")/../../.."
FPP=src/Fpp.Cli/bin/Release/net10.0/fpp
WASMTIME="${WASMTIME:-$HOME/.wasmtime/bin/wasmtime}"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
"$FPP" build -o "$out/pin.wasm" tests/tooling/gc/pin.fpp >/dev/null 2>&1
res=$(FPPRT_HEAP_MB=32 "$WASMTIME" run -W gc=y,exceptions=y --env FPPRT_MOVING=1 "$out/pin.wasm" 2>&1)
echo "$res"
for line in "pinned stable: true" "data intact while pinned: true" \
            "moved after unpin: true" "data intact after move: true"; do
    echo "$res" | grep -qF "$line" || { echo "PIN-GATE FAIL: missing '$line'"; exit 1; }
done
echo "pin-gate: OK"
