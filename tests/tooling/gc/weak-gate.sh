#!/usr/bin/env bash
# Weak-reference gate: WeakReference clears once its target is unreachable, a
# ConditionalWeakTable entry dies WITH its key (even when the value points
# back at it), GCRoot holds an object until freed, and the cleanup registry
# takes thousands of pending watches — one per value, which is what the
# ported Index needs.
set -e
envfwd=()
for k in FPPRT_MOVING FPPRT_CONSERVATIVE FPP_GC_LOG; do
  if [ -n "${!k+x}" ]; then envfwd+=(--env "$k=${!k}"); fi
done
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
FPP_REACTOR="$here/fpprt_reactor.wasm" "$fpp" build --gc -o "$out/weak.wasm" "$here/weak.fpp"
got=$(wasmtime run -W exceptions=y,gc=y "${envfwd[@]}" "$out/weak.wasm" 2>/dev/null)
want='live true dead false
target 1
entries 2
entries after 1
kept kept
rooted true
freed false
pending 5000 fired 0
drained 5000'
if [ "$got" = "$want" ]; then
    echo "WEAK OK (refs clear, ephemeron table drops dead keys, roots pin, 5000 watches)"
else
    echo "WEAK MISMATCH"
    echo "want: $want"
    echo "got:  $got"
    exit 1
fi
