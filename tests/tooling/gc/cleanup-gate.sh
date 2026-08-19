#!/usr/bin/env bash
# Deterministic-cleanup gate: GC.OnCleanup closures fire exactly once, in
# registration order, at GC.Collect — never while the object is reachable.
# Runs the wasm-linear gc leg (fpprt watch table) under wasmtime.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
FPP_REACTOR="$here/fpprt_reactor.wasm" "$fpp" build --gc -o "$out/cleanup.wasm" "$here/cleanup.fpp"
got=$(wasmtime run -W exceptions=y,gc=y "$out/cleanup.wasm" 2>/dev/null)
want='before
dead 1
dead 2
dead 3
after 3
released
dead kept
dead inner
end'
if [ "$got" = "$want" ]; then
    echo "CLEANUP OK (deterministic: order, liveness, forced collect)"
else
    echo "CLEANUP MISMATCH"
    echo "want: $want"
    echo "got:  $got"
    exit 1
fi
