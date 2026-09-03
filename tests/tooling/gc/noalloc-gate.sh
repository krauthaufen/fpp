#!/usr/bin/env bash
# NO-BOXING gate: the by-value struct shapes must reach the heap ZERO times.
#
# The answer is checked too, but the point of this gate is the ALLOCATION: a
# struct crossing a call — as an argument, as a result, as a nested result, or
# as a module-level global read by value — is passed in registers and written
# through a destination on the raw struct stack. None of that is the
# collector's business, so four million iterations must not collect once.
#
# Why a gate and not a conformance suite: a suite compares OUTPUT, and every
# one of these shapes answered correctly while quietly allocating. The heap is
# sized so that one small object per iteration cannot possibly fit.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT

"$fpp" build -o "$out/noalloc.wasm" "$here/noalloc.fpp" > "$out/build.log" 2>&1 || {
    echo "NOALLOC BUILD FAILED"; head -5 "$out/build.log"; exit 1; }

log="$out/run.log"
wasmtime run -W exceptions=y,gc=y --env FPPRT_HEAP_MB=64 \
    "$out/noalloc.wasm" > "$out/stdout" 2> "$log" || {
    echo "NOALLOC RUN FAILED"; tail -5 "$log"; exit 1; }

got=$(head -1 "$out/stdout")
want="5.99993e+08 999 6 5.00006e+11 3000000 3e+06"
if [ "$got" != "$want" ]; then
    echo "NOALLOC WRONG ANSWER"; echo "want: $want"; echo "got:  $got"; exit 1
fi

# The program reports the runtime's own lifetime allocation counter across the
# two loops. It must be EXACTLY zero: not "no collection happened", which
# proves nothing when the heap can grow instead of collecting — that proxy was
# tried first and reported success while 236 MB went by.
bytes=$(sed -n 's/^allocated //p' "$out/stdout")
if [ "$bytes" != "0" ]; then
    echo "NOALLOC FAILED — a by-value struct shape is allocating again: $bytes bytes over 4M calls"
    exit 1
fi
echo "NOALLOC OK (7M calls: struct args/results/nested/global/struct-CLASS + int and STRUCT byref-as-stack-offset — 0 bytes allocated)"
