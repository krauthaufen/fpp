#!/usr/bin/env bash
# GC.ReuseIfUnique on the fpprt leg: a function-local array reuses in
# place, a static-held one refuses; exact output is the assertion.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
rt="$root/runtime"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
"$fpp" build -o "$out/p.c" "$root/tests/tooling/gcuniq.fpp"
gcc -O1 -I"$rt" -I"$rt/gc/api" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/semi-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    "$out/p.c" "$rt/fpprt.c" "$rt/fpprt-lang.c" \
    "$rt/gc/src/gc-platform-gnu-linux.c" "$rt/gc/src/gc-stack.c" \
    "$rt/gc/src/gc-options.c" "$rt/gc/src/gc-tracepoint.c" \
    "$rt/gc/src/gc-ephemeron.c" "$rt/gc/src/gc-finalizer.c" "$rt/gc/src/semi.c" \
    -I"$rt/gc/src" -lm -lpthread -o "$out/p"
got=$("$out/p")
want="reused 70
shared stays
2
4"
[ "$got" = "$want" ] || { echo "GCUNIQ FAILED:"; echo "$got"; exit 1; }
echo "GCUNIQ OK (local reuses, shared refuses)"
