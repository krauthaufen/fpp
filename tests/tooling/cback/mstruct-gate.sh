#!/usr/bin/env bash
# Mutable-struct semantics: stack values, in-place mutation, copy on
# binding and assignment. The REFERENCE is dotnet fsi — the wasm-GC
# oracle's structs are the workaround this backend replaces. Expected
# output below was produced by fsi and is pinned.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
"$root/src/Fpp.Cli/bin/Release/net10.0/fpp" build -o "$out/m.c" "$here/mstruct.fpp"
rt="$root/runtime"
make -C "$rt" GC_COLLECTOR=mmc build/mmc/libwhippet.a build/mmc/fpprt.o >/dev/null
gcc -O2 -g -I"$rt" -I"$rt/gc/api" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    -c "$rt/fpprt-lang.c" -o "$out/fpprt-lang.o"
gcc -O1 -g -I"$rt" -I"$rt/gc/api" -I"$rt/gc/src" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    "$out/m.c" "$rt/build/mmc/fpprt.o" "$out/fpprt-lang.o" \
    "$rt/build/mmc/libwhippet.a" -lm -lpthread -o "$out/m"
"$out/m" > "$out/got.txt"
printf '3\n42\n3\n99\n42\n7\n10\n11\n13\nhello\n200001\nhello\nbye\n' > "$out/want.txt"
if diff -u "$out/want.txt" "$out/got.txt"; then
    echo "MUTABLE STRUCTS OK (fsi-pinned, mmc)"
else
    echo "MUTABLE STRUCTS FAILED (mmc)"
    exit 1
fi

# the SHAKEOUT leg: semi moves EVERYTHING every collection — a missed
# frame-pod registration for a ref-holding stack struct dies here
gcc -O1 -g -I"$rt" -I"$rt/gc/api" -I"$rt/gc/src" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/semi-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    "$out/m.c" "$rt/fpprt.c" "$rt/fpprt-lang.c" \
    "$rt/gc/src/gc-platform-gnu-linux.c" "$rt/gc/src/gc-stack.c" \
    "$rt/gc/src/gc-options.c" "$rt/gc/src/gc-tracepoint.c" \
    "$rt/gc/src/gc-ephemeron.c" "$rt/gc/src/gc-finalizer.c" "$rt/gc/src/semi.c" \
    -lm -lpthread -o "$out/msemi"
FPP_HEAP_MB=2 "$out/msemi" 2>/dev/null > "$out/got-semi.txt"
if diff -u "$out/want.txt" "$out/got-semi.txt"; then
    echo "MUTABLE STRUCTS OK (fsi-pinned, semi shakeout)"
else
    echo "MUTABLE STRUCTS FAILED (semi)"
    exit 1
fi
