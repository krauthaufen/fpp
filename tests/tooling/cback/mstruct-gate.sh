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
printf '3\n42\n3\n99\n42\n7\n10\n11\n13\n' > "$out/want.txt"
if diff -u "$out/want.txt" "$out/got.txt"; then
    echo "MUTABLE STRUCTS OK (fsi-pinned)"
else
    echo "MUTABLE STRUCTS FAILED"
    exit 1
fi
