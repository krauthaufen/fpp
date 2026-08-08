#!/usr/bin/env bash
# Pinnable/fixed/Unmanaged: `use p = fixed arr` pins through the class,
# Unmanaged is compiler-derived for blittable structs and SEALED, and
# sizeof demands it. Native leg (address interop) + diagnostics.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
rt="$root/runtime"
"$fpp" build -o "$out/p.c" "$here/pinnable.fpp"
make -C "$rt" GC_COLLECTOR=mmc build/mmc/libwhippet.a build/mmc/fpprt.o >/dev/null
gcc -O1 -g -I"$rt" -I"$rt/gc/api" -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS="\"$rt/gc/api/mmc-attrs.h\"" -DGC_EMBEDDER="\"$rt/fpprt-embedder.h\"" \
    "$out/p.c" "$here/pinnable-native.c" "$rt/fpprt.c" "$rt/fpprt-lang.c" \
    "$rt/build/mmc/libwhippet.a" -lm -lpthread -o "$out/p"
"$out/p" > "$out/got.txt"
printf '10\n72\n11\n17\nok\n' > "$out/want.txt"
diff -u "$out/want.txt" "$out/got.txt"
# the SEALS: ref elements refuse to pin, instances refuse to be written
printf 'let a = [| "x" |]\nlet go =\n    use p = fixed a\n    print p\n' > "$out/bad1.fpp"
"$fpp" check "$out/bad1.fpp" 2>&1 | grep -q "no instance Unmanaged<string>"
printf 'type Foo = { A : int }\ninstance Unmanaged<Foo>\n' > "$out/bad2.fpp"
"$fpp" check "$out/bad2.fpp" 2>&1 | grep -q "solved by the compiler"
echo "PINNABLE OK (fixed + sealed Unmanaged)"
