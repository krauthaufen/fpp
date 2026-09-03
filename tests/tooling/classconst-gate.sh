#!/usr/bin/env bash
# A CLASS CONSTANT USED DIRECTLY IN AN EXPRESSION (KNOWN-ISSUES #3 from the
# fpp.base port): `t * (One - One * t)` in a `when Num<'a>` body trapped,
# while binding the constant first worked.
#
# A GATE rather than a conformance suite because there is no oracle: F# has
# no `Num` typeclass, so `dotnet fsi` cannot type-check the file at all. The
# answers are asserted by the program itself.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT

"$fpp" build -o "$out/cc.wasm" "$here/classconst.fpp" > "$out/build.log" 2>&1 || {
    echo "CLASSCONST BUILD FAILED"; head -5 "$out/build.log"; exit 1; }
got=$(wasmtime run -W exceptions=y,gc=y "$out/cc.wasm" 2>&1) || {
    echo "CLASSCONST TRAPPED"; echo "$got" | tail -3; exit 1; }
if [ "$got" != "DONE tests=12 failures=0" ]; then
    echo "CLASSCONST FAILED"; echo "$got"; exit 1
fi
echo "CLASSCONST OK (class constants in expressions, 12 cases: two type parameters, and a sibling member not pinning)"
