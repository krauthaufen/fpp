#!/usr/bin/env bash
# A WITNESS SAYS WHAT THE TYPE IS. `typeName<'a>`/`sizeof<'a>` are the
# observable half of that, across every channel a witness reaches a body by:
# a caller's argument, a class' slots read off `self`, and the SLOT WITNESS
# ABI for a vtable member generic beyond its class.
#
# A GATE rather than a conformance suite because there is no oracle: F#
# spells these `typeof<'a>.Name` and answers "Int32", so `dotnet fsi` cannot
# stand in.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
wt="${WASMTIME:-$HOME/.wasmtime/bin/wasmtime}"
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT

"$fpp" build -o "$out/tw.wasm" "$here/typewitness.fpp" > "$out/build.log" 2>&1 || {
    echo "TYPEWITNESS BUILD FAILED"; head -20 "$out/build.log"; exit 1; }
got=$("$wt" run -W function-references=y,gc=y,exceptions=y \
      --preload fpprt="$root/tests/tooling/gc/fpprt_reactor_mmc.wasm" \
      "$out/tw.wasm" 2>&1) || {
    echo "TYPEWITNESS TRAPPED"; echo "$got" | tail -5; exit 1; }
if [ "$(echo "$got" | tail -1)" != "DONE tests=22 failures=0" ]; then
    echo "TYPEWITNESS FAILED"; echo "$got"; exit 1
fi
echo "TYPEWITNESS OK (22 cases: concrete, generic function, generic class, vtable row, slot witnesses)"
