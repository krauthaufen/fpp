#!/usr/bin/env bash
# Intrinsic type extensions on BUILTIN scalar types (`type string with member
# s.Foo ...`). F++ spelling; F# writes `type System.String with` (its BCL
# names are a separate canonicalization). String routes through the member
# index (not a nonexistent $str primitive); int/float/bool resolve directly.
set -e
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/.." && pwd)
fpp="${FPP:-$root/../src/Fpp.Cli/bin/Release/net10.0/fpp}"
wt="${WASMTIME:-$HOME/.wasmtime/bin/wasmtime}"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
cat > "$out/e.fpp" <<'EOF'
type string with
    member s.Shout () : string = s + "!"
type int with
    member x.Double : int = x * 2
type float with
    member x.Squared : float = x * x
type bool with
    member b.Flip : bool = not b
let go = printfn "%s %d %g %b" (("hi").Shout ()) ((21).Double) ((3.0).Squared) ((true).Flip)
EOF
"$fpp" build --strict -o "$out/e.wasm" "$out/e.fpp" >/dev/null 2>&1
got=$("$wt" run -W gc=y,exceptions=y "$out/e.wasm")
want="hi! 42 9 false"
if [ "$got" = "$want" ]; then echo "BUILTIN EXTENSION OK (string/int/float/bool member extensions resolve)"
else echo "BUILTIN EXTENSION WRONG: want [$want] got [$got]"; exit 1; fi
