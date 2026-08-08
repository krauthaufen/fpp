#!/usr/bin/env bash
# The browser-interop gate: DOM via the generic "js" primitives, typed
# number accessors, string round-trips, an F++ closure as a real event
# listener, and ZERO-COPY TypedArray aliasing over a pinned array — both
# directions. Needs Chrome (headed-chrome) and node; skips cleanly without.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
command -v node >/dev/null || { echo "JSINTEROP SKIPPED (no node)"; exit 0; }
[ -e /home/schorsch/.headed-chrome/index.js ] || { echo "JSINTEROP SKIPPED (no headed-chrome)"; exit 0; }
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
"$fpp" build -o "$here/jsdemo.wasm" "$here/jsdemo.fpp"
"$fpp" build -o "$here/webgl.wasm" "$here/webgl.fpp"
cd "$root"
python3 -m http.server 8734 >/dev/null 2>&1 &
srv=$!
trap 'kill $srv 2>/dev/null || true' EXIT
sleep 1
got=$(node "$here/drive.js")
want='{"log":["7","","made","","1","9","7","0","","ready",""],"madeText":"hello from F++","viewY1":4.5,"clicks":2,"x0AfterJsWrite":95}'
if [ "$got" = "$want" ]; then
    echo "JS INTEROP OK (dom, callbacks, strings, zero-copy views)"
else
    echo "JS INTEROP MISMATCH"
    echo "want: $want"
    echo "got:  $got"
    exit 1
fi
# the WebGL leg: pinned verts -> view -> bufferData -> draw -> readPixels
# into a pinned struct -> F++ checks the color. Zero copies end to end.
got=$(node "$here/gldrive.js")
want='{"log":["2","5","5","1","2","7","0","gl-done"]}'
if [ "$got" = "$want" ]; then
    echo "WEBGL OK (zero-copy upload and readback)"
else
    echo "WEBGL MISMATCH"
    echo "want: $want"
    echo "got:  $got"
    exit 1
fi
