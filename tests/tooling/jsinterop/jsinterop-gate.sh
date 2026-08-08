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
"$fpp" build -o "$here/domdemo.wasm" "$root/stdlib/dom.fpp" "$here/domdemo.fpp"
"$fpp" build --strict -o "$here/gpu-triangle.wasm" "$root/stdlib/dom.fpp" "$root/stdlib/webgpu.fpp" "$here/gpu-triangle.fpp"
cd "$root"
python3 -m http.server 8734 >/dev/null 2>&1 &
srv=$!
trap 'kill $srv 2>/dev/null || true' EXIT
sleep 1
got=$(node "$here/drive.js")
want='{"log":["7","","made","","café €","","1","9","7","0","","4","0","7","","ready",""],"madeText":"hello from F++","viewY1":4.5,"clicks":2,"x0AfterJsWrite":95}'
if [ "$got" = "$want" ]; then
    echo "JS INTEROP OK (dom, callbacks, strings, zero-copy views)"
else
    echo "JS INTEROP MISMATCH"
    echo "want: $want"
    echo "got:  $got"
    exit 1
fi
# the typed-DOM leg: the curated hierarchy, properties, optionals, and
# DYNAMIC-type wrapping (`:? HTMLCanvasElement` / `:? MouseEvent` answer
# what the browser knows)
got=$(node "$here/domdrive.js")
want='{"log":["typed","hello typed café","t€xt","5","123px","BUTTON","hello typed café","big","BUTTON","4","canvas 32","span SPAN","dom-ready"],"text":"hello typed café","cls":"big","width":"123px","clicks":2,"lastX":77}'
if [ "$got" = "$want" ]; then
    echo "DOM OK (typed hierarchy, dynamic type tests, optionals)"
else
    echo "DOM MISMATCH"
    echo "want: $want"
    echo "got:  $got"
    exit 1
fi
# the WebGPU leg: the hello-triangle sample as F++ — generated bindings,
# record descriptors, future{} async, GPU readback asserting the pixels.
# Skips cleanly where navigator.gpu is absent.
got=$(node "$here/gpudrive.js")
case "$got" in
  *'"skip":true'*) echo "WEBGPU-TRIANGLE SKIPPED (no navigator.gpu)" ;;
  *'"ok":1'*) echo "WEBGPU OK (hello-triangle renders, readback verified)" ;;
  *) echo "WEBGPU MISMATCH"; echo "got: $got"; exit 1 ;;
esac
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
