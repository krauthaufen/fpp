#!/bin/sh
# Build the browser demo: F++ -> wat -> wasm. Serve this directory and open.
set -e
cd "$(dirname "$0")"
dotnet run --project ../src/Fpp.Cli -- build -o demo.wasm demo.fpp
# gpu.html instantiates by hand with no runtime module, so the standalone
# (bump-allocator) linear build is the right shape for it
dotnet run --project ../src/Fpp.Cli -- build --linear -o gpu.wasm gpu.fpp
echo "demo.wasm built — serve the REPO ROOT (the page imports ../stdlib/fpp-js.mjs):"
echo "  cd .. && python3 -m http.server 8123   # then open /demo/index.html"
