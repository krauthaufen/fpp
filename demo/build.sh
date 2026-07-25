#!/bin/sh
# Build the browser demo: F++ -> wat -> wasm. Serve this directory and open.
set -e
cd "$(dirname "$0")"
dotnet run --project ../src/Fpp.Cli -- build -o demo.wat demo.fpp
wasm-tools parse demo.wat -o demo.wasm
echo "demo.wasm built — serve with: python3 -m http.server 8123"
