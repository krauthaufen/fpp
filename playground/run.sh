#!/usr/bin/env bash
# Build the playground and run it under wasmtime.
set -euo pipefail
cd "$(dirname "$0")/.."

dotnet run --project src/Fpp.Cli -c Release -- build playground/playground.fppproj

if command -v wasmtime >/dev/null 2>&1; then WASMTIME=wasmtime
elif [ -x "$HOME/.wasmtime/bin/wasmtime" ]; then WASMTIME="$HOME/.wasmtime/bin/wasmtime"
else
    echo "wasmtime not found — install it with:" >&2
    echo "  curl https://wasmtime.dev/install.sh -sSf | bash" >&2
    exit 1
fi

exec "$WASMTIME" -W exceptions=y playground/playground.wat
