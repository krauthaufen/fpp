#!/usr/bin/env bash
# NEGATIVE conformance gate: programs F# REJECTS must be rejected by F++
# too — at the right line, with a diagnostic worth reading, and without
# crashing the compiler.
#
# Each neg/<name>.fpp is an ILLEGAL program in the common F#/F++ subset.
# Expectations live in the file itself, one per line:
#
#   //! 12 expected to have type
#
# meaning: some F++ diagnostic must point at line 12 AND contain that
# substring. (The fsc message texts cannot be the oracle — different
# compiler, different wording — so each case asserts OUR diagnostic
# directly; see DIVERGENCES.md on why diff-based oracles cannot arbitrate
# this.) What MAKES a case a conformance case is the other side:
# `./neg.sh --oracle` runs every file under `dotnet fsi` and demands a
# nonzero exit, proving real F# rejects the program too.
#
#   ./neg.sh              # gate every case
#   ./neg.sh <name>       # gate one case
#   ./neg.sh --oracle     # verify fsi rejects every case (slow, hermetic-ish)
set -u
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
fpp="${FPP:-$root/src/Fpp.Cli/bin/Release/net10.0/fpp}"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT

oracle=0
if [ "${1:-}" = "--oracle" ]; then oracle=1; shift; fi
only="${1:-}"

pass=0; fail=0
for f in "$here"/neg/*.fpp; do
  b=$(basename "$f" .fpp)
  [ -n "$only" ] && [ "$b" != "$only" ] && continue

  if [ "$oracle" = 1 ]; then
    # a DIVERGENCE case: F# accepts the program (usually with a warning),
    # F++ rejects it on purpose — DIVERGENCES.md carries the reason
    if grep -q '^//? fsc-accepts' "$f"; then
      echo "ORACLE-SKIP    $b (chosen divergence: fsc accepts)"
      pass=$((pass+1))
      continue
    fi
    # the fsi copy drops the module header, as the positive runner does
    sed '0,/^module /{/^module /d}' "$f" > "$out/$b.fsx"
    if timeout 120 dotnet fsi "$out/$b.fsx" >/dev/null 2>"$out/$b.fsierr" </dev/null; then
      echo "ORACLE-ACCEPTS $b (fsi compiled and ran an illegal program?)"
      fail=$((fail+1))
    else
      echo "ORACLE-REJECTS $b"
      pass=$((pass+1))
    fi
    continue
  fi

  "$fpp" build --gc -o "$out/$b.wasm" "$f" >"$out/$b.log" 2>&1
  rc=$?
  if [ "$rc" = 0 ]; then
    echo "ACCEPTED $b (must be rejected)"; fail=$((fail+1)); continue
  fi
  # a crash (unhandled exception) is not a diagnostic
  if grep -qE "Unhandled exception|at Fpp\." "$out/$b.log"; then
    echo "CRASH   $b"; sed -n '1,4p' "$out/$b.log"; fail=$((fail+1)); continue
  fi
  ok=1
  while IFS= read -r exp; do
    line=${exp%% *}
    sub=${exp#* }
    if ! grep -E "^error: [^:]*:$line:[0-9]+: " "$out/$b.log" | grep -qF "$sub"; then
      if [ "$ok" = 1 ]; then echo "MISS    $b"; fi
      echo "        wanted line $line containing: $sub"
      ok=0
    fi
  done < <(grep -oP '^//! \K.*' "$f")
  if [ "$ok" = 1 ]; then
    echo "OK      $b"
    pass=$((pass+1))
  else
    sed -n '1,6p' "$out/$b.log" | sed 's/^/        got: /'
    fail=$((fail+1))
  fi
done
echo "NEG: $pass ok, $fail failed"
[ "$fail" = 0 ]
