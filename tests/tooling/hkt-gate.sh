#!/usr/bin/env bash
# Higher-kinded typeclasses: `class Mappable<'f<_>>` with instances at
# list / option / array, constraint-polymorphic functions stamped per
# constructor AND per element. Parity across both backends is the gate.
set -e
here=$(cd "$(dirname "$0")" && pwd)
bash "$here/cback/run.sh" "$here/hkt.fpp"
