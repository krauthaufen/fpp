#!/usr/bin/env bash
# Higher-kinded typeclasses: `class Mappable<'f<_>>` with instances at
# list / option / array, constraint-polymorphic functions stamped per
# constructor AND per element. Parity across both backends is the gate.
set -e
here=$(cd "$(dirname "$0")" && pwd)
bash "$here/cback/run.sh" "$here/hkt.fpp"
bash "$here/cback/run.sh" "$here/hktns.fpp"
bash "$here/cback/run.sh" "$here/hktgadt.fpp"
bash "$here/cback/run.sh" "$here/exist.fpp"
bash "$here/cback/run.sh" "$here/clsmem.fpp"
bash "$here/cback/run.sh" "$here/gadtref.fpp"
bash "$here/cback/run.sh" "$here/gadtsub.fpp"
bash "$here/cback/run.sh" "$here/gadtmixed.fpp"
bash "$here/cback/run.sh" "$here/gadtnames.fpp"
bash "$here/cback/run.sh" "$here/natint.fpp"
bash "$here/cback/run.sh" "$here/optrec.fpp"
bash "$here/cback/run.sh" "$here/future.fpp"
bash "$here/cback/run.sh" "$here/memcons.fpp"
bash "$here/cback/run.sh" "$here/usearm.fpp"
bash "$here/cback/run.sh" "$here/samearity.fpp"
bash "$here/cback/run.sh" "$here/genericenum.fpp"
bash "$here/cback/run.sh" "$here/asyncloop.fpp"
