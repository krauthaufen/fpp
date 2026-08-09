# Packages

Libraries ship as `.fpkg` archives: not source, not a platform binary, but
the fat IR (`.fppir`) — resolver exports, inference schemes, and generic
templates that specialize at link time — once per target flavor. One
package builds programs for every backend.

## The archive

A zip. Inside:

```
fpkg                    the manifest
mylib-wasm.fppir        the wasm-GC flavor
mylib-native.fppir      the C/fpprt flavor (native and wasm-linear)
```

The manifest is the project-file line format:

```
name mylib
version 1.2.3
requires base ^1.0
lib wasm mylib-wasm.fppir
lib native mylib-native.fppir
```

Two flavors exist because `#if WASM` / `#if NATIVE` resolve when the IR is
built; a library that never uses them still ships both (they are cheap and
usually identical in shape).

## Versions and ranges

Semver 2.0. A dependency range is one of:

```
*              any release
=1.2.3         exactly that version
1.2            caret: >=1.2.0 <2.0.0 — the DEFAULT reading of a bare version
^1.2.3         the same, spelled out (0.x carets wall at the minor)
~1.2.3         >=1.2.3 <1.3.0
>=1.2 <2       a space-separated comparator conjunction
```

Prereleases (`1.0.0-rc.1`) are only ever picked by a range that names a
prerelease of the same triple. A plain `^1.0` never resolves to a beta.

## The registry

A directory, or any static HTTP server over one:

```
<base>/<name>/versions              one version per line
<base>/<name>/<name>-<v>.fpkg       the archives
```

`fpp publish pkg.fpkg <dir>` writes that layout; `fpp publish pkg.fpkg
https://...` PUTs it (any server that accepts PUT — nginx with dav, a
five-line handler — is a registry). A git repository holding the layout is
a registry too: clone it and point at the checkout.

## Using packages

In the project file:

```
name app
registry https://pkg.example.com/fpp
package geolib ^0.3
src main.fpp
```

Then:

```
fpp restore app.fppproj     # solves, downloads to ~/.fpp/pkg, writes fpp.lock
fpp build   app.fppproj     # offline: links the lock's picks, flavor by target
```

The solver picks one version per package name, newest satisfying
everything, backtracking when the greedy choice boxes a later edge in. A
genuine conflict is an error that names the package, every constraint on
it, and who demanded each. The solution is written to `fpp.lock` in
dependency order — check it in; builds use the lock and the cache only,
and refuse (pointing at `restore`) rather than resolving behind your back.

## Publishing your own

```
name mylib
version 1.2.3
package base ^1.0          # dependencies, if any
registry https://...       # where they come from
src lib.fpp
```

```
fpp restore mylib.fppproj                    # if it has dependencies
fpp pack mylib.fppproj -o mylib-1.2.3.fpkg   # builds BOTH flavors
fpp publish mylib-1.2.3.fpkg <registry>
```

`pack` records the project's `package` ranges as the package's `requires`,
so what you tested against is what consumers solve against.
