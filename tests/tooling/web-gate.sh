#!/usr/bin/env bash
# The BROWSER workflow, end to end without a browser: scaffold a project,
# bundle it, and check that what comes out is what a page needs.
#
# The three things asserted are the three that actually broke while this was
# written, each of which produced a page that loaded and then did nothing:
#
#   * the extern must land in module "jsxl", not "env". Without
#     [<JsImport>] it is the C ABI and the browser refuses to instantiate:
#     "env: module is not an object or function".
#   * the entry point must be EXPORTED. A top-level function is not, so the
#     page got "mod.onClick is not a function" — after the module had
#     already run, which makes it look like a runtime bug rather than a
#     missing attribute.
#   * fpp-js.mjs must be COPIED into the output. A static host cannot reach
#     into the compiler's install directory.
#
# A real browser run lives outside the gate (it needs a display and a
# server); this is the part that can be checked in two seconds.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
wt="${WASM_TOOLS:-wasm-tools}"

out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
cd "$out"

"$fpp" new site > /dev/null
cd site

# the scaffold must build as it stands — a template that does not compile is
# the worst thing this command could ship
"$fpp" bundle > /dev/null

fail() { echo "FAIL: $1"; exit 1; }

[ -f dist/index.html ]  || fail "no index.html in dist"
[ -f dist/app.wasm ]    || fail "no app.wasm in dist"
[ -f dist/main.js ]     || fail "no main.js in dist"
[ -f dist/fpp-js.mjs ]  || fail "fpp-js.mjs was not copied — a static host cannot find it"

if command -v "$wt" > /dev/null 2>&1; then
    imports=$("$wt" print dist/app.wasm | grep '(import "jsxl"' || true)
    [ -n "$imports" ] || fail "the extern is not a jsxl import — is [<JsImport>] missing from the template?"
    "$wt" print dist/app.wasm | grep -q '(export "onClick"' \
        || fail "onClick is not exported — is [<Export>] missing from the template?"
    "$wt" print dist/app.wasm | grep -q '(export "_start"' \
        || fail "_start is not exported — the page could not run the module's top level"
fi

# and the page has to reference what was emitted
grep -q 'src="./main.js"' dist/index.html || fail "index.html does not load main.js"
grep -q './app.wasm' dist/main.js         || fail "main.js does not load app.wasm"

echo "WEB OK (scaffold builds, bundles, jsxl import + exports present)"
