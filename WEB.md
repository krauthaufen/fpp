# F++ in the browser

```
fpp new site        # a project that builds to a page and runs
cd site
fpp dev             # build, serve, watch, reload — http://localhost:8080
fpp bundle          # dist/, for any static host
```

That is the whole workflow. What follows is what each part does and why it
is shaped the way it is.

## What a project is

```
site/
  app.fppproj       name / out / src — the ordinary project file
  src/Main.fpp      your code
  web/index.html    the page
  web/main.js       the GLUE: it owns the DOM, F++ owns the logic
  web/fpp-js.mjs    the loader, copied in by dev/bundle
```

There is no configuration file and no plugin system. A web project is a
project whose `out` points into `web/`, and everything else is a convention
you can change.

## The two directions across the boundary

**JS → F++** is an export:

```fsharp
[<Export>]
let onClick () : int = ...
```

Without `[<Export>]` a top-level function is not in the module's exports, and
the page gets `mod.onClick is not a function` — *after* the module has
already run, which reads like a runtime bug rather than a missing attribute.

**F++ → JS** is a typed extern:

```fsharp
[<JsImport>]
extern let setText : string -> string -> int
```

`[<JsImport>]` is what makes it a JavaScript import (module `jsxl`, with the
argument kinds mangled into the name). Without it the extern is the plain C
one (module `env`, raw ABI) and the browser refuses to instantiate the module
at all: *"env: module is not an object or function"*.

The page supplies it by name:

```js
const mod = await instantiateLinear("./app.wasm", {
  sink: s => console.log(s),                 // where printfn goes
  jsx: { setText: (id, text) => { ...; return 0; } },
});
mod._start();                                // runs Main.fpp's top level
```

An extern always answers something — return `0` when there is nothing to say.

## npm

```
fpp npm install ms          # npm, run in the project directory
```

An npm package is consumed from **the glue**, not from F++:

```js
import ms from "ms";
jsx: { setDuration: (id, v) => { el.textContent = ms(v, {long:true}); return 0; } }
```

and F++ declares `[<JsImport>] extern let setDuration : string -> int -> int`.
Nothing in the compiler knows npm exists, which is the point — the boundary
that already worked is the one npm arrives through.

**No npm packages means no Node.** Browsers resolve ES modules natively, so
`bundle` is a copy and `dev` serves files. Node enters only when you import a
bare specifier, which a browser cannot resolve: then `bundle` runs `esbuild`
to flatten `main.js`, and says so if it is missing.

## `fpp dev`

Builds once, serves `web/`, watches `src/` and `web/`, rebuilds on change,
and reloads every open page over server-sent events. A failed build is
reported and the old page keeps being served, so a syntax error does not take
the site down while you fix it.

It is a reload, not hot module replacement: a wasm module has no meaningful
partial update, and pretending otherwise would be a lie about what happened.

Note the watcher ignores `.wasm` — the build's own output lands under `web/`
and would otherwise retrigger it forever.

## `fpp bundle`

Writes `dist/`: the wasm, the page, the loader, and `main.js` (flattened if
npm is in play). Everything is relative, so it works from a subdirectory of a
domain as readily as from its root. There is no hashing, minification, or
code splitting — one wasm module and one script is not a dependency graph
that needs managing.

## What this is not

No HMR, no CSS pipeline, no dev-server proxy, no SSR. If a project needs
those it needs a real bundler, and `fpp bundle` output drops into one as a
plain directory.
