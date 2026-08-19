# JS interop on wasm-linear

The arc after the linear fixpoint: make the WHOLE browser-interop surface —
the generic `Js.*` primitives, `[<JsImport>]`/jsx typed externs, `[<Export>]`,
callbacks, zero-copy TypedArray views, and the dom/webgl/webgpu stdlib layers
riding on them — work on the wasm-LINEAR backend, so the wasm-GC backend can
eventually be dropped wholesale. The jsinterop gate's six legs are the
acceptance bar: each must pass built `--linear` exactly as it passes on GC.

## The linear boundary ABI (module "jslin")

Representations at the import/export boundary — all raw, no shifts:

| F++ type    | crosses as | notes |
|-------------|-----------|-------|
| `JsObj`     | i32 handle id | JS-side strong table; 0 = null. `rawScalarName` lists JsObj, so handles are raw scalars everywhere (never scanned, never rooted). |
| `int`/`bool`/`char` | raw i32 | ints lower raw in registers already |
| `float`     | f64       | `flatUnbox F64` out, box-via-temp back in |
| `string`    | linear ptr | layout `[hdr:4][len:4][u16 data]`; glue reads len at p+4, decodes utf-16le at p+8. JS→wasm strings: glue calls exported `lin_salloc(units)` then writes u16 data. |
| `nativeint` | raw i32 address | pin answers the element-data address |

- **Handles**: unlike wasm-GC (externref, no table), linear objects cannot hold
  externref, so every JsObj is an id into the glue's handle table (the same
  table the VM plugins already use). `Js.handle`/`Js.register` become identity.
  `Js.watch` is a no-op — no finalizers on linear; handles LEAK (residue:
  explicit free or fpprt finalizer support later).
- **Callbacks**: an F++ closure crosses as a SLOT ADDRESS, not a pointer —
  `$cbreg(clo)` stores the closure into a slot the collector treats as a root
  (standalone: a `$lalloc` word, nothing moves; gc: a static-root slot) and
  JS calls back through exported `jscall(slot, argHandle)` which loads the
  CURRENT closure pointer from the slot and `call_indirect $lclo`s it.
- **jsx typed externs**: imported from module "jsxl" with the kind signature
  MANGLED into the import name (`name#eds:d` — param kinds, ':', return kind;
  kinds as in BinDriver: e=JsObj s=string d=float b=bool i=int u=unit). The
  glue exposes module "jsxl" as a Proxy that parses the name and wraps the
  user's plain `jsx: { name: fn }` function with the per-kind conversions.
- **Views**: `Js.viewF32 (Array.pin a) n` — standalone: pin = data address
  (`a+8`), nothing moves, the view aliases the real storage. GC mode: fpprt
  pinning needs the mmc collector (`fpprt_pin`; semi-space aborts) — M3.

## Milestones

- **M1 — generic primitives, standalone `--linear`** — DONE: all `Js.*`
  EUnknown arms, `mem*` arms, `EArrayPin/Unpin/Bytes`, `[<Export>]`,
  `$cbreg`+`jscall`, `lin_salloc`, glue `jsLinImports`/`instantiateLinear`,
  plain `extern let` env imports; jsdemo leg green in headed Chrome.
- **M2 — typed layers** — DONE: jsxl mangled imports (+ VM plugins via
  `vms:`), all six gate legs green on `--linear` (jsdemo, typed DOM, webgl,
  webgl-typed, gpu-triangle incl. future{} async, gpu-compute). The -lin
  legs are wired into jsinterop-gate.sh with their own want strings (only
  print WRITE CHUNKING differs from GC: linear prints a number in one
  fd_write, the GC printval per digit).
  Compiler bugs this flushed out (all fixed): pattern-only string literals
  interned past $hp and overwritten by the first allocation (scanPatConsts);
  enums lowered as union OBJECTS (EnumConst: an enum IS its raw int, in
  ctors, patterns and derefPat); `?F : float` optional record fields
  recorded as bare "float" and packed as raw f64 (now "Option$<float>");
  collapsed newtype-struct arrays (`F1[]`, F1 = {V : float32}) stored boxed
  pointers instead of packed scalars (storKindRes — required for zero-copy
  views); `print` of int/float on linear (static-type dispatch via
  printConOf; no runtime $printval exists on linear); shortest-form float
  formatting ($ftoa_s, mirrors GC $ftoa) for `print <float>` and
  `string <float>`; `int#s`/`int#p`/`nativeint#` conversions;
  `memLoadFloat/memStoreFloat`; $lalloc 8-aligns (Mem.alloc promises it).
- **M3 — reactor (gc) mode in the browser**: WASI shims for the merged
  reactor module, js* calls routed through rooted-args (import calls are
  safepoints — a callback can re-enter and collect), pinning via an
  mmc-built reactor (or pin-copies-to-malloc like the GC backend does).
- **M4 — flip**: `fpp build` default → linear; wasm-GC behind a flag for one
  release as cross-check, then delete BinDriver.

## Import set (jslin)

`global(k) s→h`, `get(o,k)`, `set(o,k,h)`, `getNum(o,k)→f64`,
`setNum(o,k,f64)`, `item(o,i)`, `itemSet`, `call0..call12(o,k,h*)`,
`new0..new2(C,h*)`, `num(f64)→h`, `toNum(h)→f64`, `bool(i32)→h`,
`toBool(h)→i32`, `str(p)→h`, `toStr(h)→p` (allocates via `lin_salloc`),
`mkFn(slot)→h`, `undef/obj/arr()→h`, `push(a,h)`, `isNull` wasm-side
(`id==0`), `viewU8/U16/I32/F32/F64(p,n)→h`.

Null: glue maps JS null → id 0 and `h(0)` → null; `undefined` gets a real id
(parity with GC-mode externref, where only null is ref.null).
