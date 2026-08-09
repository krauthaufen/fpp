// The JavaScript side of F++'s `Js` module — the import object for module
// "js". One function per operation, kept MONOMORPHIC so engine inline
// caches stay warm. Property keys arrive as (ptr, len) UTF-8 in the
// module's exported linear memory ONLY when dynamic — literal keys are
// interned wasm-side as externref globals and arrive as ready JS strings;
// objects cross as externref (no handle table, no copies); TypedArray
// views alias wasm memory directly.
//
// Usage:
//   import { instantiate } from '/stdlib/fpp-js.mjs';
//   const exports = await instantiate('prog.wasm', { sink: console.log,
//     jsx: { now: () => performance.now() } });   // [<JsImport>] externs
//   exports._start();

export const jsImports = (getExports) => {
  const mem = () => getExports().memory.buffer;
  // the handle table: STRONG refs, freed when the WASM wrapper dies —
  // wasm-GC objects are JS-observable, so the registry watches THEM
  const table = new Map();
  let nextId = 1;
  const registry = new FinalizationRegistry(id => table.delete(id));
  return { js: {
    // keys arrive as JS STRINGS — literals are interned wasm-side, made
    // once through strNew; nothing decodes per call
    global: (k) => globalThis[k],
    get: (o, k) => o[k],
    set: (o, k, v) => { o[k] = v; },
    getNum: (o, k) => Number(o[k]),
    setNum: (o, k, v) => { o[k] = v; },
    item: (o, i) => o[i],
    itemSet: (o, i, v) => { o[i] = v; },
    call0: (o, k) => o[k](),
    call1: (o, k, a) => o[k](a),
    call2: (o, k, a, b) => o[k](a, b),
    call3: (o, k, a, b, c) => o[k](a, b, c),
    call4: (o, k, a, b, c, d) => o[k](a, b, c, d),
    call5: (o, k, a, b, c, d, e) => o[k](a, b, c, d, e),
    call6: (o, k, a, b, c, d, e, f) => o[k](a, b, c, d, e, f),
    call7: (o, k, a, b, c, d, e, f, g) => o[k](a, b, c, d, e, f, g),
    call8: (o, k, a0, a1, a2, a3, a4, a5, a6, a7) => o[k](a0, a1, a2, a3, a4, a5, a6, a7),
    call9: (o, k, a0, a1, a2, a3, a4, a5, a6, a7, a8) => o[k](a0, a1, a2, a3, a4, a5, a6, a7, a8),
    call10: (o, k, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9) => o[k](a0, a1, a2, a3, a4, a5, a6, a7, a8, a9),
    call11: (o, k, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) => o[k](a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10),
    call12: (o, k, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11) => o[k](a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11),
    new0: (C) => new C(),
    new1: (C, a) => new C(a),
    new2: (C, a, b) => new C(a, b),
    num: (v) => v,
    toNum: (v) => Number(v),
    toBool: (v) => (v ? 1 : 0),
    bool: (v) => !!v,
    undef: () => undefined,
    // an F++ closure as a JS function: calls back through the exported
    // bridge; captured state lives in the closure, the GCs keep it alive
    mkFn: (clo) => (...a) => getExports().jscall(clo, a.length ? a[0] : undefined),
    obj: () => ({}),
    arr: () => ([]),
    push: (a, v) => { a.push(v); },
    h: (id) => table.get(id),
    reg: (o) => { const id = nextId++; table.set(id, o); return id; },
    watch: (wrapper, id) => registry.register(wrapper, id),
    // ZERO-COPY: views over the module's own memory at a pinned address.
    // Fresh per call — memory.grow would detach a cached one.
    viewU8:  (p, n) => new Uint8Array(mem(), p, n),
    viewU16: (p, n) => new Uint16Array(mem(), p, n),
    viewI32: (p, n) => new Int32Array(mem(), p, n),
    viewF32: (p, n) => new Float32Array(mem(), p, n),
    viewF64: (p, n) => new Float64Array(mem(), p, n),
  } };
};

/// Instantiate an F++ module with the whole boundary wired: the "js"
/// primitives, the engine string builtins, wasi print into `sink`, and any
/// app-supplied typed imports as { jsx: { name: fn } }.
export const instantiate = async (url, { jsx = {}, sink = null } = {}) => {
  let exports;
  const { instance } = await WebAssembly.instantiateStreaming(
    fetch(url),
    { ...jsImports(() => exports), ...wasiImports(() => exports, sink), jsx },
    { builtins: ['js-string'] });
  exports = instance.exports;
  return exports;
};

// `print` lowers to wasi fd_write; drain the iovecs into `sink`
export const wasiImports = (getExports, sink) => ({
  wasi_snapshot_preview1: {
    fd_write: (fd, iovs, n, written) => {
      const view = new DataView(getExports().memory.buffer);
      let total = 0;
      for (let i = 0; i < n; i++) {
        const ptr = view.getUint32(iovs + i * 8, true);
        const len = view.getUint32(iovs + i * 8 + 4, true);
        total += len;
        if (sink) sink(dec2().decode(new Uint8Array(getExports().memory.buffer, ptr, len)));
      }
      view.setUint32(written, total, true);
      return 0;
    },
    fd_close: () => 0,
    fd_seek: () => 0,
    proc_exit: () => {},
    environ_get: () => 0,
    environ_sizes_get: (a, b) => {
      const v = new DataView(getExports().memory.buffer);
      v.setUint32(a, 0, true); v.setUint32(b, 0, true);
      return 0;
    },
  },
});
const dec2 = (() => { let d = null; return () => (d ??= new TextDecoder()); })();
