// The JavaScript side of F++'s `Js` module — the import object for module
// "js". One function per operation, kept MONOMORPHIC so engine inline
// caches stay warm. Property keys arrive as (ptr, len) UTF-8 in the
// module's exported linear memory; objects cross as externref (no handle
// table, no copies); TypedArray views alias wasm memory directly.
//
// Usage:
//   import { jsImports, wasiImports } from '/stdlib/fpp-js.mjs';
//   let exports;
//   const { instance } = await WebAssembly.instantiateStreaming(
//     fetch('prog.wasm'),
//     { ...jsImports(() => exports), ...wasiImports(() => exports, console.log) });
//   exports = instance.exports;
//   exports._start();

export const jsImports = (getExports) => {
  const dec = new TextDecoder();
  const enc = new TextEncoder();
  const mem = () => getExports().memory.buffer;
  const key = (p, n) => dec.decode(new Uint8Array(mem(), p, n));
  let pending = null; // bytes measured by strLen, written by the next strWrite
  return { js: {
    global: (p, n) => globalThis[key(p, n)],
    get: (o, p, n) => o[key(p, n)],
    set: (o, p, n, v) => { o[key(p, n)] = v; },
    getNum: (o, p, n) => Number(o[key(p, n)]),
    setNum: (o, p, n, v) => { o[key(p, n)] = v; },
    item: (o, i) => o[i],
    itemSet: (o, i, v) => { o[i] = v; },
    call0: (o, p, n) => o[key(p, n)](),
    call1: (o, p, n, a) => o[key(p, n)](a),
    call2: (o, p, n, a, b) => o[key(p, n)](a, b),
    call3: (o, p, n, a, b, c) => o[key(p, n)](a, b, c),
    new0: (C) => new C(),
    new1: (C, a) => new C(a),
    new2: (C, a, b) => new C(a, b),
    num: (v) => v,
    toNum: (v) => Number(v),
    toBool: (v) => (v ? 1 : 0),
    // an F++ closure as a JS function: calls back through the exported
    // bridge; captured state lives in the closure, the GCs keep it alive
    mkFn: (clo) => (...a) => getExports().jscall(clo, a.length ? a[0] : undefined),
    strNew: (p, n) => dec.decode(new Uint8Array(mem(), p, n)),
    strLen: (s) => { pending = enc.encode(String(s)); return pending.length; },
    strWrite: (s, p) => {
      const b = pending !== null ? pending : enc.encode(String(s));
      pending = null;
      new Uint8Array(mem(), p, b.length).set(b);
      return b.length;
    },
    // ZERO-COPY: views over the module's own memory at a pinned address.
    // Fresh per call — memory.grow would detach a cached one.
    viewU8:  (p, n) => new Uint8Array(mem(), p, n),
    viewU16: (p, n) => new Uint16Array(mem(), p, n),
    viewI32: (p, n) => new Int32Array(mem(), p, n),
    viewF32: (p, n) => new Float32Array(mem(), p, n),
    viewF64: (p, n) => new Float64Array(mem(), p, n),
  } };
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
