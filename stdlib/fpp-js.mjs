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
  // wasm-GC objects are JS-observable, so the registry watches THEM.
  // A plain ARRAY, not a Map: ids are sequential ints and the VM resolves
  // one per decoded command — array indexing beats a hashed Map.get
  const table = [];
  let nextId = 1;
  const registry = new FinalizationRegistry(id => { table[id] = undefined; });
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
    h: (id) => table[id],
    reg: (o) => { const id = nextId++; table[id] = o; return id; },
    watch: (wrapper, id) => registry.register(wrapper, id),
    // ZERO-COPY: views over the module's own memory at a pinned address.
    // Fresh per call — memory.grow would detach a cached one.
    viewU8:  (p, n) => new Uint8Array(mem(), p, n),
    viewU16: (p, n) => new Uint16Array(mem(), p, n),
    viewI32: (p, n) => new Int32Array(mem(), p, n),
    viewF32: (p, n) => new Float32Array(mem(), p, n),
    viewF64: (p, n) => new Float64Array(mem(), p, n),
  },
  // for VM plugins (generated decoder modules): the SAME handle table and
  // memory the js primitives use — a decoded command must resolve handles
  // exactly as Js.handle does
  internals: {
    mem,
    h: (id) => table[id],
    reg: (o) => { const id = nextId++; table[id] = o; return id; },
    watch: (wrapper, id) => registry.register(wrapper, id),
  } };
};

// The wasm-LINEAR boundary (module "jslin"): every JsObj is a raw i32 HANDLE
// into a strong table (0 = null; linear memory cannot hold externref), ints
// and bools cross raw, floats as f64, and a string crosses as its linear
// POINTER — length at p+4, utf-16 code units at p+8. JS-made strings enter
// through the module's exported `lin_salloc`. Handles are never reclaimed
// (no finalizers on linear yet) — fine for pages, a known leak for
// long-running apps.
export const jsLinImports = (getExports) => {
  const mem = () => getExports().memory.buffer;
  const table = [null];
  let nextId = 1;
  const reg = (v) => (v === null ? 0 : ((table[nextId] = v), nextId++));
  const h = (id) => table[id];
  const dec = new TextDecoder('utf-16le');
  const lstr = (p) => {
    const dv = new DataView(mem());
    const n = dv.getUint32(p + 4, true);
    return dec.decode(new Uint8Array(mem(), p + 8, n * 2));
  };
  const sout = (s) => {
    const ex = getExports();
    const p = ex.lin_salloc(s.length);
    const u16 = new Uint16Array(ex.memory.buffer, p + 8, s.length);
    for (let i = 0; i < s.length; i++) u16[i] = s.charCodeAt(i);
    return p;
  };
  // gc (reactor) modules: free the table entries of wrappers a collection
  // proved dead (Js.watch queues their handle ids under kind 0). Called
  // after every callback dispatch; standalone modules have no drain export
  // and skip. This is what makes the handle table leak-free under gc.
  const drainDead = () => {
    const ex = getExports();
    if (!ex.fpprt_drain1) return;
    for (let id; (id = ex.fpprt_drain1(0)) !== 0;) table[id] = undefined;
  };
  return { internals: { mem, h, reg, lstr, sout, drainDead },
    jslin: {
      global: (k) => reg(globalThis[lstr(k)]),
      get: (o, k) => reg(h(o)[lstr(k)]),
      set: (o, k, v) => { h(o)[lstr(k)] = h(v); },
      getNum: (o, k) => Number(h(o)[lstr(k)]),
      setNum: (o, k, v) => { h(o)[lstr(k)] = v; },
      item: (o, i) => reg(h(o)[i]),
      itemSet: (o, i, v) => { h(o)[i] = h(v); },
      call0: (o, k) => reg(h(o)[lstr(k)]()),
      call1: (o, k, a) => reg(h(o)[lstr(k)](h(a))),
      call2: (o, k, a, b) => reg(h(o)[lstr(k)](h(a), h(b))),
      call3: (o, k, a, b, c) => reg(h(o)[lstr(k)](h(a), h(b), h(c))),
      call4: (o, k, a, b, c, d) => reg(h(o)[lstr(k)](h(a), h(b), h(c), h(d))),
      call5: (o, k, a, b, c, d, e) => reg(h(o)[lstr(k)](h(a), h(b), h(c), h(d), h(e))),
      call6: (o, k, a0, a1, a2, a3, a4, a5) => reg(h(o)[lstr(k)](h(a0), h(a1), h(a2), h(a3), h(a4), h(a5))),
      call7: (o, k, a0, a1, a2, a3, a4, a5, a6) => reg(h(o)[lstr(k)](h(a0), h(a1), h(a2), h(a3), h(a4), h(a5), h(a6))),
      call8: (o, k, a0, a1, a2, a3, a4, a5, a6, a7) => reg(h(o)[lstr(k)](h(a0), h(a1), h(a2), h(a3), h(a4), h(a5), h(a6), h(a7))),
      call9: (o, k, a0, a1, a2, a3, a4, a5, a6, a7, a8) => reg(h(o)[lstr(k)](h(a0), h(a1), h(a2), h(a3), h(a4), h(a5), h(a6), h(a7), h(a8))),
      call10: (o, k, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9) => reg(h(o)[lstr(k)](h(a0), h(a1), h(a2), h(a3), h(a4), h(a5), h(a6), h(a7), h(a8), h(a9))),
      call11: (o, k, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) => reg(h(o)[lstr(k)](h(a0), h(a1), h(a2), h(a3), h(a4), h(a5), h(a6), h(a7), h(a8), h(a9), h(a10))),
      call12: (o, k, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11) => reg(h(o)[lstr(k)](h(a0), h(a1), h(a2), h(a3), h(a4), h(a5), h(a6), h(a7), h(a8), h(a9), h(a10), h(a11))),
      new0: (C) => reg(new (h(C))()),
      new1: (C, a) => reg(new (h(C))(h(a))),
      new2: (C, a, b) => reg(new (h(C))(h(a), h(b))),
      num: (v) => reg(v),
      toNum: (v) => Number(h(v)),
      bool: (v) => reg(!!v),
      toBool: (v) => (h(v) ? 1 : 0),
      str: (p) => reg(lstr(p)),
      toStr: (v) => sout(String(h(v))),
      // an F++ closure as a JS function: the token is a SLOT the wasm side
      // keeps current across collections; call back through exported jscall
      mkFn: (slot) => reg((...a) => {
        const r = getExports().jscall(slot, reg(a.length ? a[0] : undefined));
        drainDead();
        return r;
      }),
      undef: () => reg(undefined),
      obj: () => reg({}),
      arr: () => reg([]),
      push: (a, v) => { h(a).push(h(v)); },
      // ZERO-COPY views over linear memory at a pinned address; fresh per
      // call — memory.grow would detach a cached one
      viewU8:  (p, n) => reg(new Uint8Array(mem(), p, n)),
      viewU16: (p, n) => reg(new Uint16Array(mem(), p, n)),
      viewI32: (p, n) => reg(new Int32Array(mem(), p, n)),
      viewF32: (p, n) => reg(new Float32Array(mem(), p, n)),
      viewF64: (p, n) => reg(new Float64Array(mem(), p, n)),
    } };
};

// [<JsImport>] under linear: the import NAME carries the kind signature
// ("mix#di:d"), so a Proxy can wrap the user's plain { jsx: { name: fn } }
// function with the per-kind conversions (e=handle s=string d=f64 b=bool
// i=int u=unit-dropped).
const jsxlProxy = (jsx, internals) => new Proxy({}, {
  get: (_, prop) => {
    const [name, sig] = String(prop).split('#');
    const [ps, r] = sig.split(':');
    const fn = jsx[name];
    return (...raw) => {
      const args = [];
      let i = 0;
      for (const k of ps) {
        if (k === 'u') continue;
        const v = raw[i++];
        args.push(k === 'e' ? internals.h(v) : k === 's' ? internals.lstr(v) : k === 'b' ? !!v : v);
      }
      const res = fn(...args);
      return r === 'u' ? undefined
           : r === 'e' ? internals.reg(res)
           : r === 's' ? internals.sout(String(res))
           : r === 'b' ? (res ? 1 : 0)
           : Number(res);
    };
  }
});

/// Instantiate a `fpp build --linear` module with the linear boundary wired:
/// the "jslin" primitives, "jsxl" typed imports from { jsx: { name: fn } },
/// VM plugins as { vms: [gpuVm] } (each contributes jsx entries, sharing the
/// SAME handle table and memory), and wasi print into `sink`.
export const instantiateLinear = async (url, { jsx = {}, sink = null, vms = [] } = {}) => {
  let exports;
  const { jslin, internals } = jsLinImports(() => exports);
  const jsxAll = { ...jsx };
  for (const mk of vms) Object.assign(jsxAll, mk(internals));
  const wasi = wasiImports(() => exports, sink).wasi_snapshot_preview1;
  // the linear module always declares the file-read WASI imports (the
  // self-host path); a browser host answers "no such file"
  const wasiAll = { ...wasi, path_open: () => 44, fd_read: () => 8, fd_filestat_get: () => 8 };
  const { instance } = await WebAssembly.instantiateStreaming(
    fetch(url),
    { jslin, jsxl: jsxlProxy(jsxAll, internals), wasi_snapshot_preview1: wasiAll });
  exports = instance.exports;
  return exports;
};

/// Instantiate an F++ module with the whole boundary wired: the "js"
/// primitives, the engine string builtins, wasi print into `sink`, any
/// app-supplied typed imports as { jsx: { name: fn } }, and any generated
/// VM plugins as { vms: [gpuVm] } — each is called with the internals and
/// contributes its jsx entries.
export const instantiate = async (url, { jsx = {}, sink = null, vms = [] } = {}) => {
  let exports;
  const { js, internals } = jsImports(() => exports);
  const jsxAll = { ...jsx };
  for (const mk of vms) Object.assign(jsxAll, mk(internals));
  const { instance } = await WebAssembly.instantiateStreaming(
    fetch(url),
    { js, ...wasiImports(() => exports, sink), jsx: jsxAll },
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
    clock_time_get: (id, prec, ptr) => {
      const v = new DataView(getExports().memory.buffer);
      v.setBigUint64(ptr, BigInt(Math.round(performance.now() * 1e6)), true);
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
