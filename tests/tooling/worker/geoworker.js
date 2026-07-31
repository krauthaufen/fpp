// The worker side: the SAME module, its own instance, its own heap.
import { wasiImports } from './wasi.js';
let ex = null;
const boot = async () => {
  if (ex) return ex;
  let inst = null;
  const m = await WebAssembly.instantiateStreaming(fetch('geo.wasm'),
    wasiImports(() => inst.exports.memory));
  inst = m.instance;
  inst.exports._start();
  ex = inst.exports;
  return ex;
};
self.onmessage = async e => {
  try {
    const x = await boot();
    const bytes = new Uint8Array(e.data.buf);      // a transferred ArrayBuffer
    const p = x.reserve(bytes.length);             // room in THIS heap
    new Uint8Array(x.memory.buffer, p, bytes.length).set(bytes);
    const rp = x.dispatch(p);                      // decode, handle, encode
    const rn = x.msgLength(rp);
    // copy out, then transfer: the reply leaves as a move, not a copy
    const out = new Uint8Array(rn);
    out.set(new Uint8Array(x.memory.buffer, rp, rn));
    self.postMessage({ buf: out.buffer }, [out.buffer]);
  } catch (err) {
    self.postMessage({ error: String(err) });
  }
};
