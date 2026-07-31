self.onmessage = async e => {
  const { memory, addr, n, racy } = e.data;
  const { instance } = await WebAssembly.instantiate(
    await (await fetch('worker.wasm')).arrayBuffer(), { env: { mem: memory } });
  const t = performance.now();
  (racy ? instance.exports.hammerRacy : instance.exports.hammer)(addr, n);
  self.postMessage({ ms: performance.now() - t });
};
