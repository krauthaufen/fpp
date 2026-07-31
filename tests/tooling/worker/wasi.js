// The module writes through wasi fd_write (that is what `print` lowers to).
// A worker has nowhere to print, so this just drains the iovecs.
export const wasiImports = (getMemory, sink) => ({
  wasi_snapshot_preview1: {
    fd_write: (fd, iovs, n, written) => {
      const mem = getMemory();
      const view = new DataView(mem.buffer);
      let total = 0;
      for (let i = 0; i < n; i++) {
        const ptr = view.getUint32(iovs + i * 8, true);
        const len = view.getUint32(iovs + i * 8 + 4, true);
        total += len;
        if (sink) sink(new TextDecoder().decode(new Uint8Array(mem.buffer, ptr, len)));
      }
      view.setUint32(written, total, true);
      return 0;
    },
    fd_close: () => 0,
    fd_seek: () => 0,
    proc_exit: () => {},
    environ_get: () => 0,
    environ_sizes_get: (a, b) => { const v = new DataView(getMemory().buffer); v.setUint32(a, 0, true); v.setUint32(b, 0, true); return 0; },
  },
});
