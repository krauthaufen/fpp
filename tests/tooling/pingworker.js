self.onmessage = e => {
  const { buf, transfer } = e.data;
  // touch it, so nothing is optimised away
  const v = new Uint8Array(buf);
  v[0] = (v[0] + 1) & 255;
  if (transfer) self.postMessage({ buf }, [buf]);
  else self.postMessage({ buf });
};
