// Compile a .wasm to machine code with the SAME engine configuration the
// launcher uses — a precompiled module only loads into an engine configured
// exactly as the one that produced it.
#include <stdio.h>
#include <stdlib.h>
#include <wasm.h>
#include <wasmtime.h>

static unsigned char *slurp(const char *path, size_t *len) {
  FILE *f = fopen(path, "rb");
  if (!f) { perror(path); exit(1); }
  fseek(f, 0, SEEK_END); *len = ftell(f); fseek(f, 0, SEEK_SET);
  unsigned char *buf = malloc(*len);
  if (fread(buf, 1, *len, f) != *len) { fprintf(stderr, "short read\n"); exit(1); }
  fclose(f);
  return buf;
}

int main(int argc, char **argv) {
  if (argc != 3) { fprintf(stderr, "usage: fppaot <in.wasm> <out.cwasm>\n"); return 2; }
  size_t len = 0;
  unsigned char *wasm = slurp(argv[1], &len);
  wasm_config_t *config = wasm_config_new();
  wasmtime_config_wasm_gc_set(config, true);
  wasmtime_config_wasm_function_references_set(config, true);
  wasmtime_config_wasm_tail_call_set(config, true);
  wasmtime_config_wasm_exceptions_set(config, true);
  wasm_engine_t *engine = wasm_engine_new_with_config(config);
  wasmtime_module_t *module = NULL;
  wasmtime_error_t *err = wasmtime_module_new(engine, wasm, len, &module);
  if (err) { wasm_byte_vec_t m; wasmtime_error_message(err, &m); fprintf(stderr, "compile: %.*s\n", (int) m.size, m.data); return 1; }
  wasm_byte_vec_t out;
  err = wasmtime_module_serialize(module, &out);
  if (err) { wasm_byte_vec_t m; wasmtime_error_message(err, &m); fprintf(stderr, "serialize: %.*s\n", (int) m.size, m.data); return 1; }
  FILE *o = fopen(argv[2], "wb");
  fwrite(out.data, 1, out.size, o);
  fclose(o);
  fprintf(stderr, "precompiled %zu -> %zu bytes\n", len, out.size);
  return 0;
}
