// A standalone launcher: the F++ module is compiled in, wasmtime is linked in,
// and the result is an ordinary executable with nothing to install.
#include <stdio.h>
#include <stdlib.h>
#include <wasm.h>
#include <wasi.h>
#include <wasmtime.h>

extern const unsigned char FPP_MODULE[];
extern const unsigned int FPP_MODULE_LEN;

static void die(const char *what, wasmtime_error_t *err, wasm_trap_t *trap) {
  fprintf(stderr, "%s", what);
  wasm_byte_vec_t msg;
  if (err) { wasmtime_error_message(err, &msg); wasmtime_error_delete(err); }
  else if (trap) { wasm_trap_message(trap, &msg); wasm_trap_delete(trap); }
  else { fprintf(stderr, "\n"); exit(1); }
  fprintf(stderr, ": %.*s\n", (int) msg.size, msg.data);
  wasm_byte_vec_delete(&msg);
  exit(1);
}

int main(int argc, char **argv) {
  wasm_config_t *config = wasm_config_new();
  // what F++ modules need: GC, and tail calls for its tail-recursive code
  wasmtime_config_wasm_gc_set(config, true);
  wasmtime_config_wasm_function_references_set(config, true);
  wasmtime_config_wasm_tail_call_set(config, true);
  wasmtime_config_wasm_exceptions_set(config, true);
  wasm_engine_t *engine = wasm_engine_new_with_config(config);
  wasmtime_store_t *store = wasmtime_store_new(engine, NULL, NULL);
  wasmtime_context_t *ctx = wasmtime_store_context(store);

  wasi_config_t *wasi = wasi_config_new();
  wasi_config_inherit_argv(wasi);
  wasi_config_inherit_env(wasi);
  wasi_config_inherit_stdin(wasi);
  wasi_config_inherit_stdout(wasi);
  wasi_config_inherit_stderr(wasi);
  wasmtime_error_t *err = wasmtime_context_set_wasi(ctx, wasi);
  if (err) die("wasi", err, NULL);

  wasmtime_module_t *module = NULL;
#ifdef FPP_PRECOMPILED
  // the module was compiled to machine code at BUILD time: nothing to compile
  // when the program starts
  err = wasmtime_module_deserialize(engine, FPP_MODULE, FPP_MODULE_LEN, &module);
  if (err) die("loading the precompiled module", err, NULL);
#else
  err = wasmtime_module_new(engine, FPP_MODULE, FPP_MODULE_LEN, &module);
  if (err) die("compiling the embedded module", err, NULL);
#endif

  wasmtime_linker_t *linker = wasmtime_linker_new(engine);
  err = wasmtime_linker_define_wasi(linker);
  if (err) die("defining wasi", err, NULL);
  err = wasmtime_linker_module(linker, ctx, "", 0, module);
  if (err) die("linking", err, NULL);

  wasmtime_func_t start;
  err = wasmtime_linker_get_default(linker, ctx, "", 0, &start);
  if (err) die("finding the entry point", err, NULL);
  wasm_trap_t *trap = NULL;
  err = wasmtime_func_call(ctx, &start, NULL, 0, NULL, 0, &trap);
  if (err || trap) die("running", err, trap);

  wasmtime_module_delete(module);
  wasmtime_store_delete(store);
  wasm_engine_delete(engine);
  return 0;
}
