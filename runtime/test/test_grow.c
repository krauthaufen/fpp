/* The heap must GROW: start at 2 MB, then keep ~48 MB of live cons cells.
 * A fixed-size heap dies here; the growable policy resizes synchronously
 * at collection time, so this passes with no background thread — the
 * configuration wasm runs. */
#include <inttypes.h>
#include <stdio.h>

#include "../fpprt.h"

#define TID_CONS FPPRT_TID_FIRST
static const uint32_t cons_refs[] = { 1 * sizeof(uintptr_t),
                                      2 * sizeof(uintptr_t) };
#define CONS_CDR (2 * sizeof(uintptr_t))
#define CONS_VAL (3 * sizeof(uintptr_t))

int main(void) {
  fpprt_init(&(struct fpprt_opts){ .heap_bytes = 2 * 1024 * 1024 });
  fpprt_register_type(TID_CONS, (struct fpprt_type){
    4 * sizeof(uintptr_t), FPPRT_KIND_STRUCT, 2, cons_refs, "cons" });

  /* 1.5M live cells * 4 words: 48 MB on 64-bit, 24 MB on wasm32 —
   * either way far beyond the 2 MB start */
  size_t n = 1500000;
  FPPRT_FRAME(f, 1);
  for (size_t i = 0; i < n; i++) {
    fpprt_ref c = fpprt_alloc(TID_CONS);
    *(uintptr_t *)((char *)c + CONS_VAL) = i;
    fpprt_write_ref(c, CONS_CDR, f_slots[0]);
    f_slots[0] = c;
  }
  fpprt_collect();
  size_t count = 0;
  uintptr_t sum = 0;
  for (fpprt_ref l = f_slots[0]; l; l = fpprt_read_ref(l, CONS_CDR)) {
    sum += *(uintptr_t *)((char *)l + CONS_VAL);
    count++;
  }
  /* expected sum in the SAME word width, so wasm32 checks exactly too */
  uintptr_t expected = 0;
  for (uintptr_t i = 0; i < (uintptr_t)n; i++) expected += i;
  if (count != n || sum != expected) {
    printf("GROW FAILED: count %zu (want %zu), sum %" PRIuPTR
           " (want %" PRIuPTR ")\n", count, n, sum, expected);
    return 1;
  }
  printf("grow OK (%zu live cells from a 2 MB start)\n", n);
  FPPRT_LEAVE(f);
  return 0;
}
