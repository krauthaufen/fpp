/* A reservation that CANNOT be served must be reported as an empty one.
 *
 * It used to be reported as a successful reservation of address 0: the
 * aligned_alloc returned NULL, NDEBUG compiled the GC_ASSERT away, and the
 * memset that followed zeroed linear memory from address 0 — over the C data
 * segment, function pointers included. The program then died far from here,
 * on an indirect call through a zeroed pointer, as `wasm trap: uninitialized
 * element` (table slot 0 is the null funcref). The self-hosted compiler hit
 * it whenever its heap tried to grow past what a 2 GB linear memory can hand
 * out in one contiguous block.
 *
 * `large_object_space_alloc` already tests this result for NULL, so an empty
 * reservation is the contract; `nofl_space_expand` did not, and now declines
 * to expand instead of registering NULL slabs. */
#define GC_IMPL 1
#include <stdint.h>
#include <stdio.h>

#include "gc-platform.h"

int main(void) {
  /* 3 GB: past wasm32's 2 GB linear memory, so this cannot be served */
  size_t huge = (size_t)3 * 1024 * 1024 * 1024;
  struct gc_reservation r = gc_platform_reserve_memory(huge, 65536);
  if (r.base != 0 || r.size != 0) {
    printf("RESERVE FAILED: impossible reservation reported base %" PRIuPTR
           " size %zu\n", (uintptr_t)r.base, r.size);
    return 1;
  }
  /* and one that CAN be served still works */
  struct gc_reservation ok = gc_platform_reserve_memory(1024 * 1024, 65536);
  if (ok.base == 0 || ok.size != 1024 * 1024) {
    printf("RESERVE FAILED: a 1 MB reservation was refused\n");
    return 1;
  }
  gc_platform_release_reservation(ok);
  printf("reserve OK (an impossible reservation is empty, a possible one is not)\n");
  return 0;
}
