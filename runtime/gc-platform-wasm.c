/* Whippet platform layer for wasm (emscripten standalone / wasi-sdk).
 * Single-threaded, precise-roots builds only: no mmap, no signals, no
 * dl_iterate_phdr. Reservations are plain aligned allocations that are
 * never returned to the system — wasm linear memory only grows anyway.
 */
#define GC_IMPL 1

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#include "gc-assert.h"
#include "gc-platform.h"

void gc_platform_init(void) {}

uintptr_t gc_platform_current_thread_stack_base(void) {
  /* conservative stack scanning is not supported on wasm: precise builds
   * never call this with a meaningful expectation */
  int here;
  return (uintptr_t)&here;
}

void gc_platform_visit_global_conservative_roots(void (*f)(uintptr_t start,
                                                           uintptr_t end,
                                                           struct gc_heap *heap,
                                                           void *data),
                                                 struct gc_heap *heap,
                                                 void *data) {
  /* precise builds only */
}

int gc_platform_processor_count(void) { return 1; }

uint64_t gc_platform_monotonic_nanoseconds(void) {
  struct timespec ts;
  if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0)
    return 0;
  return (uint64_t)ts.tv_sec * 1000000000ull + (uint64_t)ts.tv_nsec;
}

size_t gc_platform_page_size(void) {
  /* wasm pages are 64 KiB; the collectors only need a granule */
  return 65536;
}

/* FPPRT_MEM_LOG=1: every reservation, so a heap that grows itself to death is
 * visible as a sequence rather than as a trap somewhere else. */
static int fpprt_mem_log_(void) {
  static int v = -1;
  if (v < 0) { const char *s = getenv("FPPRT_MEM_LOG"); v = (s && *s == '1'); }
  return v;
}

struct gc_reservation gc_platform_reserve_memory(size_t size,
                                                 size_t alignment) {
  if (alignment < gc_platform_page_size())
    alignment = gc_platform_page_size();
  void *mem = aligned_alloc(alignment, (size + alignment - 1) & ~(alignment - 1));
  /* A FAILED reservation must be fatal and LOUD, as it is on the gnu-linux
   * platform (perror + GC_CRASH). It was neither here: NDEBUG compiles
   * GC_ASSERT away, so a null `mem` fell through to the memset below and
   * zeroed linear memory FROM ADDRESS 0 — over the C data segment, function
   * pointers included. The program then died far away, on an indirect call
   * through a zeroed pointer, as `wasm trap: uninitialized element` (table
   * slot 0 is the null funcref). That is what a self-host under a 512 MB
   * heap looked like: no message, no OOM, just a trap in the collector. */
  if (!mem) {
    /* Report a FAILED reservation as an empty one and let the caller decide.
     * A heap that cannot grow should collect more often, not die: the
     * self-hosted compiler holds ~600 MB live, the growable sizer therefore
     * targets live + sqrt(live)*sqrt(threshold/2) ~ 1.2 GB, and asking a
     * 2 GB linear memory for a CONTIGUOUS 570 MB block on top of the heap it
     * already holds simply cannot be served. `large_object_space_alloc`
     * already tests this result for NULL — that is the contract; the callers
     * that did not were the bug (see nofl_space_expand). */
    if (fpprt_mem_log_())
      fprintf(stderr, "[mem reserve %zu KB FAILED]\n", size >> 10);
    return (struct gc_reservation){ 0, 0 };
  }
  if (fpprt_mem_log_())
    fprintf(stderr, "[mem reserve %zu KB -> %p]\n", size >> 10, mem);
  memset(mem, 0, size);
  return (struct gc_reservation){ (uintptr_t)mem, size };
}

void *gc_platform_acquire_memory_from_reservation(struct gc_reservation r,
                                                  size_t offset, size_t size) {
  GC_ASSERT(offset + size <= r.size);
  return (void *)(r.base + offset);
}

void gc_platform_release_reservation(struct gc_reservation r) {
  free((void *)r.base);
}

void *gc_platform_acquire_memory(size_t size, size_t alignment) {
  struct gc_reservation r = gc_platform_reserve_memory(size, alignment);
  return (void *)r.base;
}

void gc_platform_release_memory(void *base, size_t size) {
  /* leaked by design: linear memory never shrinks */
}

int gc_platform_populate_memory(void *addr, size_t size) { return 1; }

int gc_platform_discard_memory(void *addr, size_t size) {
  memset(addr, 0, size);
  return 1;
}
