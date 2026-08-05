/* Whippet platform layer for wasm (emscripten standalone / wasi-sdk).
 * Single-threaded, precise-roots builds only: no mmap, no signals, no
 * dl_iterate_phdr. Reservations are plain aligned allocations that are
 * never returned to the system — wasm linear memory only grows anyway.
 */
#define GC_IMPL 1

#include <stdint.h>
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

struct gc_reservation gc_platform_reserve_memory(size_t size,
                                                 size_t alignment) {
  if (alignment < gc_platform_page_size())
    alignment = gc_platform_page_size();
  void *mem = aligned_alloc(alignment, (size + alignment - 1) & ~(alignment - 1));
  GC_ASSERT(mem);
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
