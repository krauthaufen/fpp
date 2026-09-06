/* Whippet platform layer for wasm (emscripten standalone / wasi-sdk).
 * Single-threaded, precise-roots builds only: no mmap, no signals, no
 * dl_iterate_phdr. Reservations are plain aligned allocations; releasing one
 * returns it to the C allocator so the block can be REUSED (see the registry
 * below — wasm linear memory never shrinks, but that is not a reason to leak
 * inside it).
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

/* ---- the allocation registry --------------------------------------------
 * `gc_platform_release_memory` used to do nothing at all, justified as "linear
 * memory never shrinks". That conflates two things: wasm linear memory indeed
 * never shrinks, but the C allocator INSIDE it can happily reuse a freed
 * block. Never freeing meant every large object and every worklist buffer the
 * collector retired was lost, so allocation marched monotonically up the
 * address space until the 2 GB wall. A self-hosted compile asked for 32 GB
 * across 1099 reservations and died at 0x7ff50000 with "we have the space but
 * mmap didn't work" — an OOM with hundreds of MB free. Which heap sizes
 * survived looked random; it was only ever how much churn fitted below the
 * wall.
 *
 * `free` needs the EXACT pointer `aligned_alloc` returned, and one caller
 * (semi's region shrink) releases the TAIL of a region rather than the whole
 * block. So every acquisition is recorded here and a release frees only on an
 * exact (base, size) match. Anything else is ignored, exactly as before —
 * precise, never a guess at whether a pointer is free-able. */
#define FPPRT_ALLOC_EMPTY 0u
#define FPPRT_ALLOC_TOMB 1u
struct fpprt_alloc_ent { uintptr_t base; size_t size; };
static struct fpprt_alloc_ent *g_allocs;
static size_t g_allocs_cap;   /* power of two */
static size_t g_allocs_live;
static size_t g_allocs_used;  /* live + tombstones */

static size_t fpprt_alloc_hash(uintptr_t base, size_t cap) {
  uintptr_t h = base >> 4;
  h *= 2654435761u;
  return (size_t)(h & (cap - 1));
}

static void fpprt_alloc_insert(struct fpprt_alloc_ent *tab, size_t cap,
                               uintptr_t base, size_t size) {
  size_t i = fpprt_alloc_hash(base, cap);
  while (tab[i].base != FPPRT_ALLOC_EMPTY && tab[i].base != FPPRT_ALLOC_TOMB)
    i = (i + 1) & (cap - 1);
  tab[i].base = base;
  tab[i].size = size;
}

static void fpprt_alloc_grow(void) {
  size_t ncap = g_allocs_cap ? g_allocs_cap * 2 : 256;
  struct fpprt_alloc_ent *ntab =
      (struct fpprt_alloc_ent *)calloc(ncap, sizeof(struct fpprt_alloc_ent));
  /* the registry is an OPTIMISATION: if it cannot grow, stop recording and
   * fall back to the old leak rather than failing the allocation */
  if (!ntab) return;
  for (size_t i = 0; i < g_allocs_cap; i++)
    if (g_allocs[i].base != FPPRT_ALLOC_EMPTY &&
        g_allocs[i].base != FPPRT_ALLOC_TOMB)
      fpprt_alloc_insert(ntab, ncap, g_allocs[i].base, g_allocs[i].size);
  free(g_allocs);
  g_allocs = ntab;
  g_allocs_cap = ncap;
  g_allocs_used = g_allocs_live;
}

static void fpprt_alloc_put(uintptr_t base, size_t size) {
  if (base == FPPRT_ALLOC_EMPTY || base == FPPRT_ALLOC_TOMB) return;
  if ((g_allocs_used + 1) * 10 >= g_allocs_cap * 7) fpprt_alloc_grow();
  if (!g_allocs_cap) return;
  fpprt_alloc_insert(g_allocs, g_allocs_cap, base, size);
  g_allocs_live++;
  g_allocs_used++;
}

/* remove and report whether (base, size) was an exact whole allocation */
static int fpprt_alloc_take(uintptr_t base, size_t size) {
  if (!g_allocs_cap || base == FPPRT_ALLOC_EMPTY || base == FPPRT_ALLOC_TOMB)
    return 0;
  size_t i = fpprt_alloc_hash(base, g_allocs_cap);
  while (g_allocs[i].base != FPPRT_ALLOC_EMPTY) {
    if (g_allocs[i].base == base) {
      if (g_allocs[i].size != size) return 0;  /* a partial release */
      g_allocs[i].base = FPPRT_ALLOC_TOMB;
      g_allocs_live--;
      return 1;
    }
    i = (i + 1) & (g_allocs_cap - 1);
  }
  return 0;
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
  fpprt_alloc_put((uintptr_t)mem, size);
  return (struct gc_reservation){ (uintptr_t)mem, size };
}

void *gc_platform_acquire_memory_from_reservation(struct gc_reservation r,
                                                  size_t offset, size_t size) {
  GC_ASSERT(offset + size <= r.size);
  return (void *)(r.base + offset);
}

void gc_platform_release_reservation(struct gc_reservation r) {
  fpprt_alloc_take(r.base, r.size);
  free((void *)r.base);
}

void *gc_platform_acquire_memory(size_t size, size_t alignment) {
  struct gc_reservation r = gc_platform_reserve_memory(size, alignment);
  return (void *)r.base;
}

void gc_platform_release_memory(void *base, size_t size) {
  /* RETURN it to the allocator so the block is reused. Only an exact whole
   * allocation is freed; a partial release (semi's region shrink) is ignored,
   * because `free` would corrupt the allocator's bookkeeping. */
  if (fpprt_alloc_take((uintptr_t)base, size)) {
    if (fpprt_mem_log_())
      fprintf(stderr, "[mem release %zu KB <- %p]\n", size >> 10, base);
    free(base);
  } else if (fpprt_mem_log_()) {
    fprintf(stderr, "[mem release %zu KB <- %p NOT-WHOLE, kept]\n",
            size >> 10, base);
  }
}

int gc_platform_populate_memory(void *addr, size_t size) { return 1; }

int gc_platform_discard_memory(void *addr, size_t size) {
  memset(addr, 0, size);
  return 1;
}
