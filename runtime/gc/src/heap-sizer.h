#ifndef HEAP_SIZER_H
#define HEAP_SIZER_H

#include "gc-api.h"

#include "gc-options-internal.h"
#include "growable-heap-sizer.h"
#include "adaptive-heap-sizer.h"

struct gc_heap_sizer {
  enum gc_heap_size_policy policy;
  // How much heap the collector needs per byte of live data to FUNCTION:
  // 2 for the copying collectors (to-space must fit a full copy), 1 for
  // in-place collectors. The sizing policies below reason about live
  // data; this converts their answers into this collector's terms —
  // without it, growable sizing walled a semispace heap at ~1.3x live
  // and the collector died at two-thirds of what it could hold.
  size_t space_multiplier;
  union {
    struct gc_growable_heap_sizer* growable;
    struct gc_adaptive_heap_sizer* adaptive;
  };
};

static struct gc_heap_sizer
gc_make_heap_sizer(struct gc_heap *heap,
                   const struct gc_common_options *options,
                   size_t space_multiplier,
                   uint64_t (*get_allocation_counter_from_thread)(struct gc_heap*),
                   void (*set_heap_size_from_thread)(struct gc_heap*, size_t),
                   struct gc_background_thread *thread) {
  struct gc_heap_sizer ret = { options->heap_size_policy, space_multiplier, };
  switch (options->heap_size_policy) {
    case GC_HEAP_SIZE_FIXED:
      break;

    case GC_HEAP_SIZE_GROWABLE:
      ret.growable =
        gc_make_growable_heap_sizer(heap, options->heap_double_threshold);
      break;

    case GC_HEAP_SIZE_ADAPTIVE:
      ret.adaptive =
        gc_make_adaptive_heap_sizer (heap, options->heap_expansiveness,
                                     get_allocation_counter_from_thread,
                                     set_heap_size_from_thread,
                                     thread);
      break;

    default:
      GC_CRASH();
  }
  return ret;
}

static size_t
gc_heap_sizer_target_size(struct gc_heap_sizer sizer,
                          size_t heap_size, size_t live_bytes) {
  switch (sizer.policy) {
    case GC_HEAP_SIZE_FIXED:
      return heap_size;

    case GC_HEAP_SIZE_GROWABLE:
      return gc_growable_heap_sizer_target_size(sizer.growable, heap_size,
                                                live_bytes
                                                * sizer.space_multiplier);

    case GC_HEAP_SIZE_ADAPTIVE:
      return gc_adaptive_heap_sizer_target_size(sizer.adaptive, heap_size,
                                                live_bytes
                                                * sizer.space_multiplier);

    default:
      GC_CRASH();
  }
}

static void
gc_heap_sizer_on_gc(struct gc_heap_sizer sizer, size_t heap_size,
                    size_t live_bytes, size_t pause_ns,
                    void (*set_heap_size)(struct gc_heap*, size_t)) {
  switch (sizer.policy) {
    case GC_HEAP_SIZE_FIXED:
      break;

    case GC_HEAP_SIZE_GROWABLE:
      gc_growable_heap_sizer_on_gc(sizer.growable, heap_size,
                                   live_bytes * sizer.space_multiplier,
                                   pause_ns, set_heap_size);
      break;

    case GC_HEAP_SIZE_ADAPTIVE:
      if (sizer.adaptive->background_task_id < 0)
        gc_adaptive_heap_sizer_background_task(sizer.adaptive);
      gc_adaptive_heap_sizer_on_gc(sizer.adaptive,
                                   live_bytes * sizer.space_multiplier,
                                   pause_ns, set_heap_size);
      break;

    default:
      GC_CRASH();
  }
}
                    

#endif // HEAP_SIZER_H
