/* fpprt — the F++ runtime: object model and GC interface.
 *
 * One representation for every backend that has a linear address space:
 * native now, wasm-linear later. The collector behind it is Whippet
 * (runtime/gc, vendored, MIT), chosen at compile time: `semi` to shake out
 * missed roots (it moves EVERYTHING every collection), `pcc` for parallel
 * copying, `mmc` for Immix-style mark-region with real per-object pinning.
 *
 * Object layout:
 *   [ tag word ] [ fields... ]                    plain object
 *   [ tag word ] [ length ] [ elements... ]       array (ref or scalar)
 *
 * The tag is (typeid << 1) | 1 while the object is live; a forwarded
 * object's tag holds the forwarding pointer (aligned, so bit 0 = 0). The
 * typeid indexes the type table, which the compiler fills at startup with
 * each type's size and reference-field offsets — that table is the whole
 * "pointer map" story, and it is why the heap can be traced precisely and
 * objects can MOVE.
 *
 * Roots: wasm gives no stack walking and native stack maps are a compiler
 * project of their own, so ref-holding locals live in explicit shadow
 * frames (FPPRT_FRAME/FPPRT_LEAVE). The discipline is simple and brutal:
 * every ref that must survive an allocation lives in a frame slot, and the
 * `semi` collector exists to punish every violation immediately.
 */
#ifndef FPPRT_H
#define FPPRT_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef uintptr_t fpprt_ref;   /* address of the tag word; 0 = null */

/* ---- type table -------------------------------------------------------- */

enum fpprt_type_kind {
  FPPRT_KIND_STRUCT = 0,       /* fixed size, refoffs lists ref fields   */
  FPPRT_KIND_REF_ARRAY = 1,    /* [tag][len][ref x len]                  */
  FPPRT_KIND_SCALAR_ARRAY = 2, /* [tag][len][elem x len], size = elem sz */
  FPPRT_KIND_EPHEMERON = 3,    /* internal: gc_ephemeron payload         */
  FPPRT_KIND_POD_ARRAY = 4     /* flat struct elems WITH ref fields:
                                  size = elem bytes, refoffs = per-elem
                                  ELEM-RELATIVE ref offsets              */
};

struct fpprt_type {
  uint32_t size;            /* STRUCT: total bytes incl. header;
                               SCALAR_ARRAY: element bytes; else 0 */
  uint32_t kind;            /* enum fpprt_type_kind */
  uint32_t nrefs;           /* STRUCT: number of reference fields */
  const uint32_t *refoffs;  /* STRUCT: byte offsets of those fields */
  const char *name;         /* diagnostics only */
};

/* reserved typeids; the compiler registers its own from FPPRT_TID_FIRST */
#define FPPRT_TID_EPHEMERON 0u
#define FPPRT_TID_REF_ARRAY 1u
#define FPPRT_TID_HASHBOX   2u
#define FPPRT_TID_FIRST     3u

/* Register `t` under `tid`. Registration is startup-only: it is not
 * thread-safe and must complete before the second mutator exists. */
void fpprt_register_type(uint32_t tid, struct fpprt_type t);

/* ---- lifecycle --------------------------------------------------------- */

struct fpprt_opts {
  size_t heap_bytes;        /* INITIAL size; 0 = default (16 MB). The heap
                               GROWS as live data does (growable policy,
                               synchronous at collection — no background
                               thread), so this is a floor, not a limit. */
  size_t max_heap_bytes;    /* hard ceiling; 0 = none */
  int parallelism;          /* 0 = default */
};

void fpprt_init(const struct fpprt_opts *opts);

/* ---- shadow-stack roots ------------------------------------------------ */

/* a REF-HOLDING struct living on the C stack: `base` is the struct's
 * address MINUS FPP_POD_OFF, so the type table's blob-relative ref
 * offsets apply unchanged. base = NULL until the local is initialized. */
struct fpprt_frame_pod {
  char *base;
  uint32_t tid;
};

struct fpprt_frame {
  struct fpprt_frame *prev;
  uint32_t nslots;
  fpprt_ref *slots;         /* points at the caller's slot array */
  uint32_t npods;           /* stack structs with ref fields */
  struct fpprt_frame_pod *pods;
};

extern _Thread_local struct fpprt_frame *fpprt_top_frame;

/* `FPPRT_FRAME(f, 3);` declares frame f with f_slots[3], zeroed, pushed.
 * Slots are refs the GC may read AND UPDATE (moving collector). */
#define FPPRT_FRAME(f, n)                                        \
  fpprt_ref f##_slots[n] = { 0 };                                \
  struct fpprt_frame f = { fpprt_top_frame, (n), f##_slots,      \
                           0, 0 };                               \
  fpprt_top_frame = &f
#define FPPRT_LEAVE(f) (fpprt_top_frame = (f).prev)

/* ---- allocation -------------------------------------------------------- */

fpprt_ref fpprt_alloc(uint32_t tid);                     /* zeroed fields  */
fpprt_ref fpprt_alloc_array(uint32_t tid, size_t len);   /* zeroed elems   */

static inline uint32_t fpprt_typeid(fpprt_ref o) {
  return (uint32_t)((*(uintptr_t *)o) >> 1);
}
static inline size_t fpprt_array_len(fpprt_ref o) {
  return ((uintptr_t *)o)[1];
}
/* first field / first element */
static inline void *fpprt_body(fpprt_ref o) { return (uintptr_t *)o + 1; }
static inline void *fpprt_elems(fpprt_ref o) { return (uintptr_t *)o + 2; }

/* ---- reads and writes -------------------------------------------------- */

static inline fpprt_ref fpprt_read_ref(fpprt_ref o, uint32_t byteoff) {
  return *(fpprt_ref *)((char *)o + byteoff);
}
/* Every store of a REF into the heap goes through this: the collector's
 * write barrier is behind it. Scalar stores need no barrier. */
void fpprt_write_ref(fpprt_ref o, uint32_t byteoff, fpprt_ref v);

/* ---- weak references --------------------------------------------------- */

/* An ephemeron with key = value = target: the reference keeps nothing
 * alive, and reads as 0 once the target is collected. */
fpprt_ref fpprt_weak_new(fpprt_ref target);
fpprt_ref fpprt_weak_get(fpprt_ref weak);

/* The general form: value stays alive only while KEY is alive; both read
 * as 0 once the key is collected (ConditionalWeakTable's entry). */
fpprt_ref fpprt_eph_new(fpprt_ref key, fpprt_ref value);
fpprt_ref fpprt_eph_key(fpprt_ref e);
fpprt_ref fpprt_eph_value(fpprt_ref e);

const char *fpprt_type_name(uint32_t tid);

/* ---- static roots ------------------------------------------------------ */

/* Register a range of GLOBAL slots the collector reads and updates —
 * compiled code's top-level bindings. Slots holding tagged scalars
 * (bit 0 set) or 0 are ignored. Startup-only, like type registration. */
void fpprt_add_static_roots(fpprt_ref *base, size_t n);

/* ---- identity hash ----------------------------------------------------- */

/* .NET's default GetHashCode: a per-object value, assigned on first ask,
 * STABLE for the object's whole life however often the collector moves it,
 * and holding nothing alive. Backed by an ephemeron weak table whose
 * address-keyed buckets rehash after every collection. */
uintptr_t fpprt_idhash(fpprt_ref o);

/* ---- pinning ----------------------------------------------------------- */

/* Object will not move for the rest of its life (mmc collectors; on the
 * always-moving collectors this aborts — pinning is a capability the
 * embedder selects with the collector). */
void fpprt_pin(fpprt_ref o);
int fpprt_can_pin(void);

/* ---- control ----------------------------------------------------------- */

/* threads: every OS thread touching the heap attaches ONE mutator; park
 * around blocking waits so collection never stalls on a blocked thread */
void fpprt_thread_attach(void);
void fpprt_thread_detach(void);
void fpprt_thread_park(void);
void fpprt_thread_unpark(void);

/* the worker pool: one dense index range per dispatch, chunk-grabbed */
typedef void (*fpp_pool_kernel)(void *env, int lo, int hi);
int  fpp_pool_size(void);
void fpp_pool_dispatch(int n, int chunk, fpp_pool_kernel kernel, void *env);
/* groups × phases: group-local barriers as retirement counts, groups
 * pipeline independently; kernel(env, phase, lo, hi) */
typedef void (*fpp_phase_kernel)(void *env, int phase, int lo, int hi);
void fpp_pool_dispatch_phased(int n, int chunk, int groups, int phases,
                              fpp_phase_kernel kernel, void *env);

/* heap+static edges into `target`, counted up to 2; stack edges excluded */
int fpprt_heap_refs_upto2(fpprt_ref target);

void fpprt_collect(void);            /* full collection, for tests        */
void fpprt_safepoint(void);          /* poll: park if a GC wants the world */
/* the collector's stop-request flag for THIS thread — emitted loops test
 * it inline and only call fpprt_safepoint when it is set */
extern _Thread_local int *fpprt_sp_flag_;
#define FPPRT_POLL() \
  do { if (__builtin_expect(*fpprt_sp_flag_ != 0, 0)) \
         fpprt_safepoint(); } while (0)
/* the flag pointer hoisted into a local (one TLS lookup per function) */
#define FPPRT_POLL_AT(p) \
  do { if (__builtin_expect(*(p) != 0, 0)) fpprt_safepoint(); } while (0)
size_t fpprt_allocated_bytes(void);  /* lifetime allocation counter        */

#ifdef __cplusplus
}
#endif
#endif /* FPPRT_H */
