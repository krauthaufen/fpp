/* fpprt-lang — the LANGUAGE support layer over fpprt: what compiled F++
 * code calls that is not the collector itself. Tagged-value helpers,
 * strings, tuples, lists, cells, closures and the apply protocol,
 * structural equality/hash/compare, exceptions, printing. Grows with the
 * C backend's milestones; every function exists because generated code
 * references it. Non-trivial bodies live in fpprt-lang.c.
 */
#ifndef FPPRT_LANG_H
#define FPPRT_LANG_H

#include <inttypes.h>
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "fpprt.h"

typedef fpprt_ref V;

#if UINTPTR_MAX > 0xffffffffu
#define TAGI(x)   ((V)((((intptr_t)(x)) << 1) | 1))
#define UNTAGI(v) (((intptr_t)(v)) >> 1)
#else
/* 32-bit target: an int32 needs 32 bits, the tag holds 31 — values out of
 * range spill into i64 BOXES (Int32.MaxValue is a real sentinel: it is
 * Transaction.RunningLevel outside a transaction). eqv/cmpv/arith already
 * coerce the mixed tagged/boxed case, so a spilled int stays equal and
 * ordered against its tagged twin. This is the ACCEPTED design (decided
 * 2026-08-06): the only static alternative is always-boxing int32 here,
 * which turns every tagged pointer-compare into a structural call. The
 * spill exists ONLY at uniform positions — typed locals, params, arrays
 * and the direct-call ABI carry int32 raw and never spill. */
V fpp_box_i64_(int64_t x);                /* wrapper, defined in fpprt-lang.c */
int64_t fpp_unbox_i64_(V b);
static inline V TAGI_(intptr_t x) {
  if (x >= -(intptr_t)0x40000000 && x < (intptr_t)0x40000000)
    return (V)((x << 1) | 1);
  return fpp_box_i64_((int64_t)x);
}
static inline intptr_t UNTAGI_(V v) {
  return (v & 1) ? ((intptr_t)v >> 1) : (intptr_t)fpp_unbox_i64_(v);
}
#define TAGI(x)   TAGI_((intptr_t)(x))
#define UNTAGI(v) UNTAGI_(v)
#endif
#define VUNIT     ((V)1)
/* field offset of slot i in a heap object: generated code always speaks in
 * SLOT indices — the byte width is the TARGET's pointer size (wasm32: 4) */
#define FPPOFF(i) ((uint32_t)((i) * sizeof(V)))

/* language-level typeids; compiler-assigned ones start at FPP_TID_USER */
#define FPP_TID_STR    (FPPRT_TID_FIRST + 0)   /* UTF-16: u16 scalar array */
#define FPP_TID_F64    (FPPRT_TID_FIRST + 1)   /* one boxed double */
#define FPP_TID_I64    (FPPRT_TID_FIRST + 2)   /* one boxed int64 */
#define FPP_TID_TUPLE  (FPPRT_TID_FIRST + 3)   /* ref array, structural eq */
#define FPP_TID_CONS   (FPPRT_TID_FIRST + 4)   /* head, tail */
#define FPP_TID_CELL   (FPPRT_TID_FIRST + 5)   /* one mutable ref */
#define FPP_TID_ARR    (FPPRT_TID_FIRST + 6)   /* ref array, REFERENCE eq */
#define FPP_TID_PAP    (FPPRT_TID_FIRST + 7)   /* partial application */
#define FPP_TID_ENUM   (FPPRT_TID_FIRST + 8)   /* builtin seq enumerator */
#define FPP_TID_CMPCLO (FPPRT_TID_FIRST + 9)   /* the structural-compare closure */
/* scalar arrays: RAW element storage, one tid per element width. Typed
 * code creates and reads these; GENERIC code still creates ref arrays —
 * every accessor dispatches on the array's tid, so both reprs flow
 * everywhere soundly (no type descriptors needed). Reference equality,
 * exactly like FPP_TID_ARR. */
#define FPP_TID_AF64   (FPPRT_TID_FIRST + 10)  /* float[] */
#define FPP_TID_AF32   (FPPRT_TID_FIRST + 11)  /* float32[] */
#define FPP_TID_AI64   (FPPRT_TID_FIRST + 12)  /* int64[]/uint64[] */
#define FPP_TID_AI32   (FPPRT_TID_FIRST + 13)  /* int[]/uint32[]/enum[] */
#define FPP_TID_AU16   (FPPRT_TID_FIRST + 14)  /* char[]/int16[]/uint16[] */
#define FPP_TID_AU8    (FPPRT_TID_FIRST + 15)  /* byte[]/bool[] */
#define FPP_TID_USER   (FPPRT_TID_FIRST + 29)  /* == 32, CEmit's first tid */

/* what a tid MEANS to equality/printing; index = tid */
#define FPP_TC_OTHER  0
#define FPP_TC_RECORD 1   /* structural equality over fields */
#define FPP_TC_CASE   2   /* union case: tid + fields */
#define FPP_TC_CLO    3   /* closures: reference equality */
#define FPP_TC_CLASS  4   /* classes: reference equality, idhash */
extern unsigned char *fpp_tclass_;
extern unsigned int *fpp_tfields_;
extern size_t fpp_tmeta_cap_;

void fpp_reg_meta_(uint32_t tid, int tclass, unsigned nfields);

/* a compiled struct type: header + n uniform V fields, ALL on the map
 * (tagged scalars are skipped by the tracer) */
void fpp_reg_struct(uint32_t tid, unsigned nfields, int tclass,
                    const char *name);

/* a closure type: [tag][code][arity][env...]; code+arity off the map */
typedef V (*fpp_code_t)(V self, V *args);
void fpp_reg_clo(uint32_t tid, unsigned nenv);

static inline int fpp_is_tid(V v, uint32_t tid) {
  return v != 0 && !(v & 1) && fpprt_typeid(v) == tid;
}

/* ---- strings: UTF-16, as .NET has them --------------------------------- */
/* Length counts CODE UNITS; a char is one 16-bit unit. Literals arrive as
 * UTF-8 (the compiler's source text) and decode once at creation; printing
 * encodes back to UTF-8 for the terminal. */

static inline uint16_t *fpp_str_units(V s) { return (uint16_t *)fpprt_elems(s); }
static inline size_t fpp_str_len(V s) { return fpprt_array_len(s); }

V fpp_str_utf8(const char *bytes, size_t len);   /* decode UTF-8 -> UTF-16 */
#define fpp_str_c fpp_str_utf8

V fpp_str_concat(V a, V b);
V fpp_str_method(const char *m, V recv, V *args, size_t nargs);
int fpp_str_cmp(V a, V b);
void fpp_prints(V s);   /* NO newline — printfn-formatted text carries its own */

/* ---- boxes ------------------------------------------------------------- */

static inline V fpp_box_f64(double x) {
  V b = fpprt_alloc_array(FPP_TID_F64, 1);
  *(double *)fpprt_elems(b) = x;
  return b;
}
static inline double fpp_unbox_f64(V b) { return *(double *)fpprt_elems(b); }

static inline V fpp_box_i64(int64_t x) {
  V b = fpprt_alloc_array(FPP_TID_I64, 1);
  *(int64_t *)fpprt_elems(b) = x;
  return b;
}
static inline int64_t fpp_unbox_i64(V b) { return *(int64_t *)fpprt_elems(b); }

/* ---- tuples, lists, cells, arrays -------------------------------------- */

static inline V fpp_tuple(size_t n) { return fpprt_alloc_array(FPP_TID_TUPLE, n); }
static inline void fpp_tuple_set(V t, size_t i, V v) {
  fpprt_write_ref(t, (uint32_t)((i + 2) * sizeof(V)), v);
}
static inline V fpp_tuple_get(V t, size_t i) {
  return fpprt_read_ref(t, (uint32_t)((i + 2) * sizeof(V)));
}

V fpp_cons(V h, V t);
V fpp_cell_new(V v);
static inline V fpp_cell_get(V c) { return fpprt_read_ref(c, sizeof(V)); }
static inline void fpp_cell_set(V c, V v) { fpprt_write_ref(c, sizeof(V), v); }

static inline V fpp_arr_new(size_t n) { return fpprt_alloc_array(FPP_TID_ARR, n); }
V fpp_arr_zeroed(int kind, size_t n);   /* 0 ref, 1 int, 2 f64, 3 i64 */

/* dispatching accessors: correct on BOTH reprs; scalar elems box on get */
V fpp_arr_get(V a, size_t i);
void fpp_arr_set(V a, size_t i, V v);

static inline void fpp_arr_check_(V a, size_t i) {
  if (i >= fpprt_array_len(a)) {
    fprintf(stderr, "fpp: index out of range\n");
    abort();
  }
}

/* typed RAW accessors: direct on the matching scalar tid, dispatch (and
 * box/unbox) otherwise — the hot path never allocates */
#define FPP_SARR_ACC(NAME, CT, TID, UNBOX, BOX)                              \
  static inline CT fpp_arr_get_##NAME(V a, size_t i) {                       \
    fpp_arr_check_(a, i);                                                    \
    if (fpprt_typeid(a) == TID) return ((CT *)fpprt_elems(a))[i];            \
    { V e_ = fpp_arr_get(a, i); return (CT)(UNBOX); }                        \
  }                                                                          \
  static inline void fpp_arr_set_##NAME(V a, size_t i, CT v_) {              \
    fpp_arr_check_(a, i);                                                    \
    if (fpprt_typeid(a) == TID) { ((CT *)fpprt_elems(a))[i] = v_; return; }  \
    fpp_arr_set(a, i, (BOX));                                                \
  }
FPP_SARR_ACC(f64, double,   FPP_TID_AF64, fpp_unbox_f64(e_), fpp_box_f64(v_))
FPP_SARR_ACC(f32, float,    FPP_TID_AF32, fpp_unbox_f64(e_), fpp_box_f64((double)v_))
FPP_SARR_ACC(i64, int64_t,  FPP_TID_AI64, fpp_unbox_i64(e_), fpp_box_i64(v_))
FPP_SARR_ACC(i32, int32_t,  FPP_TID_AI32, UNTAGI(e_), TAGI((intptr_t)v_))
FPP_SARR_ACC(u16, uint16_t, FPP_TID_AU16, UNTAGI(e_), TAGI((intptr_t)v_))
FPP_SARR_ACC(u8,  uint8_t,  FPP_TID_AU8,  UNTAGI(e_), TAGI((intptr_t)v_))
#undef FPP_SARR_ACC

/* ---- ConditionalWeakTable ------------------------------------------------
 * The table object's FIRST field (offset sizeof(V)) holds a ref-array of
 * ephemerons: 0 = free slot, key reads 0 = dead entry. Keys are compared by
 * IDENTITY, entries hold neither key nor value alive. The compiler routes
 * the prelude class's ctor and members here. */
void fpp_cwt_init(V self);
V fpp_cwt_tryget(V self, V k);   /* value, or 0 when absent/dead   */
void fpp_cwt_add(V self, V k, V v);
V fpp_cwt_remove(V self, V k);   /* tagged bool                    */
V fpp_cwt_count(V self);         /* tagged live-entry count        */
V fpp_cwt_indexof(V self, V k);  /* tagged live index, -1 = absent */

/* ---- closures and apply ------------------------------------------------- */

static inline fpp_code_t fpp_clo_code(V c) {
  return (fpp_code_t)((uintptr_t *)c)[1];
}
static inline size_t fpp_clo_arity(V c) { return ((uintptr_t *)c)[2]; }

static inline V fpp_clo_new(uint32_t tid, fpp_code_t code, size_t arity,
                            size_t nenv) {
  (void)nenv;
  V c = fpprt_alloc(tid);
  ((uintptr_t *)c)[1] = (uintptr_t)code;
  ((uintptr_t *)c)[2] = arity;
  return c;
}

/* full curried semantics: under-application makes a PAP, over-application
 * calls then applies the rest */
V fpp_apply(V clo, V *args, size_t n);

/* ---- interface dispatch: [typeid][slot] -> uniform member wrapper ------- */

void fpp_vt_set(uint32_t tid, int slot, fpp_code_t fn);
V fpp_vcall(V obj, int slot, V *args, size_t n);
int fpp_vt_has(V obj, int slot);   /* interface type-test: slot filled? */
void fpp_reg_cmp(uint32_t tid, int slot);   /* class's CompareTo vt slot */
void fpp_reg_eq(uint32_t tid, int slot);    /* class's Equals vt slot */
void fpp_reg_hash(uint32_t tid, int slot);  /* class's GetHashCode vt slot */
V fpp_append(V a, V b);                     /* list @ list */

/* byref out-params: a ByRefView {Get;Set} aliases a location, a plain
 * ByRefCell holds the value — the intrinsics dispatch like compiled code */
void fpp_reg_brview(uint32_t tid);
void fpp_byref_set(V p, V v);
V fpp_byref_get(V p);

/* the FAT-PAIR byref the compiler passes on direct calls: (container, off).
 * off == 1 -> dynamic view-or-cell dispatch on the object; container == 0
 * -> off is a raw pointer to a caller frame slot (C stack, never moves);
 * else a heap object and a byte offset into it. */
static inline V fpp_br_get(V c, uintptr_t o) {
  if (o == 1) return fpp_byref_get(c);
  if (!c) return *(V *)o;
  return fpprt_read_ref(c, (uint32_t)o);
}
static inline void fpp_br_set(V c, uintptr_t o, V v) {
  if (o == 1) { fpp_byref_set(c, v); return; }
  if (!c) { *(V *)o = v; return; }   /* frame slots are roots: no barrier */
  fpprt_write_ref(c, (uint32_t)o, v);
}

/* class inheritance: `:? Base` must accept derived and stamped tids */
void fpp_reg_parent(uint32_t tid, uint32_t parent);
int fpp_isa(V x, uint32_t tid);

/* builtin seq protocol over arrays, lists and strings: the compiler wires
 * these into ITS slot numbers for IEnumerable/IEnumerator */
V fpp_seq_getenum(V self, V *args);
V fpp_enum_movenext(V self, V *args);
/* the program's slot numbers for the seq protocol — lets fpp_vcall treat a
 * NULL receiver as the empty sequence (null IS the empty list) */
void fpp_seq_slots(int ge, int mn, int disp);
V fpp_enum_current(V self, V *args);
V fpp_enum_dispose(V self, V *args);

/* ---- exceptions --------------------------------------------------------- */

struct fpp_handler {
  jmp_buf jb;
  struct fpp_handler *prev;
  struct fpprt_frame *frame_top;   /* shadow stack restores on unwind */
  const char *site;                /* diagnostics: the pushing function */
};
extern _Thread_local struct fpp_handler *fpp_handler_top_;
extern _Thread_local V fpp_exn_;

/* handler-event ring for diagnosing leaks (FPP_HLOG builds) */
extern const char *fpp_hlog_site_[64];
extern char fpp_hlog_kind_[64];
extern void *fpp_hlog_ptr_[64];
extern unsigned fpp_hlog_n_;
static inline void fpp_hlog_(char kind, const char *site, void *p) {
  fpp_hlog_kind_[fpp_hlog_n_ & 63] = kind;
  fpp_hlog_site_[fpp_hlog_n_ & 63] = site;
  fpp_hlog_ptr_[fpp_hlog_n_ & 63] = p;
  fpp_hlog_n_++;
}
void fpp_hlog_dump(void);

/* setjmp may ONLY appear as (nearly) the whole controlling expression —
 * returning its value through a function is undefined behavior, and under
 * -O1 the longjmp return path genuinely collapsed (the handler branch was
 * never taken). So the push bookkeeping is a separate statement and the
 * generated code writes `if (!setjmp(H.jb))` itself. */
static inline void fpp_handler_push_(struct fpp_handler *h, const char *site) {
  h->prev = fpp_handler_top_;
  h->frame_top = fpprt_top_frame;
  h->site = site;
  fpp_handler_top_ = h;
  fpp_hlog_('T', site, (void *)h);
}
static inline void fpp_try_pop(void) {
  fpp_handler_top_ = fpp_handler_top_->prev;
}
/* identity-checked pop: the handler being popped MUST be the top — a
 * mismatch means some try leaked its handler, and the next raise would
 * longjmp into a dead stack frame */
static inline void fpp_try_pop2(struct fpp_handler *h) {
  fpp_hlog_('P', h->site, (void *)h);
  if (fpp_handler_top_ != h) {
    fpp_hlog_dump();
    fflush(stdout);
    fprintf(stderr, "fpp: handler pop mismatch (leaked from %s, popping in %s)\n",
            fpp_handler_top_ ? fpp_handler_top_->site : "?", h->site);
    abort();
  }
  fpp_handler_top_ = h->prev;
}
static inline V fpp_exn_value(void) { return fpp_exn_; }

void fpp_raise(V payload);
extern uint32_t fpp_failure_tid_;   /* the program's Failure case, 0 = none */
V fpp_failure(const char *msg, size_t len);   /* Failure(msg) or raw string */
void fpp_reraise(void);
void fpp_match_fail(void);

/* ---- structural equality / hash / compare ------------------------------ */

int fpp_eqv(V a, V b);
int fpp_cmpv(V a, V b);
intptr_t fpp_hashv(V v);

/* ---- conversions and printing ------------------------------------------ */

static inline V fpp_to_int(V x) {
  if (x & 1) return x;
  if (fpp_is_tid(x, FPP_TID_F64)) return TAGI((intptr_t)fpp_unbox_f64(x));
  if (fpp_is_tid(x, FPP_TID_I64)) return TAGI((intptr_t)fpp_unbox_i64(x));
  if (fpp_is_tid(x, FPP_TID_STR)) {
    char buf[32];
    size_t n = fpp_str_len(x) < 31 ? fpp_str_len(x) : 31;
    for (size_t i = 0; i < n; i++) buf[i] = (char)fpp_str_units(x)[i];
    buf[n] = 0;
    return TAGI((intptr_t)strtoll(buf, NULL, 10));
  }
  return TAGI(0);
}

static inline V fpp_to_f64(V x) {
  if (x & 1) return fpp_box_f64((double)UNTAGI(x));
  if (fpp_is_tid(x, FPP_TID_F64)) return x;
  if (fpp_is_tid(x, FPP_TID_I64)) return fpp_box_f64((double)fpp_unbox_i64(x));
  return fpp_box_f64(0.0);
}

static inline V fpp_to_i64(V x) {
  if (x & 1) return fpp_box_i64((int64_t)UNTAGI(x));
  if (fpp_is_tid(x, FPP_TID_I64)) return x;
  if (fpp_is_tid(x, FPP_TID_F64)) return fpp_box_i64((int64_t)fpp_unbox_f64(x));
  return fpp_box_i64(0);
}

V fpp_to_string(V x);
V fpp_showv(V x);
void fpp_print_any(V x);
void fpp_print_u32(V x);
V fpp_negv(V a);
V fpp_absv(V a);
V fpp_signv(V a);
double fpp_round_even(double x);
V fpp_addv(V a, V b);
V fpp_subv(V a, V b);
V fpp_mulv(V a, V b);
V fpp_divv(V a, V b);
V fpp_modv(V a, V b);
V fpp_f64_to_string(V x);
static inline V fpp_u64_to_string(V x) {
  char buf[24];
  int n = snprintf(buf, sizeof buf, "%" PRIu64, (uint64_t)fpp_unbox_i64(x));
  return fpp_str_c(buf, (size_t)n);
}
static inline V fpp_u32_to_string(V x) {
  char buf[16];
  int n = snprintf(buf, sizeof buf, "%u", (unsigned)UNTAGI(x));
  return fpp_str_c(buf, (size_t)n);
}
static inline V fpp_bool_to_string(V x) {
  return UNTAGI(x) ? fpp_str_c("True", 4) : fpp_str_c("False", 5);
}
static inline V fpp_char_to_string(V x) {
  V s = fpprt_alloc_array(FPP_TID_STR, 1);
  fpp_str_units(s)[0] = (uint16_t)UNTAGI(x);
  return s;
}

void fpp_print(V s);                     /* UTF-8 encode + newline */

/* the wasm backend's "not ported" stub, C-side: a GAP traps loudly WHEN
 * REACHED, never silently, and dead code costs nothing */
static inline V fpp_not_emitted(const char *what) {
  fflush(stdout);
  fprintf(stderr, "fpp cback: not emitted: %s\n", what);
  abort();
}

/* checked-build field guard: receiver must be a REF whose type has more
 * than `idx` fields; prints who/what before dying */
static inline void fpp_chk(V recv, unsigned idx, const char *who) {
  if (!recv || (recv & 1)) {
    fflush(stdout);
    fprintf(stderr, "fpp chk: %s on %s\n", who, recv ? "TAGGED" : "NULL");
    abort();
  }
  uint32_t tid = fpprt_typeid(recv);
  if (tid < fpp_tmeta_cap_ && fpp_tfields_[tid] <= idx
      && fpp_tclass_[tid] != 0) {
    fflush(stdout);
    fprintf(stderr, "fpp chk: %s idx %u on %s (%u fields)\n", who, idx,
            fpprt_type_name(tid), fpp_tfields_[tid]);
    abort();
  }
}

extern V fpp_cmpv_clo_;   /* arity-2 closure over fpp_cmpv, made at init */

void fpp_lang_init(void);

#endif /* FPPRT_LANG_H */

/* ---- POD (blittable) structs and their arrays ---------------------------
 * A blittable struct VALUE in uniform position is a heap BLOB:
 * [tag][8-byte pad to FPP_POD_OFF][C-layout payload]. Field offsets and
 * sizes come from the C compiler itself — the generated code registers
 * them with offsetof/sizeof, so the layout IS the C ABI by construction.
 * Arrays of blittable structs store elements FLAT (C stride). */
#define FPP_POD_OFF 8
#define FPP_TC_POD 5
void fpp_reg_pod(uint32_t tid, uint32_t size, const char *name);
/* ref-holding flat structs: `refoffs` are BLOB-relative (FPP_POD_OFF +
 * field) V-field offsets — the same table traces heap blobs AND stack
 * locals (frame pods pass base = addr - FPP_POD_OFF) */
void fpp_reg_pod2(uint32_t tid, uint32_t size, uint32_t nrefs,
                  const uint32_t *refoffs, const char *name);
void fpp_reg_pod_field(uint32_t tid, uint32_t off, char kind);
void fpp_reg_pod_arr(uint32_t arrtid, uint32_t elemtid, uint32_t elemsz,
                     const char *name);
/* ref-holding elems stay FLAT: the array's type entry carries the elem's
 * ref offsets rebased to the element start (refoffs arrive blob-relative,
 * the same PRF_ table fpp_reg_pod2 takes) */
void fpp_reg_pod_ref_arr(uint32_t arrtid, uint32_t elemtid, uint32_t elemsz,
                         uint32_t nrefs, const uint32_t *blobrefoffs,
                         const char *name);
V fpp_pod_box(uint32_t tid, uint32_t size);          /* zeroed blob */
V fpp_pod_clone(V blob);                             /* fresh copy */
V fpp_rec_clone(V rec);                              /* uniform shallow copy */
V fpp_pod_get(V a, size_t i, uint32_t elemtid);      /* flat elem -> blob */
void fpp_pod_set(V a, size_t i, V blob);             /* blob -> flat elem */
int fpp_pod_eq(V a, V b);
int fpp_pod_cmp(V a, V b);
intptr_t fpp_pod_hash(V v);

/* ---- linear memory (the Memory module) ----------------------------------
 * The wasm oracle's Memory is real linear memory; natively it is ONE
 * growable arena, addresses are int OFFSETS into it. `fpp_mem_base()` is
 * exported so foreign C code can turn an offset into a pointer. */
char *fpp_mem_base(void);
int32_t fpp_mem_alloc(int32_t n);
int32_t fpp_mem_size(void);
void fpp_mem_copy(int32_t dst, int32_t src, int32_t n);
int32_t fpp_arr_bytesize(V a);
int32_t fpp_arr_pin(V a);       /* copy INTO the arena, remember */
void fpp_arr_unpin(V a);        /* copy BACK, forget */
