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

#define TAGI(x)   ((V)((((intptr_t)(x)) << 1) | 1))
#define UNTAGI(v) (((intptr_t)(v)) >> 1)
#define VUNIT     ((V)1)

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
#define FPP_TID_USER   (FPPRT_TID_FIRST + 29)  /* == 32, CEmit's first tid */

/* what a tid MEANS to equality/printing; index = tid */
#define FPP_TC_OTHER  0
#define FPP_TC_RECORD 1   /* structural equality over fields */
#define FPP_TC_CASE   2   /* union case: tid + fields */
#define FPP_TC_CLO    3   /* closures: reference equality */
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
V fpp_arr_zeroed(int kind, size_t n);   /* 0 ref, 1 tagged 0, 2 f64 0.0, 3 i64 0 */
static inline V fpp_arr_get(V a, size_t i) {
  if (i >= fpprt_array_len(a)) {
    fprintf(stderr, "fpp: index out of range\n");
    abort();
  }
  return fpprt_read_ref(a, (uint32_t)((i + 2) * sizeof(V)));
}
static inline void fpp_arr_set(V a, size_t i, V v) {
  if (i >= fpprt_array_len(a)) {
    fprintf(stderr, "fpp: index out of range\n");
    abort();
  }
  fpprt_write_ref(a, (uint32_t)((i + 2) * sizeof(V)), v);
}

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

/* builtin seq protocol over arrays, lists and strings: the compiler wires
 * these into ITS slot numbers for IEnumerable/IEnumerator */
V fpp_seq_getenum(V self, V *args);
V fpp_enum_movenext(V self, V *args);
V fpp_enum_current(V self, V *args);
V fpp_enum_dispose(V self, V *args);

/* ---- exceptions --------------------------------------------------------- */

struct fpp_handler {
  jmp_buf jb;
  struct fpp_handler *prev;
  struct fpprt_frame *frame_top;   /* shadow stack restores on unwind */
};
extern struct fpp_handler *fpp_handler_top_;
extern V fpp_exn_;

static inline int fpp_try(struct fpp_handler *h) {
  h->prev = fpp_handler_top_;
  h->frame_top = fpprt_top_frame;
  fpp_handler_top_ = h;
  return setjmp(h->jb);
}
static inline void fpp_try_pop(void) {
  fpp_handler_top_ = fpp_handler_top_->prev;
}
static inline V fpp_exn_value(void) { return fpp_exn_; }

void fpp_raise(V payload);
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

void fpp_lang_init(void);

#endif /* FPPRT_LANG_H */
