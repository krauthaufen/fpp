/* fpprt-lang — the LANGUAGE support layer over fpprt: what compiled F++
 * code calls that is not the collector itself. Tagged-value helpers,
 * strings, conversions, printing. Grows with the C backend's milestones;
 * every function here exists because generated code references it.
 */
#ifndef FPPRT_LANG_H
#define FPPRT_LANG_H

#include <inttypes.h>
#include <stdio.h>
#include <string.h>

#include "fpprt.h"

typedef fpprt_ref V;

#define TAGI(x)   ((V)((((intptr_t)(x)) << 1) | 1))
#define UNTAGI(v) (((intptr_t)(v)) >> 1)
#define VUNIT     ((V)1)

/* language-level typeids; compiler-assigned ones start at FPP_TID_USER */
#define FPP_TID_STR    (FPPRT_TID_FIRST + 0)   /* u8 scalar array */
#define FPP_TID_F64    (FPPRT_TID_FIRST + 1)   /* one boxed double */
#define FPP_TID_I64    (FPPRT_TID_FIRST + 2)   /* one boxed int64 */
#define FPP_TID_USER   (FPPRT_TID_FIRST + 8)

static inline void fpp_lang_init(void) {
  fpprt_init(NULL);
  fpprt_register_type(FPP_TID_STR, (struct fpprt_type){
    1, FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "string" });
  fpprt_register_type(FPP_TID_F64, (struct fpprt_type){
    sizeof(double), FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "float" });
  fpprt_register_type(FPP_TID_I64, (struct fpprt_type){
    sizeof(int64_t), FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "int64" });
}

/* ---- strings ----------------------------------------------------------- */

static inline V fpp_str_alloc(size_t len) {
  return fpprt_alloc_array(FPP_TID_STR, len);
}
static inline char *fpp_str_bytes(V s) { return (char *)fpprt_elems(s); }
static inline size_t fpp_str_len(V s) { return fpprt_array_len(s); }

static inline V fpp_str_c(const char *bytes, size_t len) {
  V s = fpp_str_alloc(len);
  memcpy(fpp_str_bytes(s), bytes, len);
  return s;
}

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

/* ---- conversions and printing ------------------------------------------ */

/* `string x` on a tagged int (M1; other shapes join with their milestones) */
static inline V fpp_to_string(V x) {
  if (x & 1) {
    char buf[32];
    int n = snprintf(buf, sizeof buf, "%" PRIdPTR, (intptr_t)UNTAGI(x));
    return fpp_str_c(buf, (size_t)n);
  }
  if (x && fpprt_typeid(x) == FPP_TID_STR)
    return x;
  if (x && fpprt_typeid(x) == FPP_TID_F64) {
    char buf[40];
    int n = snprintf(buf, sizeof buf, "%g", fpp_unbox_f64(x));
    return fpp_str_c(buf, (size_t)n);
  }
  if (x && fpprt_typeid(x) == FPP_TID_I64) {
    char buf[32];
    int n = snprintf(buf, sizeof buf, "%" PRId64, fpp_unbox_i64(x));
    return fpp_str_c(buf, (size_t)n);
  }
  return fpp_str_c("<obj>", 5);
}

/* the wasm backend's "not ported" stub, C-side: a GAP traps loudly WHEN
 * REACHED, never silently, and dead code costs nothing */
static inline V fpp_not_emitted(const char *what) {
  fprintf(stderr, "fpp cback: not emitted: %s\n", what);
  __builtin_trap();
}

static inline void fpp_print(V s) {
  fwrite(fpp_str_bytes(s), 1, fpp_str_len(s), stdout);
  fputc('\n', stdout);
}

#endif /* FPPRT_LANG_H */
