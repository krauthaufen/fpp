/* fpprt-lang: the non-inline bodies. See fpprt-lang.h. */
#include "fpprt-lang.h"

unsigned char *fpp_tclass_ = NULL;
unsigned int *fpp_tfields_ = NULL;
size_t fpp_tmeta_cap_ = 0;

struct fpp_handler *fpp_handler_top_ = NULL;
V fpp_exn_ = 0;

void fpp_reg_meta_(uint32_t tid, int tclass, unsigned nfields) {
  if (tid >= fpp_tmeta_cap_) {
    size_t cap = fpp_tmeta_cap_ ? fpp_tmeta_cap_ : 64;
    while (tid >= cap) cap *= 2;
    fpp_tclass_ = realloc(fpp_tclass_, cap);
    fpp_tfields_ = realloc(fpp_tfields_, cap * sizeof(unsigned int));
    if (!fpp_tclass_ || !fpp_tfields_) abort();
    memset(fpp_tclass_ + fpp_tmeta_cap_, 0, cap - fpp_tmeta_cap_);
    memset(fpp_tfields_ + fpp_tmeta_cap_, 0,
           (cap - fpp_tmeta_cap_) * sizeof(unsigned int));
    fpp_tmeta_cap_ = cap;
  }
  fpp_tclass_[tid] = (unsigned char)tclass;
  fpp_tfields_[tid] = nfields;
}

void fpp_reg_struct(uint32_t tid, unsigned nfields, int tclass,
                    const char *name) {
  uint32_t *offs = malloc(sizeof(uint32_t) * (nfields ? nfields : 1));
  if (!offs) abort();
  for (unsigned i = 0; i < nfields; i++) offs[i] = (i + 1) * sizeof(V);
  fpprt_register_type(tid, (struct fpprt_type){
    (uint32_t)((nfields + 1) * sizeof(V)), FPPRT_KIND_STRUCT,
    nfields, offs, name });
  fpp_reg_meta_(tid, tclass, nfields);
}

void fpp_reg_clo(uint32_t tid, unsigned nenv) {
  uint32_t *offs = malloc(sizeof(uint32_t) * (nenv ? nenv : 1));
  if (!offs) abort();
  for (unsigned i = 0; i < nenv; i++) offs[i] = (i + 3) * sizeof(V);
  fpprt_register_type(tid, (struct fpprt_type){
    (uint32_t)((nenv + 3) * sizeof(V)), FPPRT_KIND_STRUCT,
    nenv, offs, "closure" });
  fpp_reg_meta_(tid, FPP_TC_CLO, nenv);
}

/* ---- allocation helpers that must root their inputs -------------------- */

V fpp_str_utf8(const char *bytes, size_t len) {
  /* count units first: BMP chars are one unit, astral pairs two */
  size_t units = 0;
  for (size_t i = 0; i < len;) {
    unsigned char c = (unsigned char)bytes[i];
    if (c < 0x80) { i += 1; units += 1; }
    else if (c < 0xe0) { i += 2; units += 1; }
    else if (c < 0xf0) { i += 3; units += 1; }
    else { i += 4; units += 2; }
  }
  V s = fpprt_alloc_array(FPP_TID_STR, units);
  uint16_t *u = fpp_str_units(s);
  size_t k = 0;
  for (size_t i = 0; i < len;) {
    unsigned char c = (unsigned char)bytes[i];
    uint32_t cp;
    if (c < 0x80) { cp = c; i += 1; }
    else if (c < 0xe0) {
      cp = ((uint32_t)(c & 0x1f) << 6) | (bytes[i + 1] & 0x3f);
      i += 2;
    } else if (c < 0xf0) {
      cp = ((uint32_t)(c & 0x0f) << 12) | ((uint32_t)(bytes[i + 1] & 0x3f) << 6)
         | (bytes[i + 2] & 0x3f);
      i += 3;
    } else {
      cp = ((uint32_t)(c & 0x07) << 18) | ((uint32_t)(bytes[i + 1] & 0x3f) << 12)
         | ((uint32_t)(bytes[i + 2] & 0x3f) << 6) | (bytes[i + 3] & 0x3f);
      i += 4;
    }
    if (cp >= 0x10000) {
      cp -= 0x10000;
      u[k++] = (uint16_t)(0xd800 | (cp >> 10));
      u[k++] = (uint16_t)(0xdc00 | (cp & 0x3ff));
    } else {
      u[k++] = (uint16_t)cp;
    }
  }
  return s;
}

V fpp_str_concat(V a, V b) {
  FPPRT_FRAME(f, 2);
  f_slots[0] = a; f_slots[1] = b;
  V s = fpprt_alloc_array(FPP_TID_STR,
                          fpp_str_len(f_slots[0]) + fpp_str_len(f_slots[1]));
  memcpy(fpp_str_units(s), fpp_str_units(f_slots[0]),
         fpp_str_len(f_slots[0]) * 2);
  memcpy(fpp_str_units(s) + fpp_str_len(f_slots[0]),
         fpp_str_units(f_slots[1]), fpp_str_len(f_slots[1]) * 2);
  FPPRT_LEAVE(f);
  return s;
}

int fpp_str_cmp(V a, V b) {
  /* ordinal, by code unit — .NET's String.CompareOrdinal */
  size_t la = fpp_str_len(a), lb = fpp_str_len(b);
  size_t n = la < lb ? la : lb;
  uint16_t *ua = fpp_str_units(a), *ub = fpp_str_units(b);
  for (size_t i = 0; i < n; i++)
    if (ua[i] != ub[i]) return ua[i] < ub[i] ? -1 : 1;
  return la < lb ? -1 : la > lb ? 1 : 0;
}

void fpp_print(V s) {
  uint16_t *u = fpp_str_units(s);
  size_t n = fpp_str_len(s);
  for (size_t i = 0; i < n; i++) {
    uint32_t cp = u[i];
    if (cp >= 0xd800 && cp < 0xdc00 && i + 1 < n
        && u[i + 1] >= 0xdc00 && u[i + 1] < 0xe000) {
      cp = 0x10000 + ((cp - 0xd800) << 10) + (u[i + 1] - 0xdc00);
      i++;
    }
    if (cp < 0x80) fputc((int)cp, stdout);
    else if (cp < 0x800) {
      fputc(0xc0 | (cp >> 6), stdout);
      fputc(0x80 | (cp & 0x3f), stdout);
    } else if (cp < 0x10000) {
      fputc(0xe0 | (cp >> 12), stdout);
      fputc(0x80 | ((cp >> 6) & 0x3f), stdout);
      fputc(0x80 | (cp & 0x3f), stdout);
    } else {
      fputc(0xf0 | (cp >> 18), stdout);
      fputc(0x80 | ((cp >> 12) & 0x3f), stdout);
      fputc(0x80 | ((cp >> 6) & 0x3f), stdout);
      fputc(0x80 | (cp & 0x3f), stdout);
    }
  }
  fputc('\n', stdout);
}

V fpp_cons(V h, V t) {
  FPPRT_FRAME(f, 2);
  f_slots[0] = h; f_slots[1] = t;
  V c = fpprt_alloc(FPP_TID_CONS);
  fpprt_write_ref(c, 1 * sizeof(V), f_slots[0]);
  fpprt_write_ref(c, 2 * sizeof(V), f_slots[1]);
  FPPRT_LEAVE(f);
  return c;
}

V fpp_cell_new(V v) {
  FPPRT_FRAME(f, 1);
  f_slots[0] = v;
  V c = fpprt_alloc(FPP_TID_CELL);
  fpprt_write_ref(c, 1 * sizeof(V), f_slots[0]);
  FPPRT_LEAVE(f);
  return c;
}

/* ---- apply: full curried semantics -------------------------------------- */
/* PAP layout: [tag][code][remaining][inner][got:tuple] — inner+got traced */

static V fpp_pap_code_(V self, V *args) {
  /* self: the PAP; args: the NEW arguments (exactly `remaining` of them) */
  FPPRT_FRAME(f, 3);
  f_slots[0] = fpprt_read_ref(self, 3 * sizeof(V));    /* inner closure */
  f_slots[1] = fpprt_read_ref(self, 4 * sizeof(V));    /* got tuple */
  size_t ngot = fpprt_array_len(f_slots[1]);
  size_t nnew = fpp_clo_arity(self);
  size_t total = ngot + nnew;
  /* assemble the full argument span in a frame-rooted C array */
  V full[64];
  if (total > 64) fpp_not_emitted("apply arity > 64");
  struct fpprt_frame af = { fpprt_top_frame, (uint32_t)total, full };
  for (size_t i = 0; i < total; i++) full[i] = 0;
  fpprt_top_frame = &af;
  for (size_t i = 0; i < ngot; i++) full[i] = fpp_tuple_get(f_slots[1], i);
  for (size_t i = 0; i < nnew; i++) full[ngot + i] = args[i];
  V r = fpp_apply(f_slots[0], full, total);
  fpprt_top_frame = af.prev;
  FPPRT_LEAVE(f);
  return r;
}

V fpp_apply(V clo, V *args, size_t n) {
  if (!clo || (clo & 1)) fpp_not_emitted("apply to non-closure");
  size_t arity = fpp_clo_arity(clo);
  if (n == arity)
    return fpp_clo_code(clo)(clo, args);
  if (n < arity) {
    /* under-application: a PAP holding what arrived */
    FPPRT_FRAME(f, 2);
    f_slots[0] = clo;
    V got = fpp_tuple(n);
    f_slots[1] = got;
    for (size_t i = 0; i < n; i++) fpp_tuple_set(f_slots[1], i, args[i]);
    V pap = fpp_clo_new(FPP_TID_PAP, fpp_pap_code_, arity - n, 2);
    fpprt_write_ref(pap, 3 * sizeof(V), f_slots[0]);
    fpprt_write_ref(pap, 4 * sizeof(V), f_slots[1]);
    FPPRT_LEAVE(f);
    return pap;
  }
  /* over-application: saturate, then apply the result to the rest */
  {
    FPPRT_FRAME(f, 1);
    /* args beyond arity stay rooted: they live in the CALLER's frame span */
    V r = fpp_clo_code(clo)(clo, args);
    f_slots[0] = r;
    V out = fpp_apply(f_slots[0], args + arity, n - arity);
    FPPRT_LEAVE(f);
    return out;
  }
}

/* ---- exceptions --------------------------------------------------------- */

void fpp_raise(V payload) {
  if (!fpp_handler_top_) {
    fflush(stdout);
    fprintf(stderr, "fpp: unhandled exception\n");
    if (fpp_is_tid(payload, FPP_TID_STR)) {
      fprintf(stderr, "  ");
      for (size_t i = 0; i < fpp_str_len(payload); i++)
        fputc((int)fpp_str_units(payload)[i] & 0x7f, stderr);
      fputc('\n', stderr);
    }
    exit(101);
  }
  struct fpp_handler *h = fpp_handler_top_;
  fpp_handler_top_ = h->prev;
  fpp_exn_ = payload;
  fpprt_top_frame = h->frame_top;
  longjmp(h->jb, 1);
}

void fpp_reraise(void) { fpp_raise(fpp_exn_); }

void fpp_match_fail(void) {
  fpp_raise(fpp_str_c("match failure", 13));
}

/* ---- structural equality / hash / compare ------------------------------ */

static int fpp_tclass_of_(V v) {
  uint32_t tid = fpprt_typeid(v);
  return tid < fpp_tmeta_cap_ ? fpp_tclass_[tid] : FPP_TC_OTHER;
}

int fpp_eqv(V a, V b) {
  if (a == b) return 1;
  if ((a & 1) || (b & 1) || !a || !b) return 0;
  uint32_t ta = fpprt_typeid(a), tb = fpprt_typeid(b);
  if (ta != tb) return 0;
  switch (ta) {
  case FPP_TID_STR: return fpp_str_cmp(a, b) == 0;
  case FPP_TID_F64: return fpp_unbox_f64(a) == fpp_unbox_f64(b);
  case FPP_TID_I64: return fpp_unbox_i64(a) == fpp_unbox_i64(b);
  case FPP_TID_TUPLE: {
    size_t n = fpprt_array_len(a);
    if (n != fpprt_array_len(b)) return 0;
    for (size_t i = 0; i < n; i++)
      if (!fpp_eqv(fpp_tuple_get(a, i), fpp_tuple_get(b, i))) return 0;
    return 1;
  }
  case FPP_TID_CONS:
    return fpp_eqv(fpprt_read_ref(a, sizeof(V)), fpprt_read_ref(b, sizeof(V)))
        && fpp_eqv(fpprt_read_ref(a, 2 * sizeof(V)),
                   fpprt_read_ref(b, 2 * sizeof(V)));
  case FPP_TID_ARR: return 0;              /* reference equality only */
  case FPP_TID_CELL: return 0;
  default: {
    int tc = fpp_tclass_of_(a);
    if (tc == FPP_TC_RECORD || tc == FPP_TC_CASE) {
      unsigned n = fpp_tfields_[ta];
      for (unsigned i = 0; i < n; i++)
        if (!fpp_eqv(fpprt_read_ref(a, (i + 1) * sizeof(V)),
                     fpprt_read_ref(b, (i + 1) * sizeof(V)))) return 0;
      return 1;
    }
    return 0;                              /* closures, classes: identity */
  }
  }
}

int fpp_cmpv(V a, V b) {
  if (a == b) return 0;
  if ((a & 1) && (b & 1))
    return UNTAGI(a) < UNTAGI(b) ? -1 : UNTAGI(a) > UNTAGI(b) ? 1 : 0;
  if (!a) return -1;
  if (!b) return 1;
  if ((a & 1) || (b & 1)) return (a & 1) ? -1 : 1;
  uint32_t ta = fpprt_typeid(a), tb = fpprt_typeid(b);
  if (ta != tb) return ta < tb ? -1 : 1;
  switch (ta) {
  case FPP_TID_STR: return fpp_str_cmp(a, b);
  case FPP_TID_F64: {
    double x = fpp_unbox_f64(a), y = fpp_unbox_f64(b);
    return x < y ? -1 : x > y ? 1 : 0;
  }
  case FPP_TID_I64: {
    int64_t x = fpp_unbox_i64(a), y = fpp_unbox_i64(b);
    return x < y ? -1 : x > y ? 1 : 0;
  }
  case FPP_TID_TUPLE: {
    size_t na = fpprt_array_len(a), nb = fpprt_array_len(b);
    size_t n = na < nb ? na : nb;
    for (size_t i = 0; i < n; i++) {
      int c = fpp_cmpv(fpp_tuple_get(a, i), fpp_tuple_get(b, i));
      if (c) return c;
    }
    return na < nb ? -1 : na > nb ? 1 : 0;
  }
  case FPP_TID_CONS: {
    int c = fpp_cmpv(fpprt_read_ref(a, sizeof(V)), fpprt_read_ref(b, sizeof(V)));
    if (c) return c;
    return fpp_cmpv(fpprt_read_ref(a, 2 * sizeof(V)),
                    fpprt_read_ref(b, 2 * sizeof(V)));
  }
  default: {
    int tc = fpp_tclass_of_(a);
    if (tc == FPP_TC_RECORD || tc == FPP_TC_CASE) {
      unsigned n = fpp_tfields_[ta];
      for (unsigned i = 0; i < n; i++) {
        int c = fpp_cmpv(fpprt_read_ref(a, (i + 1) * sizeof(V)),
                         fpprt_read_ref(b, (i + 1) * sizeof(V)));
        if (c) return c;
      }
      return 0;
    }
    return a < b ? -1 : 1;
  }
  }
}

intptr_t fpp_hashv(V v) {
  if (v & 1) return UNTAGI(v);
  if (!v) return 0;
  uint32_t t = fpprt_typeid(v);
  switch (t) {
  case FPP_TID_STR: {
    intptr_t h = 5381;
    uint16_t *p = fpp_str_units(v);
    for (size_t i = 0; i < fpp_str_len(v); i++) h = h * 33 + p[i];
    return h & 0x3fffffff;
  }
  case FPP_TID_F64: return (intptr_t)fpp_unbox_f64(v);
  case FPP_TID_I64: return (intptr_t)fpp_unbox_i64(v);
  case FPP_TID_TUPLE: {
    intptr_t h = 17;
    for (size_t i = 0; i < fpprt_array_len(v); i++)
      h = h * 31 + fpp_hashv(fpp_tuple_get(v, i));
    return h & 0x3fffffff;
  }
  case FPP_TID_CONS: {
    intptr_t h = 23;
    V cur = v;
    while (fpp_is_tid(cur, FPP_TID_CONS)) {
      h = h * 31 + fpp_hashv(fpprt_read_ref(cur, sizeof(V)));
      cur = fpprt_read_ref(cur, 2 * sizeof(V));
    }
    return h & 0x3fffffff;
  }
  default: {
    int tc = fpp_tclass_of_(v);
    if (tc == FPP_TC_RECORD || tc == FPP_TC_CASE) {
      intptr_t h = 29 + (intptr_t)t;
      unsigned n = fpp_tfields_[t];
      for (unsigned i = 0; i < n; i++)
        h = h * 31 + fpp_hashv(fpprt_read_ref(v, (i + 1) * sizeof(V)));
      return h & 0x3fffffff;
    }
    return (intptr_t)fpprt_idhash(v);
  }
  }
}

/* ---- to-string ---------------------------------------------------------- */

V fpp_to_string(V x) {
  if (x & 1) {
    char buf[32];
    int n = snprintf(buf, sizeof buf, "%" PRIdPTR, (intptr_t)UNTAGI(x));
    return fpp_str_c(buf, (size_t)n);
  }
  if (!x) return fpp_str_c("", 0);
  uint32_t t = fpprt_typeid(x);
  if (t == FPP_TID_STR) return x;
  if (t == FPP_TID_F64) {
    char buf[40];
    int n = snprintf(buf, sizeof buf, "%g", fpp_unbox_f64(x));
    return fpp_str_c(buf, (size_t)n);
  }
  if (t == FPP_TID_I64) {
    char buf[32];
    int n = snprintf(buf, sizeof buf, "%" PRId64, fpp_unbox_i64(x));
    return fpp_str_c(buf, (size_t)n);
  }
  return fpp_str_c("<obj>", 5);
}

/* ---- init --------------------------------------------------------------- */

void fpp_lang_init(void) {
  fpprt_init(NULL);
  fpprt_register_type(FPP_TID_STR, (struct fpprt_type){
    2, FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "string" });
  fpprt_register_type(FPP_TID_F64, (struct fpprt_type){
    sizeof(double), FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "float" });
  fpprt_register_type(FPP_TID_I64, (struct fpprt_type){
    sizeof(int64_t), FPPRT_KIND_SCALAR_ARRAY, 0, NULL, "int64" });
  fpprt_register_type(FPP_TID_TUPLE, (struct fpprt_type){
    0, FPPRT_KIND_REF_ARRAY, 0, NULL, "tuple" });
  fpprt_register_type(FPP_TID_ARR, (struct fpprt_type){
    0, FPPRT_KIND_REF_ARRAY, 0, NULL, "array" });
  fpp_reg_struct(FPP_TID_CONS, 2, FPP_TC_OTHER, "cons");
  fpp_reg_struct(FPP_TID_CELL, 1, FPP_TC_OTHER, "cell");
  fpp_reg_clo(FPP_TID_PAP, 2);
}
