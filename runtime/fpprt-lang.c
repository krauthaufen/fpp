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
  if (!clo || (clo & 1)) {
    fprintf(stderr, "fpp: apply to %s\n", clo ? "tagged value" : "null");
    fpp_not_emitted("apply to non-closure");
  }
  if (fpp_tclass_[fpprt_typeid(clo)] != FPP_TC_CLO) {
    fprintf(stderr, "fpp: apply to non-closure %s\n",
            fpprt_type_name(fpprt_typeid(clo)));
    fpp_not_emitted("apply to non-closure object");
  }
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

/* ---- interface dispatch ------------------------------------------------- */

static fpp_code_t *fpp_vt_ = NULL;
static size_t fpp_vt_tids_ = 0;
static int fpp_vt_slots_ = 0;

void fpp_vt_set(uint32_t tid, int slot, fpp_code_t fn) {
  if (tid >= fpp_vt_tids_ || slot >= fpp_vt_slots_) {
    size_t ntids = fpp_vt_tids_ ? fpp_vt_tids_ : 64;
    while (tid >= ntids) ntids *= 2;
    int nslots = fpp_vt_slots_ ? fpp_vt_slots_ : 32;
    while (slot >= nslots) nslots *= 2;
    fpp_code_t *nt = calloc(ntids * (size_t)nslots, sizeof(fpp_code_t));
    if (!nt) abort();
    for (size_t t = 0; t < fpp_vt_tids_; t++)
      for (int s = 0; s < fpp_vt_slots_; s++)
        nt[t * (size_t)nslots + s] = fpp_vt_[t * (size_t)fpp_vt_slots_ + s];
    free(fpp_vt_);
    fpp_vt_ = nt;
    fpp_vt_tids_ = ntids;
    fpp_vt_slots_ = nslots;
  }
  fpp_vt_[tid * (size_t)fpp_vt_slots_ + slot] = fn;
}

/* per-tid CompareTo dispatch: a CLASS that defines its own ordering must
 * order that way everywhere `compare` is asked — pointer order made the
 * Index machinery spin forever */
static int *fpp_cmp_slot_ = NULL;
static size_t fpp_cmp_cap_ = 0;
void fpp_reg_cmp(uint32_t tid, int slot) {
  if (tid >= fpp_cmp_cap_) {
    size_t cap = fpp_cmp_cap_ ? fpp_cmp_cap_ : 64;
    while (tid >= cap) cap *= 2;
    int *n = malloc(cap * sizeof(int));
    if (!n) abort();
    for (size_t i = 0; i < cap; i++) n[i] = i < fpp_cmp_cap_ ? fpp_cmp_slot_[i] : -1;
    free(fpp_cmp_slot_);
    fpp_cmp_slot_ = n;
    fpp_cmp_cap_ = cap;
  }
  fpp_cmp_slot_[tid] = slot;
}
static int fpp_cmp_slot_of_(uint32_t tid) {
  return tid < fpp_cmp_cap_ ? fpp_cmp_slot_[tid] : -1;
}

int fpp_vt_has(V obj, int slot) {
  if (!obj || (obj & 1)) return 0;
  uint32_t tid = fpprt_typeid(obj);
  return tid < fpp_vt_tids_ && slot < fpp_vt_slots_
      && fpp_vt_[tid * (size_t)fpp_vt_slots_ + slot] != NULL;
}

V fpp_vcall(V obj, int slot, V *args, size_t n) {
  (void)n;
  if (!obj || (obj & 1)) fpp_not_emitted("vcall on non-object");
  uint32_t tid = fpprt_typeid(obj);
  fpp_code_t fn = (tid < fpp_vt_tids_ && slot < fpp_vt_slots_)
    ? fpp_vt_[tid * (size_t)fpp_vt_slots_ + slot] : NULL;
  if (!fn) {
    fprintf(stderr, "fpp: no vtable entry (tid %u slot %d)\n", tid, slot);
    abort();
  }
  return fn(obj, args);
}

V fpp_arr_zeroed(int kind, size_t n) {
  FPPRT_FRAME(f, 1);
  f_slots[0] = fpprt_alloc_array(FPP_TID_ARR, n);
  if (kind == 1) {
    for (size_t i = 0; i < n; i++)
      ((uintptr_t *)f_slots[0])[i + 2] = TAGI(0);   /* tagged: no barrier */
  } else if (kind == 2) {
    for (size_t i = 0; i < n; i++)
      fpp_arr_set(f_slots[0], i, fpp_box_f64(0.0));
  } else if (kind == 3) {
    for (size_t i = 0; i < n; i++)
      fpp_arr_set(f_slots[0], i, fpp_box_i64(0));
  }
  V r = f_slots[0];
  FPPRT_LEAVE(f);
  return r;
}

/* ---- builtin seq enumerators -------------------------------------------- */
/* [tag][src][idx] — idx tagged; for a LIST src walks the cons chain */

V fpp_seq_getenum(V self, V *args) {
  (void)args;
  FPPRT_FRAME(f, 1);
  f_slots[0] = self;
  V e = fpprt_alloc(FPP_TID_ENUM);
  fpprt_write_ref(e, 1 * sizeof(V), f_slots[0]);
  ((uintptr_t *)e)[2] = TAGI(-1);
  FPPRT_LEAVE(f);
  return e;
}

V fpp_enum_movenext(V self, V *args) {
  (void)args;
  V src = fpprt_read_ref(self, 1 * sizeof(V));
  if (src == 0) return TAGI(0);
  if (fpp_is_tid(src, FPP_TID_ARR) || fpp_is_tid(src, FPP_TID_STR)
      || fpp_is_tid(src, FPP_TID_TUPLE)) {
    intptr_t i = UNTAGI(((uintptr_t *)self)[2]) + 1;
    ((uintptr_t *)self)[2] = TAGI(i);
    return TAGI((size_t)i < fpprt_array_len(src));
  }
  /* a list: idx == -1 means "before first" — first MoveNext stays on src,
   * later ones advance the chain */
  if (((intptr_t)UNTAGI(((uintptr_t *)self)[2])) < 0) {
    ((uintptr_t *)self)[2] = TAGI(0);
    return TAGI(fpp_is_tid(src, FPP_TID_CONS));
  }
  V next = fpp_is_tid(src, FPP_TID_CONS) ? fpprt_read_ref(src, 2 * sizeof(V)) : 0;
  fpprt_write_ref(self, 1 * sizeof(V), next);
  return TAGI(fpp_is_tid(next, FPP_TID_CONS));
}

V fpp_enum_current(V self, V *args) {
  (void)args;
  V src = fpprt_read_ref(self, 1 * sizeof(V));
  if (fpp_is_tid(src, FPP_TID_CONS))
    return fpprt_read_ref(src, 1 * sizeof(V));
  if (fpp_is_tid(src, FPP_TID_STR)) {
    intptr_t i = UNTAGI(((uintptr_t *)self)[2]);
    return TAGI(fpp_str_units(src)[i]);
  }
  intptr_t i = UNTAGI(((uintptr_t *)self)[2]);
  return fpprt_read_ref(src, (uint32_t)((i + 2) * sizeof(V)));
}

V fpp_enum_dispose(V self, V *args) {
  (void)self; (void)args;
  return VUNIT;
}

/* ---- exceptions --------------------------------------------------------- */

uint32_t fpp_failure_tid_ = 0;

V fpp_failure(const char *msg, size_t len) {
  FPPRT_FRAME(f, 1);
  f_slots[0] = fpp_str_c(msg, len);
  V r = f_slots[0];
  if (fpp_failure_tid_) {
    r = fpprt_alloc(fpp_failure_tid_);
    fpprt_write_ref(r, sizeof(V), f_slots[0]);
  }
  FPPRT_LEAVE(f);
  return r;
}

const char *fpp_hlog_site_[64];
char fpp_hlog_kind_[64];
void *fpp_hlog_ptr_[64];
unsigned fpp_hlog_n_ = 0;
void fpp_hlog_dump(void) {
  fflush(stdout);
  unsigned start = fpp_hlog_n_ > 40 ? fpp_hlog_n_ - 40 : 0;
  for (unsigned i = start; i < fpp_hlog_n_; i++)
    fprintf(stderr, "  hlog %c %p %s\n", fpp_hlog_kind_[i & 63],
            fpp_hlog_ptr_[i & 63], fpp_hlog_site_[i & 63]);
}

void fpp_raise(V payload) {
  fpp_hlog_('R', fpp_handler_top_ ? fpp_handler_top_->site : "none",
            (void *)fpp_handler_top_);
#ifdef FPP_RAISE_DEBUG
  {
    int depth = 0;
    for (struct fpp_handler *h = fpp_handler_top_; h; h = h->prev) depth++;
    fprintf(stderr, "[raise depth=%d payload=%s]\n", depth,
            (payload && !(payload & 1))
              ? fpprt_type_name(fpprt_typeid(payload)) : "tagged");
  }
#endif
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
  fpp_raise(fpp_failure("match failure", 13));
}

/* ---- structural equality / hash / compare ------------------------------ */

static int fpp_tclass_of_(V v) {
  uint32_t tid = fpprt_typeid(v);
  return tid < fpp_tmeta_cap_ ? fpp_tclass_[tid] : FPP_TC_OTHER;
}

int fpp_eqv(V a, V b) {
  /* the identity fast path must not answer for floats: the same NaN box
   * still compares UNEQUAL to itself */
  if (a == b && !((a && !(a & 1)) && fpprt_typeid(a) == FPP_TID_F64)) return 1;
  if (a == b) return fpp_unbox_f64(a) == fpp_unbox_f64(b);
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
    if (tc == FPP_TC_CLASS) {
      int slot = fpp_cmp_slot_of_(ta);
      if (slot >= 0) {
        V arg = b;
        return (int)UNTAGI(fpp_vcall(a, slot, &arg, 1));
      }
    }
    /* no defined ordering: order by IDENTITY HASH, which is stable for an
     * object's whole life — raw pointers move with the collector and vary
     * with ASLR, and a comparison that changes between calls corrupts
     * every ordered structure built on it */
    {
      intptr_t ha = fpprt_idhash(a), hb = fpprt_idhash(b);
      return ha < hb ? -1 : ha > hb ? 1 : (a < b ? -1 : a > b ? 1 : 0);
    }
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

V fpp_f64_to_string(V x) {
  /* mirrors the wasm backend's formatting: shortest %.17g that reads back,
   * tried at increasing precision — parity decides if this needs refining */
  double d = fpp_unbox_f64(x);
  char buf[40];
  int n = 0;
  for (int prec = 1; prec <= 17; prec++) {
    n = snprintf(buf, sizeof buf, "%.*g", prec, d);
    double back = strtod(buf, NULL);
    if (back == d) break;
  }
  return fpp_str_c(buf, (size_t)n);
}

/* ---- generic arithmetic: the oracle's $addv family ---------------------- */

/* representational drift is REAL in the uniform pipeline: a generic zero
 * seeds as a tagged int and meets int64 boxes — same source-level type,
 * two runtime spellings. The dispatch coerces numeric mixes. */
static inline int fpp_numeric_(V v) {
  return (v & 1) || fpp_is_tid(v, FPP_TID_F64) || fpp_is_tid(v, FPP_TID_I64);
}
static inline double fpp_as_f64_(V v) {
  if (v & 1) return (double)UNTAGI(v);
  if (fpp_is_tid(v, FPP_TID_F64)) return fpp_unbox_f64(v);
  return (double)fpp_unbox_i64(v);
}
static inline int64_t fpp_as_i64_(V v) {
  if (v & 1) return (int64_t)UNTAGI(v);
  return fpp_unbox_i64(v);
}

#define FPP_ARITH2(name, op, strcase)                                   \
V name(V a, V b) {                                                      \
  if ((a & 1) && (b & 1))                                               \
    return TAGI((intptr_t)(int32_t)((int32_t)UNTAGI(a) op (int32_t)UNTAGI(b))); \
  if (fpp_is_tid(a, FPP_TID_F64) && fpp_is_tid(b, FPP_TID_F64))         \
    return fpp_box_f64(fpp_unbox_f64(a) op fpp_unbox_f64(b));           \
  if (fpp_is_tid(a, FPP_TID_I64) && fpp_is_tid(b, FPP_TID_I64))         \
    return fpp_box_i64(fpp_unbox_i64(a) op fpp_unbox_i64(b));           \
  if (fpp_numeric_(a) && fpp_numeric_(b)) {                             \
    if (fpp_is_tid(a, FPP_TID_F64) || fpp_is_tid(b, FPP_TID_F64))       \
      return fpp_box_f64(fpp_as_f64_(a) op fpp_as_f64_(b));             \
    return fpp_box_i64(fpp_as_i64_(a) op fpp_as_i64_(b));               \
  }                                                                     \
  strcase                                                               \
  fprintf(stderr, "fpp: mixed arith a=%s b=%s\n",                       \
          (a & 1) ? "tagged" : a ? fpprt_type_name(fpprt_typeid(a)) : "null", \
          (b & 1) ? "tagged" : b ? fpprt_type_name(fpprt_typeid(b)) : "null"); \
  fpp_not_emitted("generic arith on mixed values");                     \
  return 0;                                                             \
}
FPP_ARITH2(fpp_addv, +,
  if (fpp_is_tid(a, FPP_TID_STR) && fpp_is_tid(b, FPP_TID_STR))
    return fpp_str_concat(a, b);)
FPP_ARITH2(fpp_subv, -, )
FPP_ARITH2(fpp_mulv, *, )

V fpp_divv(V a, V b) {
  if ((a & 1) && (b & 1)) {
    if (UNTAGI(b) == 0) fpp_raise(fpp_failure("division by zero", 16));
    return TAGI((intptr_t)(int32_t)((int32_t)UNTAGI(a) / (int32_t)UNTAGI(b)));
  }
  if (fpp_is_tid(a, FPP_TID_F64) && fpp_is_tid(b, FPP_TID_F64))
    return fpp_box_f64(fpp_unbox_f64(a) / fpp_unbox_f64(b));
  if (fpp_is_tid(a, FPP_TID_I64) && fpp_is_tid(b, FPP_TID_I64))
    return fpp_box_i64(fpp_unbox_i64(a) / fpp_unbox_i64(b));
  fpp_not_emitted("generic div on mixed values");
  return 0;
}
V fpp_modv(V a, V b) {
  if ((a & 1) && (b & 1)) {
    if (UNTAGI(b) == 0) fpp_raise(fpp_failure("division by zero", 16));
    return TAGI((intptr_t)(int32_t)((int32_t)UNTAGI(a) % (int32_t)UNTAGI(b)));
  }
  if (fpp_is_tid(a, FPP_TID_F64) && fpp_is_tid(b, FPP_TID_F64))
    return fpp_box_f64(__builtin_fmod(fpp_unbox_f64(a), fpp_unbox_f64(b)));
  if (fpp_is_tid(a, FPP_TID_I64) && fpp_is_tid(b, FPP_TID_I64))
    return fpp_box_i64(fpp_unbox_i64(a) % fpp_unbox_i64(b));
  fpp_not_emitted("generic mod on mixed values");
  return 0;
}

V fpp_negv(V a) {
  if (a & 1) return TAGI(-UNTAGI(a));
  if (fpp_is_tid(a, FPP_TID_F64)) return fpp_box_f64(-fpp_unbox_f64(a));
  if (fpp_is_tid(a, FPP_TID_I64)) return fpp_box_i64(-fpp_unbox_i64(a));
  fpp_not_emitted("generic negation");
  return 0;
}

V fpp_absv(V a) {
  if (a & 1) { intptr_t v = UNTAGI(a); return TAGI(v < 0 ? -v : v); }
  if (fpp_is_tid(a, FPP_TID_F64))
    return fpp_box_f64(__builtin_fabs(fpp_unbox_f64(a)));
  if (fpp_is_tid(a, FPP_TID_I64)) {
    int64_t v = fpp_unbox_i64(a);
    return fpp_box_i64(v < 0 ? -v : v);
  }
  fpp_not_emitted("abs");
  return 0;
}

V fpp_signv(V a) {
  if (a & 1) { intptr_t v = UNTAGI(a); return TAGI(v < 0 ? -1 : v > 0 ? 1 : 0); }
  if (fpp_is_tid(a, FPP_TID_F64)) {
    double v = fpp_unbox_f64(a);
    return TAGI(v < 0 ? -1 : v > 0 ? 1 : 0);
  }
  if (fpp_is_tid(a, FPP_TID_I64)) {
    int64_t v = fpp_unbox_i64(a);
    return TAGI(v < 0 ? -1 : v > 0 ? 1 : 0);
  }
  fpp_not_emitted("sign");
  return 0;
}

double fpp_round_even(double x) {
  /* .NET Math.Round: banker's rounding */
  double r = __builtin_nearbyint(x);
  return r == 0.0 ? 0.0 : r;   /* normalize -0 */
}

/* ---- show and the print family ------------------------------------------ */

V fpp_showv(V x) {
  /* the generic renderer; grows toward the oracle's $showv as parity
   * demands (records, unions, lists) */
  return fpp_to_string(x);
}

void fpp_print_any(V x) {
  fpp_print(fpp_showv(x));
}

void fpp_print_u32(V x) {
  char buf[16];
  int n = snprintf(buf, sizeof buf, "%u", (unsigned)UNTAGI(x));
  V s = fpp_str_c(buf, (size_t)n);
  fpp_print(s);
}

/* ---- init --------------------------------------------------------------- */

V fpp_cmpv_clo_ = 0;
static V fpp_cmpv_code_(V self, V *args) {
  (void)self;
  return TAGI(fpp_cmpv(args[0], args[1]));
}

void fpp_lang_init(void) {
  /* FPP_HEAP_MB: initial heap for compiled programs. The growable policy
   * still applies; a bigger floor keeps a copying collector out of
   * near-boundary thrash on allocation-heavy workloads. */
  struct fpprt_opts opts = { 0 };
  const char *mb = getenv("FPP_HEAP_MB");
  if (mb && mb[0]) opts.heap_bytes = (size_t)strtoull(mb, NULL, 10) << 20;
  fpprt_init(opts.heap_bytes ? &opts : NULL);
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
  /* [tag][src][idx]: idx is a TAGGED int, so both fields sit on the map
   * and the tracer skips the tagged one */
  fpp_reg_struct(FPP_TID_ENUM, 2, FPP_TC_OTHER, "enum");
  fpp_reg_struct(FPP_TID_CELL, 1, FPP_TC_OTHER, "cell");
  fpp_reg_clo(FPP_TID_PAP, 2);
  fpp_reg_clo(FPP_TID_CMPCLO, 0);
  fpp_cmpv_clo_ = fpp_clo_new(FPP_TID_CMPCLO, fpp_cmpv_code_, 2, 0);
  fpprt_add_static_roots(&fpp_cmpv_clo_, 1);
}

/* ---- string methods: the $str.* family, .NET semantics ------------------ */

static int fpp_str_index_of_(V s, V what, intptr_t start, int last) {
  size_t n = fpp_str_len(s);
  uint16_t *u = fpp_str_units(s);
  if (what & 1) {
    uint16_t c = (uint16_t)UNTAGI(what);
    if (last) {
      for (intptr_t i = (intptr_t)n - 1; i >= start; i--)
        if (u[i] == c) return (int)i;
    } else {
      for (size_t i = (size_t)start; i < n; i++)
        if (u[i] == c) return (int)i;
    }
    return -1;
  }
  size_t m = fpp_str_len(what);
  uint16_t *w = fpp_str_units(what);
  if (m == 0) return last ? (int)n : (int)start;
  if (m > n) return -1;
  if (last) {
    for (intptr_t i = (intptr_t)(n - m); i >= start; i--)
      if (memcmp(u + i, w, m * 2) == 0) return (int)i;
  } else {
    for (size_t i = (size_t)start; i + m <= n; i++)
      if (memcmp(u + i, w, m * 2) == 0) return (int)i;
  }
  return -1;
}

static V fpp_str_sub_(V s, size_t start, size_t len) {
  FPPRT_FRAME(f, 1);
  f_slots[0] = s;
  V r = fpprt_alloc_array(FPP_TID_STR, len);
  memcpy(fpp_str_units(r), fpp_str_units(f_slots[0]) + start, len * 2);
  FPPRT_LEAVE(f);
  return r;
}

static int fpp_str_ws_(uint16_t c) {
  return c == ' ' || c == '\t' || c == '\n' || c == '\r'
      || c == '\v' || c == '\f' || c == 0xa0;
}

V fpp_str_method(const char *m, V recv, V *args, size_t nargs) {
  size_t n = fpp_str_len(recv);
  uint16_t *u = fpp_str_units(recv);
  if (!strcmp(m, "Contains"))
    return TAGI(fpp_str_index_of_(recv, args[0], 0, 0) >= 0);
  if (!strcmp(m, "IndexOf")) {
    intptr_t start = nargs > 1 ? UNTAGI(args[1]) : 0;
    return TAGI(fpp_str_index_of_(recv, args[0], start, 0));
  }
  if (!strcmp(m, "LastIndexOf"))
    return TAGI(fpp_str_index_of_(recv, args[0], 0, 1));
  if (!strcmp(m, "StartsWith")) {
    size_t mlen = fpp_str_len(args[0]);
    return TAGI(mlen <= n && memcmp(u, fpp_str_units(args[0]), mlen * 2) == 0);
  }
  if (!strcmp(m, "EndsWith")) {
    size_t mlen = fpp_str_len(args[0]);
    return TAGI(mlen <= n
                && memcmp(u + n - mlen, fpp_str_units(args[0]), mlen * 2) == 0);
  }
  if (!strcmp(m, "Substring")) {
    size_t start = (size_t)UNTAGI(args[0]);
    size_t len = nargs > 1 ? (size_t)UNTAGI(args[1]) : n - start;
    if (start > n || start + len > n)
      fpp_raise(fpp_failure("Substring out of range", 22));
    return fpp_str_sub_(recv, start, len);
  }
  if (!strcmp(m, "Remove")) {
    size_t start = (size_t)UNTAGI(args[0]);
    size_t cut = nargs > 1 ? (size_t)UNTAGI(args[1]) : n - start;
    FPPRT_FRAME(f, 1);
    f_slots[0] = recv;
    V r = fpprt_alloc_array(FPP_TID_STR, n - cut);
    memcpy(fpp_str_units(r), fpp_str_units(f_slots[0]), start * 2);
    memcpy(fpp_str_units(r) + start, fpp_str_units(f_slots[0]) + start + cut,
           (n - start - cut) * 2);
    FPPRT_LEAVE(f);
    return r;
  }
  if (!strcmp(m, "Insert")) {
    size_t at = (size_t)UNTAGI(args[0]);
    FPPRT_FRAME(f, 2);
    f_slots[0] = recv;
    f_slots[1] = args[1];
    size_t mlen = fpp_str_len(f_slots[1]);
    V r = fpprt_alloc_array(FPP_TID_STR, n + mlen);
    memcpy(fpp_str_units(r), fpp_str_units(f_slots[0]), at * 2);
    memcpy(fpp_str_units(r) + at, fpp_str_units(f_slots[1]), mlen * 2);
    memcpy(fpp_str_units(r) + at + mlen, fpp_str_units(f_slots[0]) + at,
           (n - at) * 2);
    FPPRT_LEAVE(f);
    return r;
  }
  if (!strcmp(m, "Replace")) {
    /* build by scanning; args may be chars or strings */
    FPPRT_FRAME(f, 3);
    f_slots[0] = recv;
    f_slots[1] = args[0];
    f_slots[2] = args[1];
    if ((f_slots[1] & 1) && (f_slots[2] & 1)) {
      V r = fpp_str_sub_(f_slots[0], 0, n);
      uint16_t from = (uint16_t)UNTAGI(f_slots[1]);
      uint16_t to = (uint16_t)UNTAGI(f_slots[2]);
      for (size_t i = 0; i < n; i++)
        if (fpp_str_units(r)[i] == from) fpp_str_units(r)[i] = to;
      FPPRT_LEAVE(f);
      return r;
    }
    size_t flen = fpp_str_len(f_slots[1]);
    size_t tlen = fpp_str_len(f_slots[2]);
    /* count matches */
    size_t count = 0;
    for (size_t i = 0; flen && i + flen <= n;) {
      if (memcmp(fpp_str_units(f_slots[0]) + i, fpp_str_units(f_slots[1]),
                 flen * 2) == 0) { count++; i += flen; }
      else i++;
    }
    V r = fpprt_alloc_array(FPP_TID_STR, n + count * tlen - count * flen);
    uint16_t *out = fpp_str_units(r);
    size_t k = 0;
    for (size_t i = 0; i < n;) {
      if (flen && i + flen <= n
          && memcmp(fpp_str_units(f_slots[0]) + i, fpp_str_units(f_slots[1]),
                    flen * 2) == 0) {
        memcpy(out + k, fpp_str_units(f_slots[2]), tlen * 2);
        k += tlen;
        i += flen;
      } else out[k++] = fpp_str_units(f_slots[0])[i++];
    }
    FPPRT_LEAVE(f);
    return r;
  }
  if (!strcmp(m, "ToUpper") || !strcmp(m, "ToLower")) {
    int up = m[2] == 'U';
    FPPRT_FRAME(f, 1);
    f_slots[0] = recv;
    V r = fpp_str_sub_(f_slots[0], 0, n);
    for (size_t i = 0; i < n; i++) {
      uint16_t c = fpp_str_units(r)[i];
      if (up && c >= 'a' && c <= 'z') fpp_str_units(r)[i] = c - 32;
      if (!up && c >= 'A' && c <= 'Z') fpp_str_units(r)[i] = c + 32;
    }
    FPPRT_LEAVE(f);
    return r;
  }
  if (!strcmp(m, "Trim") || !strcmp(m, "TrimStart") || !strcmp(m, "TrimEnd")) {
    size_t a = 0, b = n;
    int doStart = strcmp(m, "TrimEnd") != 0;
    int doEnd = strcmp(m, "TrimStart") != 0;
    if (doStart) while (a < b && fpp_str_ws_(u[a])) a++;
    if (doEnd) while (b > a && fpp_str_ws_(u[b - 1])) b--;
    return fpp_str_sub_(recv, a, b - a);
  }
  if (!strcmp(m, "PadLeft") || !strcmp(m, "PadRight")) {
    size_t want = (size_t)UNTAGI(args[0]);
    uint16_t fill = nargs > 1 ? (uint16_t)UNTAGI(args[1]) : ' ';
    if (want <= n) return recv;
    FPPRT_FRAME(f, 1);
    f_slots[0] = recv;
    V r = fpprt_alloc_array(FPP_TID_STR, want);
    size_t pad = want - n;
    if (m[3] == 'L') {
      for (size_t i = 0; i < pad; i++) fpp_str_units(r)[i] = fill;
      memcpy(fpp_str_units(r) + pad, fpp_str_units(f_slots[0]), n * 2);
    } else {
      memcpy(fpp_str_units(r), fpp_str_units(f_slots[0]), n * 2);
      for (size_t i = 0; i < pad; i++) fpp_str_units(r)[n + i] = fill;
    }
    FPPRT_LEAVE(f);
    return r;
  }
  if (!strcmp(m, "ToCharArray")) {
    FPPRT_FRAME(f, 1);
    f_slots[0] = recv;
    V r = fpp_arr_new(n);
    for (size_t i = 0; i < n; i++)
      ((uintptr_t *)r)[i + 2] = TAGI(fpp_str_units(f_slots[0])[i]);
    FPPRT_LEAVE(f);
    return r;
  }
  if (!strcmp(m, "Split")) {
    /* split on one char (tagged) — .NET drops nothing by default */
    FPPRT_FRAME(f, 2);
    f_slots[0] = recv;
    uint16_t sep = (uint16_t)UNTAGI(args[0]);
    size_t parts = 1;
    for (size_t i = 0; i < n; i++) if (u[i] == sep) parts++;
    f_slots[1] = fpp_arr_new(parts);
    size_t start = 0, k = 0;
    for (size_t i = 0; i <= n; i++) {
      if (i == n || fpp_str_units(f_slots[0])[i] == sep) {
        V piece = fpp_str_sub_(f_slots[0], start, i - start);
        fpp_arr_set(f_slots[1], k++, piece);
        start = i + 1;
      }
    }
    V r = f_slots[1];
    FPPRT_LEAVE(f);
    return r;
  }
  fprintf(stderr, "fpp: string method %s\n", m);
  fpp_not_emitted("string method");
  return 0;
}
