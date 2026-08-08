/* The OTHER side of the interop gate: an independently written C file with
 * its own declarations of the structs interop.fpp pins. If F++'s layout is
 * not the C ABI, the size check or the sums diverge. Pinning is IN-PLACE:
 * the address F++ hands over is the pinned array's real element storage,
 * pointer-wide (a nativeint on the F++ side; fpp_mem_base() is NULL and
 * only kept so base+offset arithmetic stays spellable). */
#include <stdint.h>
#include <math.h>

extern char *fpp_mem_base(void);

typedef struct { double x, y; } V2d;
typedef struct { float a, b, c; } V3f;
typedef struct { unsigned char r, g, b; } C3b;
typedef struct { double m; unsigned char t; } Mixed;
typedef struct { V2d o, d; } Ray;

int32_t c_check_sizes(int32_t v2d, int32_t v3f, int32_t c3b, int32_t mixed,
                      int32_t ray) {
    return v2d == (int32_t)sizeof(V2d) && v3f == (int32_t)sizeof(V3f)
        && c3b == (int32_t)sizeof(C3b) && mixed == (int32_t)sizeof(Mixed)
        && ray == (int32_t)sizeof(Ray);
}

double c_sum_v2d(intptr_t off, int32_t n) {
    V2d *p = (V2d *)(fpp_mem_base() + off);
    double s = 0.0;
    for (int32_t i = 0; i < n; i++) s += p[i].x + p[i].y;
    return s;
}

void c_scale_v2d(intptr_t off, int32_t n, double k) {
    V2d *p = (V2d *)(fpp_mem_base() + off);
    for (int32_t i = 0; i < n; i++) { p[i].x *= k; p[i].y *= k; }
}

int32_t c_sum_i32(intptr_t off, int32_t n) {
    int32_t *p = (int32_t *)(fpp_mem_base() + off);
    int32_t s = 0;
    for (int32_t i = 0; i < n; i++) s += p[i];
    return s;
}

double c_ray_len(intptr_t off) {
    Ray *r = (Ray *)(fpp_mem_base() + off);
    double dx = r->d.x - r->o.x, dy = r->d.y - r->o.y;
    return sqrt(dx * dx + dy * dy);
}
