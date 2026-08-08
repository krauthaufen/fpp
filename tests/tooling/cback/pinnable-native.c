#include <stdint.h>
typedef struct { double x, y; } V2;
double c_sum2(intptr_t p, int n) {
    V2 *v = (V2 *)p;
    double s = 0;
    for (int i = 0; i < n; i++) s += v[i].x + v[i].y;
    return s;
}

int c_first(intptr_t p) { return ((unsigned char *)p)[0]; }

void c_bump(intptr_t p) { ((V2 *)p)->x += 10.0; }
