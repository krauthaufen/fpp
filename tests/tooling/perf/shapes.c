#include <stdio.h>
typedef struct { float x, y, z; } V3f;      /* 12, align 4  */
typedef struct { double x, y; } V2d;        /* 16, align 8  */
typedef struct { unsigned char r,g,b,a; } C4b; /* 4, align 1 */
typedef struct { double m; unsigned char t; } Mix; /* 16, align 8 */
typedef struct { V2d lo, hi; } Box;         /* 32, nested   */
#define N 1000000
#define R 20
static V3f a[N]; static V2d b[N]; static C4b c[N]; static Mix d[N]; static Box e[N];
int main(int argc, char **argv) {
    double s = 0; int k = argc;
    for (int i = 0; i < N; i++) {
        a[i].x = k; a[i].y = 2*k; a[i].z = 3*k;
        b[i].x = k; b[i].y = 2*k;
        c[i].r = k; c[i].g = 2*k; c[i].b = 3*k; c[i].a = 4*k;
        d[i].m = k; d[i].t = k;
        e[i].lo.x = k; e[i].lo.y = k; e[i].hi.x = 2*k; e[i].hi.y = 2*k;
    }
    for (int r = 0; r < R; r++) for (int i = 0; i < N; i++) {
        s += (double)a[i].x + a[i].y + a[i].z;
        s += b[i].x + b[i].y;
        s += (double)c[i].r + c[i].g + c[i].b + c[i].a;
        s += d[i].m + (double)d[i].t;
        s += e[i].lo.x + e[i].hi.y;
    }
    printf("%.0f\n", s);
    return 0;
}
