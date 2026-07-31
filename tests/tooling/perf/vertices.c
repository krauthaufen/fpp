#include <stdio.h>
typedef struct { float x, y, z; } V3f;
#define N 1000000
#define R 20
static V3f v[N];
int main(int argc, char **argv) {
    float seed = (float)argc;
    for (int i = 0; i < N; i++) { v[i].x = seed; v[i].y = 2*seed; v[i].z = 3*seed; }
    double acc = 0;
    for (int r = 0; r < R; r++)
        for (int i = 0; i < N; i++) acc += (double)v[i].x + (double)v[i].y + (double)v[i].z;
    printf("%f\n", acc);
    return 0;
}
