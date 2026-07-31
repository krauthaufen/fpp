#include <stdio.h>
typedef struct { float x, y, z; } V3f;
#define N 1000000
static V3f v[N];
int main(int argc, char **argv) {
    for (int i = 0; i < N; i++) { v[i].x = argc; v[i].y = 2*argc; v[i].z = 3*argc; }
    double acc = 0;
    for (int r = 0; r < 20; r++)
        for (int i = 0; i < N; i++) acc += (double)v[i].x;
    printf("%.0f\n", acc);
    return 0;
}
