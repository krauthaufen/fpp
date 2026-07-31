#include <stdio.h>
#include <stddef.h>
typedef struct { float a, b, c; } V3f;
typedef struct { double x, y; } V2d;
typedef struct { float a, b; } V2f;
typedef struct { int a, b, c; } V3i;
typedef struct { double x, y, z; } V3d;
int main(void) {
    V3f a3[2]; V2d a2[2]; V2f f2[2]; V3i i3[2]; V3d d3[2];
    printf("V3f sizeof=%zu stride=%zu\n", sizeof(V3f), (size_t)((char*)&a3[1]-(char*)&a3[0]));
    printf("V2d sizeof=%zu stride=%zu\n", sizeof(V2d), (size_t)((char*)&a2[1]-(char*)&a2[0]));
    printf("V2f sizeof=%zu stride=%zu\n", sizeof(V2f), (size_t)((char*)&f2[1]-(char*)&f2[0]));
    printf("V3i sizeof=%zu stride=%zu\n", sizeof(V3i), (size_t)((char*)&i3[1]-(char*)&i3[0]));
    printf("V3d sizeof=%zu stride=%zu\n", sizeof(V3d), (size_t)((char*)&d3[1]-(char*)&d3[0]));
    return 0;
}
