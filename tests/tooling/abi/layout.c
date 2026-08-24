#include <stdio.h>
#include <stddef.h>
typedef struct { float a, b, c; } V3f;
typedef struct { double x, y; } V2d;
typedef struct { float a, b; } V2f;
typedef struct { int a, b, c; } V3i;
typedef struct { double x, y, z; } V3d;
typedef struct { unsigned char r, g, b; } C3b;
typedef struct { unsigned char r, g, b, a; } C4b;
typedef struct { double m; unsigned char t; } Mixed;
typedef struct { char c; } Ch1;
/* NESTED structs: a struct field is laid out INLINE, exactly as C does it —
   this is interop surface, not an optimisation. */
typedef struct { V2d lo, hi; } Box;
typedef struct { V3f p; unsigned char t; } Tagged;
typedef struct { C4b c; float f; } Small;
int main(void) {
    V3f a3[2]; V2d a2[2]; V2f f2[2]; V3i i3[2]; V3d d3[2]; C3b c3[2]; C4b c4[2]; Mixed mx[2];
    Box bx[2]; Tagged tg[2]; Small sm[2];
    printf("V3f sizeof=%zu stride=%zu\n", sizeof(V3f), (size_t)((char*)&a3[1]-(char*)&a3[0]));
    printf("V2d sizeof=%zu stride=%zu\n", sizeof(V2d), (size_t)((char*)&a2[1]-(char*)&a2[0]));
    printf("V2f sizeof=%zu stride=%zu\n", sizeof(V2f), (size_t)((char*)&f2[1]-(char*)&f2[0]));
    printf("V3i sizeof=%zu stride=%zu\n", sizeof(V3i), (size_t)((char*)&i3[1]-(char*)&i3[0]));
    printf("V3d sizeof=%zu stride=%zu\n", sizeof(V3d), (size_t)((char*)&d3[1]-(char*)&d3[0]));
    printf("C3b sizeof=%zu stride=%zu\n", sizeof(C3b), (size_t)((char*)&c3[1]-(char*)&c3[0]));
    printf("C4b sizeof=%zu stride=%zu\n", sizeof(C4b), (size_t)((char*)&c4[1]-(char*)&c4[0]));
    printf("Mixed sizeof=%zu stride=%zu\n", sizeof(Mixed), (size_t)((char*)&mx[1]-(char*)&mx[0]));
    printf("Box sizeof=%zu stride=%zu offs=%zu,%zu\n", sizeof(Box), (size_t)((char*)&bx[1]-(char*)&bx[0]),
           offsetof(Box, lo), offsetof(Box, hi));
    printf("Tagged sizeof=%zu stride=%zu offs=%zu,%zu\n", sizeof(Tagged), (size_t)((char*)&tg[1]-(char*)&tg[0]),
           offsetof(Tagged, p), offsetof(Tagged, t));
    printf("Small sizeof=%zu stride=%zu offs=%zu,%zu\n", sizeof(Small), (size_t)((char*)&sm[1]-(char*)&sm[0]),
           offsetof(Small, c), offsetof(Small, f));
    return 0;
}
