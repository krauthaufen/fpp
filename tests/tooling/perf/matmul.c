// Dense square matrix multiply over flat double arrays: the classic
// triple loop, indexed with i*n+k arithmetic rather than a counter the
// compiler can bound. Nothing allocates after setup, so it isolates
// float FMA-less arithmetic and strided loads from everything else.
#include <stdio.h>
#include <stdlib.h>

#define N 320

int main(void) {
    double *a = malloc(sizeof(double) * N * N);
    double *b = malloc(sizeof(double) * N * N);
    double *c = malloc(sizeof(double) * N * N);
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) {
            a[i * N + j] = (double)((i + j) % 7);
            b[i * N + j] = (double)((i * 2 + j) % 5);
            c[i * N + j] = 0.0;
        }
    for (int rep = 0; rep < 3; rep++)
        for (int i = 0; i < N; i++)
            for (int k = 0; k < N; k++) {
                double aik = a[i * N + k];
                for (int j = 0; j < N; j++)
                    c[i * N + j] += aik * b[k * N + j];
            }
    double s = 0.0;
    for (int i = 0; i < N * N; i++) s += c[i];
    printf("%.0f\n", s);
    return 0;
}
