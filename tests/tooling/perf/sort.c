/* The C twin of sort.fpp: the same median-of-middle quicksort, same keys. */
#include <stdio.h>
#define N 2000000
#define REPS 6
static int a[N];

static void qsort_(int lo, int hi) {
    if (lo < hi) {
        int mid = lo + (hi - lo) / 2;
        int p = a[mid];
        int i = lo, j = hi;
        while (i <= j) {
            while (a[i] < p) i++;
            while (a[j] > p) j--;
            if (i <= j) { int t = a[i]; a[i] = a[j]; a[j] = t; i++; j--; }
        }
        if (lo < j) qsort_(lo, j);
        if (i < hi) qsort_(i, hi);
    }
}

int main(void) {
    long long acc = 0;
    for (int rep = 0; rep < REPS; rep++) {
        unsigned s = 2463534242u;
        for (int i = 0; i < N; i++) {
            s ^= s << 13; s ^= s >> 17; s ^= s << 5;
            a[i] = (int)(s % 10000000u);
        }
        qsort_(0, N - 1);
        acc += a[0] + a[N / 2] + a[N - 1];
    }
    printf("%.0f\n", (double)acc);
    return 0;
}
