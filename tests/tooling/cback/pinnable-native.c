typedef struct { double x, y; } V2;
double c_sum2(long long p, int n) {
    V2 *v = (V2 *)p;
    double s = 0;
    for (int i = 0; i < n; i++) s += v[i].x + v[i].y;
    return s;
}

int c_first(long long p) { return ((unsigned char *)p)[0]; }
