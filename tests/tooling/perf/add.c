#include <stdio.h>
int main(int argc, char **argv) {
    double acc = 0, a = argc;
    for (int r = 0; r < 20; r++)
        for (int i = 0; i < 1000000; i++) acc += a;
    printf("%.0f\n", acc);
    return 0;
}
