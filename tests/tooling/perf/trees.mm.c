/* trees, with REAL memory management: malloc per node, and the tree freed
 * when it goes out of scope. The arena twin beside this one bump-allocates
 * and drops a pointer, which is not memory management at all — it is what
 * makes the collected languages look 3x slower than "C". This is what a C
 * programmer who owns the lifetime actually writes. */
#include <stdio.h>
#include <stdlib.h>

typedef struct Node { struct Node *l, *r; } Node;

static Node *make(int d) {
    if (d == 0) return NULL;
    Node *n = malloc(sizeof(Node));
    n->l = make(d - 1);
    n->r = make(d - 1);
    return n;
}

static void destroy(Node *t) {
    if (t) { destroy(t->l); destroy(t->r); free(t); }
}

static int check(Node *t) { return t ? 1 + check(t->l) + check(t->r) : 1; }

#define MAXD 18
#define MIND 4

int main(void) {
    long long acc = 0;
    Node *longLived = make(MAXD);
    for (int d = MIND; d <= MAXD; d += 2) {
        long iters = 1L << (MAXD - d + MIND);
        int sum = 0;
        for (long i = 0; i < iters; i++) {
            Node *t = make(d);
            sum += check(t);
            destroy(t);                 /* the lifetime ends here */
        }
        acc += sum;
    }
    acc += check(longLived);
    destroy(longLived);
    printf("%.0f\n", (double)acc);
    return 0;
}
