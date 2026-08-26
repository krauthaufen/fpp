/* The C twin of trees.fpp: malloc per node, and the tree freed when it goes
 * out of scope — what a C programmer who owns the lifetime writes.
 *
 * This replaced a bump-arena twin that dropped a whole tree by resetting a
 * pointer. That is not memory management, and against it the collected
 * languages looked 2.9x slow while the real gap is 4%. */
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
