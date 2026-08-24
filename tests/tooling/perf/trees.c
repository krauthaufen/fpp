/* The C twin of trees.fpp. Nodes come from a bump arena that is RESET after
 * each tree is checked — the C equivalent of "this garbage died young", and
 * about as cheap as reclamation gets. */
#include <stdio.h>
#include <stdlib.h>

typedef struct Node { struct Node *l, *r; } Node;

#define ARENA (1 << 24)
static Node *arena; static long arena_used = 0;
static Node *alloc_node(void) { return &arena[arena_used++]; }

static Node *make(int d) {
    if (d == 0) return 0;
    Node *n = alloc_node();
    n->l = make(d - 1);
    n->r = make(d - 1);
    return n;
}

static int check(Node *t) { return t ? 1 + check(t->l) + check(t->r) : 1; }

#define MAXD 18
#define MIND 4

int main(void) {
    arena = malloc(sizeof(Node) * ARENA);
    long long acc = 0;
    long base;
    Node *longLived = make(MAXD);
    base = arena_used;
    for (int d = MIND; d <= MAXD; d += 2) {
        long iters = 1L << (MAXD - d + MIND);
        int sum = 0;
        for (long i = 0; i < iters; i++) {
            arena_used = base;              /* drop the previous tree */
            sum += check(make(d));
        }
        acc += sum;
    }
    arena_used = base;
    acc += check(longLived);
    printf("%.0f\n", (double)acc);
    return 0;
}
