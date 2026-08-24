/* The C twin of avl.fpp: the same persistent AVL, the same xorshift keys.
 *
 * The nodes are never freed. That is not sloppiness — the F++ and F# twins do
 * not free them either, they drop them and let the collector deal with it, so
 * a bump allocator with no reclamation is the closest C equivalent of "the
 * program never says free". It does mean this benchmark flatters C's memory
 * management, which is the point: it shows what the collector costs. */
#include <stdio.h>
#include <stdlib.h>

typedef struct Node {
    struct Node *l, *r;
    int k, v, h;
} Node;

/* a bump arena: malloc per node would measure glibc's allocator, not the
 * algorithm, and the twins allocate from a nursery in one pointer bump too */
#define ARENA (1 << 22)
static Node *chunk; static int chunk_used = ARENA;

static Node *alloc_node(void) {
    if (chunk_used == ARENA) { chunk = malloc(sizeof(Node) * ARENA); chunk_used = 0; }
    return &chunk[chunk_used++];
}

static int height(Node *t) { return t ? t->h : 0; }

static Node *mk(Node *l, int k, int v, Node *r) {
    int hl = height(l), hr = height(r);
    Node *n = alloc_node();
    n->l = l; n->k = k; n->v = v; n->r = r;
    n->h = 1 + (hl > hr ? hl : hr);
    return n;
}

static Node *bal(Node *l, int k, int v, Node *r) {
    int hl = height(l), hr = height(r);
    if (hl > hr + 1) {
        if (!l) return mk(l, k, v, r);
        if (height(l->l) >= height(l->r)) return mk(l->l, l->k, l->v, mk(l->r, k, v, r));
        if (!l->r) return mk(l, k, v, r);
        return mk(mk(l->l, l->k, l->v, l->r->l), l->r->k, l->r->v, mk(l->r->r, k, v, r));
    } else if (hr > hl + 1) {
        if (!r) return mk(l, k, v, r);
        if (height(r->r) >= height(r->l)) return mk(mk(l, k, v, r->l), r->k, r->v, r->r);
        if (!r->l) return mk(l, k, v, r);
        return mk(mk(l, k, v, r->l->l), r->l->k, r->l->v, mk(r->l->r, r->k, r->v, r->r));
    }
    return mk(l, k, v, r);
}

static Node *insert(int k, int v, Node *t) {
    if (!t) { Node *n = alloc_node(); n->l = 0; n->r = 0; n->k = k; n->v = v; n->h = 1; return n; }
    if (k < t->k) return bal(insert(k, v, t->l), t->k, t->v, t->r);
    if (k > t->k) return bal(t->l, t->k, t->v, insert(k, v, t->r));
    return mk(t->l, k, v, t->r);
}

static int find(int k, Node *t) {
    if (!t) return 0;
    if (k < t->k) return find(k, t->l);
    if (k > t->k) return find(k, t->r);
    return t->v;
}

static int total(Node *t) { return t ? total(t->l) + t->k + total(t->r) : 0; }

#define N 200000
#define REPS 6

int main(void) {
    long long acc = 0;
    for (int rep = 0; rep < REPS; rep++) {
        unsigned s = 2463534242u;
        Node *t = 0;
        for (int i = 0; i < N; i++) {
            s ^= s << 13; s ^= s >> 17; s ^= s << 5;
            int k = (int)(s % 1000000u);
            t = insert(k, k + 1, t);
        }
        unsigned s2 = 2463534242u;
        for (int j = 0; j < N; j++) {
            s2 ^= s2 << 13; s2 ^= s2 >> 17; s2 ^= s2 << 5;
            int k = (int)(s2 % 1000000u);
            acc += find(k, t);
        }
        acc += total(t) + height(t);
    }
    printf("%.0f\n", (double)acc);
    return 0;
}
