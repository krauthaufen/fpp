/* The C twin of avl.fpp: the same persistent AVL, the same xorshift keys,
 * with malloc per node and REFCOUNTS — because the tree is PERSISTENT, and
 * each insert shares most of its nodes with the version before it, so "free
 * the old tree" would free nodes the new one still points at. Refcounting
 * is what a C programmer actually has to write here, and the inc/dec per
 * edge is what it costs.
 *
 * This replaced a bump-arena twin that never freed at all. That one made
 * the collected languages look 2.1x slower than "C" while measuring
 * something no real program can do — read DIVERGENCES-free: if a benchmark
 * never reclaims, it is not comparable to one that must. */
#include <stdio.h>
#include <stdlib.h>

typedef struct Node {
    struct Node *l, *r;
    int k, v, h, rc;
} Node;

static Node *retain(Node *t) { if (t) t->rc++; return t; }

static void release(Node *t) {
    if (!t) return;
    if (--t->rc == 0) { release(t->l); release(t->r); free(t); }
}

static int height(Node *t) { return t ? t->h : 0; }

static Node *mk(Node *l, int k, int v, Node *r) {
    int hl = height(l), hr = height(r);
    Node *n = malloc(sizeof(Node));
    n->l = retain(l); n->r = retain(r);
    n->k = k; n->v = v;
    n->h = 1 + (hl > hr ? hl : hr);
    n->rc = 1;
    return n;
}

/* every intermediate mk() is released after the node that retained it */
static Node *bal(Node *l, int k, int v, Node *r) {
    int hl = height(l), hr = height(r);
    if (hl > hr + 1) {
        if (!l) return mk(l, k, v, r);
        if (height(l->l) >= height(l->r)) {
            Node *in = mk(l->r, k, v, r);
            Node *out = mk(l->l, l->k, l->v, in);
            release(in);
            return out;
        }
        if (!l->r) return mk(l, k, v, r);
        {
            Node *a = mk(l->l, l->k, l->v, l->r->l);
            Node *b = mk(l->r->r, k, v, r);
            Node *out = mk(a, l->r->k, l->r->v, b);
            release(a); release(b);
            return out;
        }
    } else if (hr > hl + 1) {
        if (!r) return mk(l, k, v, r);
        if (height(r->r) >= height(r->l)) {
            Node *in = mk(l, k, v, r->l);
            Node *out = mk(in, r->k, r->v, r->r);
            release(in);
            return out;
        }
        if (!r->l) return mk(l, k, v, r);
        {
            Node *a = mk(l, k, v, r->l->l);
            Node *b = mk(r->l->r, r->k, r->v, r->r);
            Node *out = mk(a, r->l->k, r->l->v, b);
            release(a); release(b);
            return out;
        }
    }
    return mk(l, k, v, r);
}

static Node *insert(int k, int v, Node *t) {
    if (!t) {
        Node *n = malloc(sizeof(Node));
        n->l = 0; n->r = 0; n->k = k; n->v = v; n->h = 1; n->rc = 1;
        return n;
    }
    if (k < t->k) {
        Node *nl = insert(k, v, t->l);
        Node *out = bal(nl, t->k, t->v, t->r);
        release(nl);
        return out;
    }
    if (k > t->k) {
        Node *nr = insert(k, v, t->r);
        Node *out = bal(t->l, t->k, t->v, nr);
        release(nr);
        return out;
    }
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
            Node *nt = insert(k, k + 1, t);
            release(t);                     /* the previous version dies here */
            t = nt;
        }
        unsigned s2 = 2463534242u;
        for (int j = 0; j < N; j++) {
            s2 ^= s2 << 13; s2 ^= s2 >> 17; s2 ^= s2 << 5;
            int k = (int)(s2 % 1000000u);
            acc += find(k, t);
        }
        acc += total(t) + height(t);
        release(t);
    }
    printf("%.0f\n", (double)acc);
    return 0;
}
