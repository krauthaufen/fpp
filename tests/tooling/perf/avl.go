// The Go twin of avl.fpp: the same persistent AVL, the same xorshift keys,
// the same never-freed nodes — Go just drops them and lets its collector
// deal with it, exactly as the F++ and F# twins do. It is here so the
// collector column can be read against a MATURE GC and not only against
// C's bump arena, which never reclaims anything at all.
package main

import "fmt"

type node struct {
	l, r *node
	k, v, h int
}

func height(t *node) int {
	if t == nil {
		return 0
	}
	return t.h
}

func mk(l *node, k, v int, r *node) *node {
	hl, hr := height(l), height(r)
	h := hl
	if hr > hl {
		h = hr
	}
	return &node{l, r, k, v, 1 + h}
}

func bal(l *node, k, v int, r *node) *node {
	hl, hr := height(l), height(r)
	if hl > hr+1 {
		if l == nil {
			return mk(l, k, v, r)
		}
		if height(l.l) >= height(l.r) {
			return mk(l.l, l.k, l.v, mk(l.r, k, v, r))
		}
		if l.r == nil {
			return mk(l, k, v, r)
		}
		return mk(mk(l.l, l.k, l.v, l.r.l), l.r.k, l.r.v, mk(l.r.r, k, v, r))
	} else if hr > hl+1 {
		if r == nil {
			return mk(l, k, v, r)
		}
		if height(r.r) >= height(r.l) {
			return mk(mk(l, k, v, r.l), r.k, r.v, r.r)
		}
		if r.l == nil {
			return mk(l, k, v, r)
		}
		return mk(mk(l, k, v, r.l.l), r.l.k, r.l.v, mk(r.l.r, r.k, r.v, r.r))
	}
	return mk(l, k, v, r)
}

func insert(k, v int, t *node) *node {
	if t == nil {
		return &node{nil, nil, k, v, 1}
	}
	if k < t.k {
		return bal(insert(k, v, t.l), t.k, t.v, t.r)
	}
	if k > t.k {
		return bal(t.l, t.k, t.v, insert(k, v, t.r))
	}
	return mk(t.l, k, v, t.r)
}

func find(k int, t *node) int {
	if t == nil {
		return 0
	}
	if k < t.k {
		return find(k, t.l)
	}
	if k > t.k {
		return find(k, t.r)
	}
	return t.v
}

// int32, not int: the C and F++ twins accumulate this in a 32-bit int and
// it OVERFLOWS — 200k keys of up to a million. Go's int is 64-bit, so
// without the narrowing the checksums disagree and the twins are not the
// same program.
func total(t *node) int32 {
	if t == nil {
		return 0
	}
	return total(t.l) + int32(t.k) + total(t.r)
}

const nkeys = 200000
const reps = 6

func main() {
	var acc int64
	for rep := 0; rep < reps; rep++ {
		s := uint32(2463534242)
		var t *node
		for i := 0; i < nkeys; i++ {
			s ^= s << 13
			s ^= s >> 17
			s ^= s << 5
			k := int(s % 1000000)
			t = insert(k, k+1, t)
		}
		s2 := uint32(2463534242)
		for j := 0; j < nkeys; j++ {
			s2 ^= s2 << 13
			s2 ^= s2 >> 17
			s2 ^= s2 << 5
			k := int(s2 % 1000000)
			acc += int64(find(k, t))
		}
		acc += int64(total(t) + int32(height(t)))
	}
	fmt.Printf("%.0f\n", float64(acc))
}
