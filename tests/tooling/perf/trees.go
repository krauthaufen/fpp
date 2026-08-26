// The Go twin of trees.fpp: the same shape, run under the SAME wasmtime via
// GOOS=wasip1. It exists so the collector column is not read against C's
// arena reset — C here bump-allocates and drops a pointer, which no
// collected language can match. Go's is a mature generational-ish
// concurrent collector; this is what "a real GC on this workload" costs.
package main

import "fmt"

type node struct{ l, r *node }

func build(d int) *node {
	if d == 0 {
		return nil
	}
	return &node{build(d - 1), build(d - 1)}
}

func check(t *node) int {
	if t == nil {
		return 1
	}
	return 1 + check(t.l) + check(t.r)
}

const maxDepth = 18
const minDepth = 4

func main() {
	var acc int64
	longLived := build(maxDepth)
	for d := minDepth; d <= maxDepth; d += 2 {
		iters := 1 << (maxDepth - d + minDepth)
		sum := 0
		for i := 0; i < iters; i++ {
			sum += check(build(d))
		}
		acc += int64(sum)
	}
	acc += int64(check(longLived))
	fmt.Printf("%.0f\n", float64(acc))
}
