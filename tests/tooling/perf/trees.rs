// The Rust twin of trees.fpp. `Box` owns each node, so the whole tree is
// freed when it goes out of scope — the same lifetime the C twin writes by
// hand and the same one the collector works out for itself.
struct Node { l: Option<Box<Node>>, r: Option<Box<Node>> }

fn build(d: i32) -> Option<Box<Node>> {
    if d == 0 { None } else { Some(Box::new(Node { l: build(d - 1), r: build(d - 1) })) }
}

fn check(t: &Option<Box<Node>>) -> i32 {
    match t { None => 1, Some(n) => 1 + check(&n.l) + check(&n.r) }
}

const MAXD: i32 = 18;
const MIND: i32 = 4;

fn main() {
    let mut acc: i64 = 0;
    let long_lived = build(MAXD);
    let mut d = MIND;
    while d <= MAXD {
        let iters: i64 = 1i64 << (MAXD - d + MIND);
        let mut sum: i32 = 0;
        let mut i: i64 = 0;
        while i < iters {
            sum += check(&build(d));   // the tree is dropped at the end of this expression
            i += 1;
        }
        acc += sum as i64;
        d += 2;
    }
    acc += check(&long_lived) as i64;
    println!("{:.0}", acc as f64);
}
