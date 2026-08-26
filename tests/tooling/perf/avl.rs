// The Rust twin of avl.fpp: the same persistent AVL, the same xorshift keys.
// `Rc` because the tree is PERSISTENT — each insert shares most of its nodes
// with the version before it, which is exactly why the C twin needs manual
// refcounts. Rust's are the same counts, just written by the compiler.
use std::rc::Rc;

struct Node { l: Tree, r: Tree, k: i32, v: i32, h: i32 }
type Tree = Option<Rc<Node>>;

fn height(t: &Tree) -> i32 { match t { None => 0, Some(n) => n.h } }

fn mk(l: Tree, k: i32, v: i32, r: Tree) -> Tree {
    let h = 1 + std::cmp::max(height(&l), height(&r));
    Some(Rc::new(Node { l, r, k, v, h }))
}

fn bal(l: Tree, k: i32, v: i32, r: Tree) -> Tree {
    let (hl, hr) = (height(&l), height(&r));
    if hl > hr + 1 {
        let ln = match &l { None => return mk(l, k, v, r), Some(n) => n.clone() };
        if height(&ln.l) >= height(&ln.r) {
            return mk(ln.l.clone(), ln.k, ln.v, mk(ln.r.clone(), k, v, r));
        }
        let lr = match &ln.r { None => return mk(l, k, v, r), Some(n) => n.clone() };
        return mk(mk(ln.l.clone(), ln.k, ln.v, lr.l.clone()), lr.k, lr.v, mk(lr.r.clone(), k, v, r));
    } else if hr > hl + 1 {
        let rn = match &r { None => return mk(l, k, v, r), Some(n) => n.clone() };
        if height(&rn.r) >= height(&rn.l) {
            return mk(mk(l, k, v, rn.l.clone()), rn.k, rn.v, rn.r.clone());
        }
        let rl = match &rn.l { None => return mk(l, k, v, r), Some(n) => n.clone() };
        return mk(mk(l, k, v, rl.l.clone()), rl.k, rl.v, mk(rl.r.clone(), rn.k, rn.v, rn.r.clone()));
    }
    mk(l, k, v, r)
}

fn insert(k: i32, v: i32, t: &Tree) -> Tree {
    match t {
        None => Some(Rc::new(Node { l: None, r: None, k, v, h: 1 })),
        Some(n) => {
            if k < n.k { bal(insert(k, v, &n.l), n.k, n.v, n.r.clone()) }
            else if k > n.k { bal(n.l.clone(), n.k, n.v, insert(k, v, &n.r)) }
            else { mk(n.l.clone(), k, v, n.r.clone()) }
        }
    }
}

fn find(k: i32, t: &Tree) -> i32 {
    match t {
        None => 0,
        Some(n) => if k < n.k { find(k, &n.l) } else if k > n.k { find(k, &n.r) } else { n.v },
    }
}

// i32, and it OVERFLOWS: the C and F++ twins accumulate this in a 32-bit int
// and so must this, or the checksums disagree. wrapping_add, since a release
// build would merely wrap but a debug build would panic.
fn total(t: &Tree) -> i32 {
    match t { None => 0, Some(n) => total(&n.l).wrapping_add(n.k).wrapping_add(total(&n.r)) }
}

const N: i32 = 200000;
const REPS: i32 = 6;

fn main() {
    let mut acc: i64 = 0;
    for _ in 0..REPS {
        let mut s: u32 = 2463534242;
        let mut t: Tree = None;
        for _ in 0..N {
            s ^= s << 13; s ^= s >> 17; s ^= s << 5;
            let k = (s % 1000000) as i32;
            t = insert(k, k + 1, &t);
        }
        let mut s2: u32 = 2463534242;
        for _ in 0..N {
            s2 ^= s2 << 13; s2 ^= s2 >> 17; s2 ^= s2 << 5;
            let k = (s2 % 1000000) as i32;
            acc += find(k, &t) as i64;
        }
        acc += total(&t).wrapping_add(height(&t)) as i64;
    }
    println!("{:.0}", acc as f64);
}
