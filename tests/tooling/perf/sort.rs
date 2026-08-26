// The Rust twin of sort.fpp: in-place quicksort over an i32 slice, the same
// xorshift keys. Bounds checks are ON, including in the partition scans that
// no analysis can prove — the same two F++ still checks.
const N: usize = 2000000;
const REPS: usize = 6;

fn qsort(a: &mut [i32], lo: isize, hi: isize) {
    if lo < hi {
        let mid = lo + (hi - lo) / 2;
        let p = a[mid as usize];
        let mut i = lo;
        let mut j = hi;
        while i <= j {
            while a[i as usize] < p { i += 1; }
            while a[j as usize] > p { j -= 1; }
            if i <= j {
                a.swap(i as usize, j as usize);
                i += 1;
                j -= 1;
            }
        }
        if lo < j { qsort(a, lo, j); }
        if i < hi { qsort(a, i, hi); }
    }
}

fn main() {
    let mut a = vec![0i32; N];
    let mut acc: i64 = 0;
    for _ in 0..REPS {
        let mut s: u32 = 2463534242;
        for i in 0..N {
            s ^= s << 13; s ^= s >> 17; s ^= s << 5;
            a[i] = (s % 10000000) as i32;
        }
        qsort(&mut a, 0, (N - 1) as isize);
        acc += a[0] as i64 + a[N / 2] as i64 + a[N - 1] as i64;
    }
    println!("{:.0}", acc as f64);
}
