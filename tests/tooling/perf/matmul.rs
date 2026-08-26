// The Rust twin of matmul.fpp: the classic triple loop over flat arrays,
// indexed with i*n+k arithmetic. Bounds checks are ON — this is what a
// checked flat-matrix index costs.
const N: usize = 320;

fn main() {
    let mut a = vec![0.0f64; N * N];
    let mut b = vec![0.0f64; N * N];
    let mut c = vec![0.0f64; N * N];
    for i in 0..N {
        for j in 0..N {
            a[i * N + j] = ((i + j) % 7) as f64;
            b[i * N + j] = ((i * 2 + j) % 5) as f64;
        }
    }
    for _ in 0..3 {
        for i in 0..N {
            for k in 0..N {
                let aik = a[i * N + k];
                for j in 0..N { c[i * N + j] += aik * b[k * N + j]; }
            }
        }
    }
    let mut s = 0.0f64;
    for i in 0..N * N { s += c[i]; }
    println!("{:.0}", s);
}
