// The Rust twin of add.fpp: a float accumulation, nothing else. `a` comes
// from argc for the same reason C's does — a constant would fold the loop
// away and the benchmark would measure nothing.
fn main() {
    let a = std::env::args().count() as f64;
    let mut acc: f64 = 0.0;
    for _ in 0..20 {
        for _ in 0..1000000 { acc += a; }
    }
    println!("{:.0}", acc);
}
