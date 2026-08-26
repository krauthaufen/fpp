// The Rust twin of vertices.fpp: fill a V3f array, then sum every component
// 20 times.
#[derive(Clone, Copy)]
struct V3f { x: f32, y: f32, z: f32 }

fn main() {
    let n = 1000000usize;
    let mut v = vec![V3f { x: 0.0, y: 0.0, z: 0.0 }; n];
    for i in 0..n { v[i] = V3f { x: 1.0, y: 2.0, z: 3.0 }; }
    let mut acc: f64 = 0.0;
    for _ in 0..20 {
        for i in 0..n { acc += v[i].x as f64 + v[i].y as f64 + v[i].z as f64; }
    }
    println!("{:.0}", acc);
}
