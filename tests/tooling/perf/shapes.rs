// The Rust twin of shapes.fpp: five struct arrays of different shapes, read
// field by field. The addends are GROUPED exactly as the other twins group
// them — left-associating is a different computation, not a faster one.
#[derive(Clone, Copy)] struct V3f { x: f32, y: f32, z: f32 }
#[derive(Clone, Copy)] struct V2d { px: f64, py: f64 }
#[derive(Clone, Copy)] struct C4b { r: u8, g: u8, b: u8, a: u8 }
#[derive(Clone, Copy)] struct Mix { m: f64, t: u8 }
#[derive(Clone, Copy)] struct Bx  { lo: V2d, hi: V2d }

fn main() {
    let n = 1000000usize;
    let reps = 20;
    let mut a = vec![V3f { x: 0.0, y: 0.0, z: 0.0 }; n];
    let mut b = vec![V2d { px: 0.0, py: 0.0 }; n];
    let mut c = vec![C4b { r: 0, g: 0, b: 0, a: 0 }; n];
    let mut d = vec![Mix { m: 0.0, t: 0 }; n];
    let mut e = vec![Bx { lo: V2d { px: 0.0, py: 0.0 }, hi: V2d { px: 0.0, py: 0.0 } }; n];
    for i in 0..n {
        a[i] = V3f { x: 1.0, y: 2.0, z: 3.0 };
        b[i] = V2d { px: 1.0, py: 2.0 };
        c[i] = C4b { r: 1, g: 2, b: 3, a: 4 };
        d[i] = Mix { m: 1.0, t: 1 };
        e[i] = Bx { lo: V2d { px: 1.0, py: 1.0 }, hi: V2d { px: 2.0, py: 2.0 } };
    }
    let mut s = 0.0f64;
    for _ in 0..reps {
        for i in 0..n {
            s += a[i].x as f64 + a[i].y as f64 + a[i].z as f64;
            s += b[i].px + b[i].py;
            s += c[i].r as f64 + c[i].g as f64 + c[i].b as f64 + c[i].a as f64;
            s += d[i].m + d[i].t as f64;
            s += e[i].lo.px + e[i].hi.py;
        }
    }
    println!("{:.0}", s);
}
