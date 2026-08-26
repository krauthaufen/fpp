// The Rust twin of nbody.fpp: the same five-body simulation over parallel
// arrays, the same constants, the same grouping of the addends.
const PI: f64 = 3.141592653589793;
const SOLAR_MASS: f64 = 4.0 * PI * PI;
const DAYS_PER_YEAR: f64 = 365.24;
const NB: usize = 5;

fn main() {
    let mut bx = [0.0f64; NB];
    let mut by = [0.0f64; NB];
    let mut bz = [0.0f64; NB];
    let mut vx = [0.0f64; NB];
    let mut vy = [0.0f64; NB];
    let mut vz = [0.0f64; NB];
    let mut mass = [0.0f64; NB];

    mass[0] = SOLAR_MASS;

    bx[1] = 4.84143144246472090; by[1] = -1.16032004402742839; bz[1] = -0.103622044471123109;
    vx[1] = 0.00166007664274403694 * DAYS_PER_YEAR;
    vy[1] = 0.00769901118419740425 * DAYS_PER_YEAR;
    vz[1] = -0.0000690460016972063023 * DAYS_PER_YEAR;
    mass[1] = 0.000954791938424326609 * SOLAR_MASS;

    bx[2] = 8.34336671824457987; by[2] = 4.12479856412430479; bz[2] = -0.403523417114321381;
    vx[2] = -0.00276742510726862411 * DAYS_PER_YEAR;
    vy[2] = 0.00499852801234917238 * DAYS_PER_YEAR;
    vz[2] = 0.0000230417297573763929 * DAYS_PER_YEAR;
    mass[2] = 0.000285885980666130812 * SOLAR_MASS;

    bx[3] = 12.8943695621391310; by[3] = -15.1111514016986312; bz[3] = -0.223307578892655734;
    vx[3] = 0.00296460137564761618 * DAYS_PER_YEAR;
    vy[3] = 0.00237847173959480950 * DAYS_PER_YEAR;
    vz[3] = -0.0000296589568540237556 * DAYS_PER_YEAR;
    mass[3] = 0.0000436624404335156298 * SOLAR_MASS;

    bx[4] = 15.3796971148509165; by[4] = -25.9193146099879641; bz[4] = 0.179258772950371181;
    vx[4] = 0.00268067772490389322 * DAYS_PER_YEAR;
    vy[4] = 0.00162824170038242295 * DAYS_PER_YEAR;
    vz[4] = -0.0000951592254519715870 * DAYS_PER_YEAR;
    mass[4] = 0.0000515138902046611451 * SOLAR_MASS;

    let mut px = 0.0; let mut py = 0.0; let mut pz = 0.0;
    for i in 0..NB {
        px += vx[i] * mass[i];
        py += vy[i] * mass[i];
        pz += vz[i] * mass[i];
    }
    vx[0] = -px / SOLAR_MASS;
    vy[0] = -py / SOLAR_MASS;
    vz[0] = -pz / SOLAR_MASS;

    let dt = 0.01;
    for _ in 0..3000000 {
        for i in 0..NB {
            for j in (i + 1)..NB {
                let dx = bx[i] - bx[j];
                let dy = by[i] - by[j];
                let dz = bz[i] - bz[j];
                let d2 = dx * dx + dy * dy + dz * dz;
                let mag = dt / (d2 * d2.sqrt());
                vx[i] -= dx * mass[j] * mag;
                vy[i] -= dy * mass[j] * mag;
                vz[i] -= dz * mass[j] * mag;
                vx[j] += dx * mass[i] * mag;
                vy[j] += dy * mass[i] * mag;
                vz[j] += dz * mass[i] * mag;
            }
        }
        for k in 0..NB {
            bx[k] += dt * vx[k];
            by[k] += dt * vy[k];
            bz[k] += dt * vz[k];
        }
    }

    let mut e = 0.0f64;
    for i in 0..NB {
        e += 0.5 * mass[i] * (vx[i] * vx[i] + vy[i] * vy[i] + vz[i] * vz[i]);
        for j in (i + 1)..NB {
            let dx = bx[i] - bx[j];
            let dy = by[i] - by[j];
            let dz = bz[i] - bz[j];
            e -= (mass[i] * mass[j]) / (dx * dx + dy * dy + dz * dz).sqrt();
        }
    }
    println!("{:.9}", e);
}
