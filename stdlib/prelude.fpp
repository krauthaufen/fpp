class Add<'a, 'b>
    type Result
    static (+) : 'a -> 'b -> Result
class Sub<'a, 'b>
    type Result
    static (-) : 'a -> 'b -> Result
class Mul<'a, 'b>
    type Result
    static (*) : 'a -> 'b -> Result
class Div<'a, 'b>
    type Result
    static (/) : 'a -> 'b -> Result
class Rem<'a, 'b>
    type Result
    static (%) : 'a -> 'b -> Result
class Num<'a>
    when Add<'a, 'a> = 'a
    when Sub<'a, 'a> = 'a
    when Mul<'a, 'a> = 'a
    static Zero : 'a
    static One : 'a
class Fractional<'a>
    when Num<'a>
    when Div<'a, 'a> = 'a
class Integral<'a>
    when Num<'a>
    when Div<'a, 'a> = 'a
    when Rem<'a, 'a> = 'a
class Ordered<'a>
    static compare : 'a -> 'a -> int
class Neg<'a>
    static (~-) : 'a -> 'a
class Abs<'a>
    static abs : 'a -> 'a
class MinMax<'a>
    static min : 'a -> 'a -> 'a
    static max : 'a -> 'a -> 'a
class Floating<'a>
    when Fractional<'a>
    static sqrt : 'a -> 'a
    static truncate : 'a -> 'a
    static exp : 'a -> 'a
    static log : 'a -> 'a
    static sin : 'a -> 'a
    static cos : 'a -> 'a
    static tan : 'a -> 'a
    static sinh : 'a -> 'a
    static cosh : 'a -> 'a
    static tanh : 'a -> 'a
    static asin : 'a -> 'a
    static acos : 'a -> 'a
    static atan : 'a -> 'a
    static atan2 : 'a -> 'a -> 'a
    static pow : 'a -> 'a -> 'a
instance Add<string, string>
    type Result = string
instance Add<int, int>
    type Result = int
instance Sub<int, int>
    type Result = int
instance Mul<int, int>
    type Result = int
instance Div<int, int>
    type Result = int
instance Rem<int, int>
    type Result = int
instance Num<int>
    static Zero = 0
    static One = 1
instance Integral<int>
instance Ordered<int>
instance Neg<int>
instance Abs<int>
instance MinMax<int>
    static min a b = if a < b then a else b
    static max a b = if a > b then a else b
instance Add<int64, int64>
    type Result = int64
instance Sub<int64, int64>
    type Result = int64
instance Mul<int64, int64>
    type Result = int64
instance Div<int64, int64>
    type Result = int64
instance Rem<int64, int64>
    type Result = int64
instance Num<int64>
    static Zero = 0L
    static One = 1L
instance Integral<int64>
instance Ordered<int64>
instance Neg<int64>
instance Abs<int64>
instance MinMax<int64>
    static min a b = if a < b then a else b
    static max a b = if a > b then a else b
instance Add<uint32, uint32>
    type Result = uint32
instance Sub<uint32, uint32>
    type Result = uint32
instance Mul<uint32, uint32>
    type Result = uint32
instance Div<uint32, uint32>
    type Result = uint32
instance Rem<uint32, uint32>
    type Result = uint32
instance Num<uint32>
    static Zero = 0u
    static One = 1u
instance Integral<uint32>
instance Ordered<uint32>
instance MinMax<uint32>
    static min a b = if a < b then a else b
    static max a b = if a > b then a else b
instance Add<float, float>
    type Result = float
instance Sub<float, float>
    type Result = float
instance Mul<float, float>
    type Result = float
instance Div<float, float>
    type Result = float
instance Num<float>
    static Zero = 0.0
    static One = 1.0
instance Fractional<float>
instance Ordered<float>
instance Neg<float>
instance Abs<float>
instance MinMax<float>
    static min a b = if a < b then a else b
    static max a b = if a > b then a else b
instance Add<float32, float32>
    type Result = float32
instance Sub<float32, float32>
    type Result = float32
instance Mul<float32, float32>
    type Result = float32
instance Div<float32, float32>
    type Result = float32
instance Num<float32>
    static Zero = 0.0f
    static One = 1.0f
instance Fractional<float32>
instance Ordered<float32>
instance Neg<float32>
instance Abs<float32>
instance MinMax<float32>
    static min a b = if a < b then a else b
    static max a b = if a > b then a else b
instance Ordered<byte>
instance Ordered<sbyte>
instance Ordered<string>
instance Ordered<char>
instance MinMax<string>
    static min a b = if a < b then a else b
    static max a b = if a > b then a else b
instance MinMax<char>
    static min a b = if a < b then a else b
    static max a b = if a > b then a else b
// exact: doubling and halving a float are exact until it goes subnormal,
// which exp's range check has already excluded
let scale2F m k =
    let mutable r = m
    let mutable n = k
    while n > 0.0 do
        r <- r * 2.0
        n <- n - 1.0
    while n < 0.0 do
        r <- r * 0.5
        n <- n + 1.0
    r
let expF x =
    if x <> x then x
    elif x > 709.782712893384 then 1.0 / 0.0
    elif x < -745.1332191019411 then 0.0
    else
        // x = k ln2 + r with |r| <= ln2/2, then Taylor to r^13/13!
        let k = truncate (x * 1.4426950408889634 + (if x < 0.0 then -0.5 else 0.5))
        let r = (x - k * 0.6931471803691238) - k * 1.9082149292705877e-10
        let p =
            1.0 + r * (1.0 + r * (0.5 + r * (0.16666666666666666
                + r * (0.041666666666666664 + r * (0.008333333333333333
                + r * (0.001388888888888889 + r * (0.0001984126984126984
                + r * (2.48015873015873e-05 + r * (2.7557319223985893e-06
                + r * (2.755731922398589e-07 + r * (2.5052108385441718e-08
                + r * 2.08767569878681e-09)))))))))))
        scale2F p k
let logF x =
    if x <> x then x
    elif x < 0.0 then 0.0 / 0.0
    elif x = 0.0 then -1.0 / 0.0
    else
        // x = m 2^e with m in [sqrt(1/2), sqrt 2), then the atanh series in
        // s = (m-1)/(m+1), where |s| <= 0.1716
        let mutable m = x
        let mutable e = 0.0
        while m >= 1.4142135623730951 do
            m <- m * 0.5
            e <- e + 1.0
        while m < 0.7071067811865476 do
            m <- m * 2.0
            e <- e - 1.0
        let s = (m - 1.0) / (m + 1.0)
        let q = s * s
        let p =
            1.0 + q * (0.3333333333333333 + q * (0.2 + q * (0.14285714285714285
                + q * (0.1111111111111111 + q * (0.09090909090909091
                + q * (0.07692307692307693 + q * (0.06666666666666667
                + q * (0.058823529411764705 + q * 0.05263157894736842))))))))
        (e * 0.6931471803691238 + e * 1.9082149292705877e-10) + 2.0 * s * p
// pi/2 split three ways, so the reduction keeps its digits for moderately
// large arguments; it degrades past 1e8
let reduceF x =
    let q = truncate (x * 0.6366197723675814 + (if x < 0.0 then -0.5 else 0.5))
    ((x - q * 1.5707963267341256) - q * 6.077100506506192e-11) - q * 1.2154201862823113e-21
let quadrantF x =
    let q = truncate (x * 0.6366197723675814 + (if x < 0.0 then -0.5 else 0.5))
    let m = q - 4.0 * truncate (q / 4.0)
    if m < 0.0 then m + 4.0 else m
let sinCoreF r =
    let q = r * r
    r * (1.0 + q * (-0.16666666666666666 + q * (0.008333333333333333
        + q * (-0.0001984126984126984 + q * (2.7557319223985893e-06
        + q * (-2.505210838544172e-08 + q * (1.6059043836821613e-10
        + q * -7.647163731819816e-13)))))))
let cosCoreF r =
    let q = r * r
    1.0 + q * (-0.5 + q * (0.041666666666666664 + q * (-0.001388888888888889
        + q * (2.48015873015873e-05 + q * (-2.755731922398589e-07
        + q * (2.08767569878681e-09 + q * -1.1470745597729725e-11))))))
let sinF x =
    if x <> x then x
    else
        let n = quadrantF x
        let r = reduceF x
        if n = 0.0 then sinCoreF r
        elif n = 1.0 then cosCoreF r
        elif n = 2.0 then -(sinCoreF r)
        else -(cosCoreF r)
let cosF x =
    if x <> x then x
    else
        let n = quadrantF x
        let r = reduceF x
        if n = 0.0 then cosCoreF r
        elif n = 1.0 then -(sinCoreF r)
        elif n = 2.0 then -(cosCoreF r)
        else sinCoreF r
// an integer exponent is done by repeated squaring, which is EXACT — the
// exp/log route would return -7.999999999999998 for (-2)^3
let powIntNF a n =
    let mutable r = 1.0
    let mutable f = a
    let mutable k = n
    while k > 0.0 do
        let half = truncate (k * 0.5)
        if k - half - half <> 0.0 then r <- r * f
        f <- f * f
        k <- half
    r
let powF a b =
    if b = 0.0 then 1.0
    elif b <> b then b
    else
        let k = truncate b
        let mag = if b < 0.0 then -b else b
        if k = b && mag <= 1024.0 then
            let r = powIntNF a mag
            if b < 0.0 then 1.0 / r else r
        elif a > 0.0 then expF (b * logF a)
        elif a = 0.0 then (if b > 0.0 then 0.0 else 1.0 / 0.0)
        else
            // a negative base is defined only at an integer exponent, and
            // that case was handled above
            0.0 / 0.0
// hyperbolics. Near zero sinh cancels catastrophically in
// (e^x - e^-x)/2, so small arguments take the series instead; cosh has no
// such problem, and tanh saturates rather than overflowing.
let sinhF x =
    if x <> x then x
    else
        let a = if x < 0.0 then -x else x
        if a < 0.5 then
            let q = x * x
            x * (1.0 + q * (0.16666666666666666 + q * (0.008333333333333333
                + q * (0.0001984126984126984 + q * 2.7557319223985893e-06))))
        else
            let e = expF x
            (e - 1.0 / e) * 0.5
let coshF x =
    if x <> x then x
    else
        let e = expF (if x < 0.0 then -x else x)
        (e + 1.0 / e) * 0.5
let tanhF x =
    if x <> x then x
    else
        let a = if x < 0.0 then -x else x
        if a < 0.5 then sinhF x / coshF x
        elif a > 20.0 then (if x < 0.0 then -1.0 else 1.0)
        else
            let e = expF (a + a)
            let t = (e - 1.0) / (e + 1.0)
            if x < 0.0 then -t else t
// atan by halving twice — atan y = 2 atan (y / (1 + sqrt (1 + y*y))) — which
// brings the argument under 0.2 before the series, where it converges fast
let atanF x =
    if x <> x then x
    else
        let a = if x < 0.0 then -x else x
        let big = a > 1.0
        let y = if big then 1.0 / a else a
        let y1 = y / (1.0 + sqrt (1.0 + y * y))
        let y2 = y1 / (1.0 + sqrt (1.0 + y1 * y1))
        let q = y2 * y2
        let s =
            y2 * (1.0 - q * (0.3333333333333333 - q * (0.2 - q * (0.14285714285714285
                - q * (0.1111111111111111 - q * (0.09090909090909091
                - q * (0.07692307692307693 - q * (0.06666666666666667
                - q * (0.058823529411764705 - q * (0.05263157894736842
                - q * 0.047619047619047616)))))))))
        let r = 4.0 * s
        let m = if big then 1.5707963267948966 - r else r
        if x < 0.0 then -m else m
let asinF x =
    if x <> x then x
    elif x >= 1.0 then 1.5707963267948966
    elif x <= -1.0 then -1.5707963267948966
    else atanF (x / sqrt (1.0 - x * x))
let atan2F y x =
    if x > 0.0 then atanF (y / x)
    elif x < 0.0 then
        if y >= 0.0 then atanF (y / x) + 3.141592653589793
        else atanF (y / x) - 3.141592653589793
    elif y > 0.0 then 1.5707963267948966
    elif y < 0.0 then -1.5707963267948966
    else 0.0
instance Floating<float>
    static exp x = expF x
    static log x = logF x
    static sin x = sinF x
    static cos x = cosF x
    static tan x = sinF x / cosF x
    static sinh x = sinhF x
    static cosh x = coshF x
    static tanh x = tanhF x
    static asin x = asinF x
    static acos x = 1.5707963267948966 - asinF x
    static atan x = atanF x
    static atan2 y x = atan2F y x
    static pow a b = powF a b
instance Rem<float, float>
    type Result = float
    static (%) a b = a - b * truncate (a / b)
// exact: doubling and halving a float are exact until it goes subnormal,
// which exp's range check has already excluded
let scale2F32 m k =
    let mutable r = m
    let mutable n = k
    while n > 0.0f do
        r <- r * 2.0f
        n <- n - 1.0f
    while n < 0.0f do
        r <- r * 0.5f
        n <- n + 1.0f
    r
let expF32 x =
    if x <> x then x
    elif x > 709.782712893384f then 1.0f / 0.0f
    elif x < -745.1332191019411f then 0.0f
    else
        // x = k ln2 + r with |r| <= ln2/2, then Taylor to r^13/13!
        let k = truncate (x * 1.4426950408889634f + (if x < 0.0f then -0.5f else 0.5f))
        let r = (x - k * 0.6931471803691238f) - k * 1.9082149292705877e-10f
        let p =
            1.0f + r * (1.0f + r * (0.5f + r * (0.16666666666666666f
                + r * (0.041666666666666664f + r * (0.008333333333333333f
                + r * (0.001388888888888889f + r * (0.0001984126984126984f
                + r * (2.48015873015873e-05f + r * (2.7557319223985893e-06f
                + r * (2.755731922398589e-07f + r * (2.5052108385441718e-08f
                + r * 2.08767569878681e-09f)))))))))))
        scale2F32 p k
let logF32 x =
    if x <> x then x
    elif x < 0.0f then 0.0f / 0.0f
    elif x = 0.0f then -1.0f / 0.0f
    else
        // x = m 2^e with m in [sqrt(1/2), sqrt 2), then the atanh series in
        // s = (m-1)/(m+1), where |s| <= 0.1716
        let mutable m = x
        let mutable e = 0.0f
        while m >= 1.4142135623730951f do
            m <- m * 0.5f
            e <- e + 1.0f
        while m < 0.7071067811865476f do
            m <- m * 2.0f
            e <- e - 1.0f
        let s = (m - 1.0f) / (m + 1.0f)
        let q = s * s
        let p =
            1.0f + q * (0.3333333333333333f + q * (0.2f + q * (0.14285714285714285f
                + q * (0.1111111111111111f + q * (0.09090909090909091f
                + q * (0.07692307692307693f + q * (0.06666666666666667f
                + q * (0.058823529411764705f + q * 0.05263157894736842f))))))))
        (e * 0.6931471803691238f + e * 1.9082149292705877e-10f) + 2.0f * s * p
// pi/2 split three ways, so the reduction keeps its digits for moderately
// large arguments; it degrades past f1e8
let reduceF32 x =
    let q = truncate (x * 0.6366197723675814f + (if x < 0.0f then -0.5f else 0.5f))
    ((x - q * 1.5707963267341256f) - q * 6.077100506506192e-11f) - q * 1.2154201862823113e-21f
let quadrantF32 x =
    let q = truncate (x * 0.6366197723675814f + (if x < 0.0f then -0.5f else 0.5f))
    let m = q - 4.0f * truncate (q / 4.0f)
    if m < 0.0f then m + 4.0f else m
let sinCoreF32 r =
    let q = r * r
    r * (1.0f + q * (-0.16666666666666666f + q * (0.008333333333333333f
        + q * (-0.0001984126984126984f + q * (2.7557319223985893e-06f
        + q * (-2.505210838544172e-08f + q * (1.6059043836821613e-10f
        + q * -7.647163731819816e-13f)))))))
let cosCoreF32 r =
    let q = r * r
    1.0f + q * (-0.5f + q * (0.041666666666666664f + q * (-0.001388888888888889f
        + q * (2.48015873015873e-05f + q * (-2.755731922398589e-07f
        + q * (2.08767569878681e-09f + q * -1.1470745597729725e-11f))))))
let sinF32 x =
    if x <> x then x
    else
        let n = quadrantF32 x
        let r = reduceF32 x
        if n = 0.0f then sinCoreF32 r
        elif n = 1.0f then cosCoreF32 r
        elif n = 2.0f then -(sinCoreF32 r)
        else -(cosCoreF32 r)
let cosF32 x =
    if x <> x then x
    else
        let n = quadrantF32 x
        let r = reduceF32 x
        if n = 0.0f then cosCoreF32 r
        elif n = 1.0f then -(sinCoreF32 r)
        elif n = 2.0f then -(cosCoreF32 r)
        else sinCoreF32 r
// an integer exponent is done by repeated squaring, which is EXACT — the
// exp/log route would return -7.999999999999998 for (-2)^3
let powIntNF32 a n =
    let mutable r = 1.0f
    let mutable f = a
    let mutable k = n
    while k > 0.0f do
        let half = truncate (k * 0.5f)
        if k - half - half <> 0.0f then r <- r * f
        f <- f * f
        k <- half
    r
let powF32 a b =
    if b = 0.0f then 1.0f
    elif b <> b then b
    else
        let k = truncate b
        let mag = if b < 0.0f then -b else b
        if k = b && mag <= 1024.0f then
            let r = powIntNF32 a mag
            if b < 0.0f then 1.0f / r else r
        elif a > 0.0f then expF32 (b * logF32 a)
        elif a = 0.0f then (if b > 0.0f then 0.0f else 1.0f / 0.0f)
        else
            // a negative base is defined only at an integer exponent, and
            // that case was handled above
            0.0f / 0.0f
// hyperbolics. Near zero sinh cancels catastrophically in
// (e^x - e^-x)/2, so small arguments take the series instead; cosh has no
// such problem, and tanh saturates rather than overflowing.
let sinhF32 x =
    if x <> x then x
    else
        let a = if x < 0.0f then -x else x
        if a < 0.5f then
            let q = x * x
            x * (1.0f + q * (0.16666666666666666f + q * (0.008333333333333333f
                + q * (0.0001984126984126984f + q * 2.7557319223985893e-06f))))
        else
            let e = expF32 x
            (e - 1.0f / e) * 0.5f
let coshF32 x =
    if x <> x then x
    else
        let e = expF32 (if x < 0.0f then -x else x)
        (e + 1.0f / e) * 0.5f
let tanhF32 x =
    if x <> x then x
    else
        let a = if x < 0.0f then -x else x
        if a < 0.5f then sinhF32 x / coshF32 x
        elif a > 20.0f then (if x < 0.0f then -1.0f else 1.0f)
        else
            let e = expF32 (a + a)
            let t = (e - 1.0f) / (e + 1.0f)
            if x < 0.0f then -t else t
// atan by halving twice — atan y = 2 atan (y / (1 + sqrt (1 + y*y))) — which
// brings the argument under 0.2 before the series, where it converges fast
let atanF32 x =
    if x <> x then x
    else
        let a = if x < 0.0f then -x else x
        let big = a > 1.0f
        let y = if big then 1.0f / a else a
        let y1 = y / (1.0f + sqrt (1.0f + y * y))
        let y2 = y1 / (1.0f + sqrt (1.0f + y1 * y1))
        let q = y2 * y2
        let s =
            y2 * (1.0f - q * (0.3333333333333333f - q * (0.2f - q * (0.14285714285714285f
                - q * (0.1111111111111111f - q * (0.09090909090909091f
                - q * (0.07692307692307693f - q * (0.06666666666666667f
                - q * (0.058823529411764705f - q * (0.05263157894736842f
                - q * 0.047619047619047616f)))))))))
        let r = 4.0f * s
        let m = if big then 1.5707963267948966f - r else r
        if x < 0.0f then -m else m
let asinF32 x =
    if x <> x then x
    elif x >= 1.0f then 1.5707963267948966f
    elif x <= -1.0f then -1.5707963267948966f
    else atanF32 (x / sqrt (1.0f - x * x))
let atan2F32 y x =
    if x > 0.0f then atanF32 (y / x)
    elif x < 0.0f then
        if y >= 0.0f then atanF32 (y / x) + 3.141592653589793f
        else atanF32 (y / x) - 3.141592653589793f
    elif y > 0.0f then 1.5707963267948966f
    elif y < 0.0f then -1.5707963267948966f
    else 0.0f
instance Floating<float32>
    static exp x = expF32 x
    static log x = logF32 x
    static sin x = sinF32 x
    static cos x = cosF32 x
    static tan x = sinF32 x / cosF32 x
    static sinh x = sinhF32 x
    static cosh x = coshF32 x
    static tanh x = tanhF32 x
    static asin x = asinF32 x
    static acos x = 1.5707963267948966f - asinF32 x
    static atan x = atanF32 x
    static atan2 y x = atan2F32 y x
    static pow a b = powF32 a b
instance Rem<float32, float32>
    type Result = float32
    static (%) a b = a - b * truncate (a / b)
instance Add<float16, float16>
    type Result = float16
instance Sub<float16, float16>
    type Result = float16
instance Mul<float16, float16>
    type Result = float16
instance Div<float16, float16>
    type Result = float16
instance Rem<float16, float16>
    type Result = float16
    static (%) a b = a - b * truncate (a / b)
instance Ordered<float16>
instance Neg<float16>
instance Abs<float16>
instance MinMax<float16>
    static min a b = if a < b then a else b
    static max a b = if a > b then a else b
instance Num<float16>
    static Zero = 0.0h
    static One = 1.0h
instance Fractional<float16>
instance Floating<float16>
    static exp x = float16 (exp (float32 x))
    static log x = float16 (log (float32 x))
    static sin x = float16 (sin (float32 x))
    static cos x = float16 (cos (float32 x))
    static tan x = float16 (tan (float32 x))
    static sinh x = float16 (sinh (float32 x))
    static cosh x = float16 (cosh (float32 x))
    static tanh x = float16 (tanh (float32 x))
    static asin x = float16 (asin (float32 x))
    static acos x = float16 (acos (float32 x))
    static atan x = float16 (atan (float32 x))
    static atan2 y x = float16 (atan2 (float32 y) (float32 x))
    static pow a b = float16 (pow (float32 a) (float32 b))
type IEnumerator<'a> =
    abstract member MoveNext : unit -> bool
    abstract member Current : 'a
type IEnumerable<'a> =
    abstract member GetEnumerator : unit -> IEnumerator<'a>
type seq<'a> = IEnumerable<'a>
type IReadOnlyCollection<'a> =
    abstract member Count : int
type IEquatable<'a> =
    abstract member Equals : 'a -> bool
type ISet<'a> =
    abstract member Count : int
    abstract member Contains : 'a -> bool
    abstract member Overlaps : seq<'a> -> bool
    abstract member SetEquals : seq<'a> -> bool
    abstract member IsSubsetOf : seq<'a> -> bool
    abstract member IsProperSubsetOf : seq<'a> -> bool
    abstract member IsSupersetOf : seq<'a> -> bool
    abstract member IsProperSupersetOf : seq<'a> -> bool
type Option<'a> =
    | None
    | Some of 'a
type option<'a> = Option<'a>
type Result<'t, 'e> =
    | Ok of 't
    | Error of 'e
type exn =
    | Failure of string
    | InvalidCast of string
    | KeyNotFoundException of string
type ValueOption<'a> =
    | ValueNone
    | ValueSome of 'a
type voption<'a> = ValueOption<'a>
[<Struct>]
type StructTuple2<'a, 'b> = { Item1 : 'a; Item2 : 'b }
[<Struct>]
type StructTuple3<'a, 'b, 'c> = { Item1 : 'a; Item2 : 'b; Item3 : 'c }
[<Struct>]
type StructTuple4<'a, 'b, 'c, 'd> = { Item1 : 'a; Item2 : 'b; Item3 : 'c; Item4 : 'd }
type IEqualityComparer<'a> =
    abstract member Equals : 'a * 'a -> bool
    abstract member GetHashCode : 'a -> int
type DefaultEqualityComparer<'a> =
    static member Instance =
        { new IEqualityComparer<'a> with
            member _.Equals (a, b) = a = b
            member _.GetHashCode a = hash a }
[<Struct>]
type KeyValuePair<'K, 'V>(key : 'K, value : 'V) =
    member x.Key = key
    member x.Value = value
// ---- String: the F# String module ----
module String =
    extern let strsub : string -> int -> int -> string
    /// `sub s start count` — the slice, copied. A primitive because building
    /// it out of concatenation is quadratic, and the lexer lives on it.
    let sub (s : string) (start : int) (count : int) : string = strsub s start count
    let length (s : string) = s.Length
    let concat (sep : string) (strings : seq<string>) =
        let mutable acc = ""
        let mutable first = true
        for x in strings do
            if first then
                acc <- x
                first <- false
            else acc <- acc + sep + x
        acc
    let replicate (n : int) (s : string) =
        let mutable acc = ""
        let mutable i = 0
        while i < n do
            acc <- acc + s
            i <- i + 1
        acc
    let init (n : int) (f : int -> string) =
        let mutable acc = ""
        let mutable i = 0
        while i < n do
            acc <- acc + f i
            i <- i + 1
        acc
    let exists (p : char -> bool) (s : string) =
        let mutable found = false
        let mutable i = 0
        while i < s.Length do
            if p s.[i] then found <- true
            i <- i + 1
        found
    let forall (p : char -> bool) (s : string) =
        let mutable ok = true
        let mutable i = 0
        while i < s.Length do
            if not (p s.[i]) then ok <- false
            i <- i + 1
        ok
    let iter (f : char -> unit) (s : string) =
        let mutable i = 0
        while i < s.Length do
            f s.[i]
            i <- i + 1
    let iteri (f : int -> char -> unit) (s : string) =
        let mutable i = 0
        while i < s.Length do
            f i s.[i]
            i <- i + 1
    let map (f : char -> char) (s : string) =
        let mutable acc = ""
        let mutable i = 0
        while i < s.Length do
            acc <- acc + string (f s.[i])
            i <- i + 1
        acc
// ---- Array: the F# Array module ----
module Array =
    extern let create : int -> 'a -> 'a[]
    extern let zeroCreate : int -> 'a[]
    extern let pin : 'a[] -> int
    extern let unpin : 'a[] -> int
    let length (xs : 'a[]) = xs.Length
    let isEmpty (xs : 'a[]) = xs.Length = 0
    let item (i : int) (xs : 'a[]) = xs.[i]
    let copy (xs : 'a[]) : 'a[] =
        let n = xs.Length
        let r = zeroCreate n
        let mutable i = 0
        while i < n do
            r.[i] <- xs.[i]
            i <- i + 1
        r
    let sub (xs : 'a[]) (start : int) (count : int) : 'a[] =
        let r = zeroCreate count
        let mutable i = 0
        while i < count do
            r.[i] <- xs.[start + i]
            i <- i + 1
        r
    let fill (xs : 'a[]) (start : int) (count : int) (value : 'a) =
        let mutable i = 0
        while i < count do
            xs.[start + i] <- value
            i <- i + 1
    let blit (src : 'a[]) (srcIndex : int) (dst : 'a[]) (dstIndex : int) (count : int) =
        let mutable i = 0
        while i < count do
            dst.[dstIndex + i] <- src.[srcIndex + i]
            i <- i + 1
    let init (n : int) (f : int -> 'a) : 'a[] =
        let r = zeroCreate n
        let mutable i = 0
        while i < n do
            r.[i] <- f i
            i <- i + 1
        r
    let rev (xs : 'a[]) : 'a[] =
        let n = xs.Length
        let r = zeroCreate n
        let mutable i = 0
        while i < n do
            r.[i] <- xs.[n - 1 - i]
            i <- i + 1
        r
    let append (a : 'a[]) (b : 'a[]) : 'a[] =
        let r = zeroCreate (a.Length + b.Length)
        let mutable i = 0
        while i < a.Length do
            r.[i] <- a.[i]
            i <- i + 1
        let mutable j = 0
        while j < b.Length do
            r.[a.Length + j] <- b.[j]
            j <- j + 1
        r
    let map (f : 'a -> 'b) (xs : 'a[]) : 'b[] =
        let n = xs.Length
        let r = zeroCreate n
        let mutable i = 0
        while i < n do
            r.[i] <- f xs.[i]
            i <- i + 1
        r
    let mapi (f : int -> 'a -> 'b) (xs : 'a[]) : 'b[] =
        let n = xs.Length
        let r = zeroCreate n
        let mutable i = 0
        while i < n do
            r.[i] <- f i xs.[i]
            i <- i + 1
        r
    let map2 (f : 'a -> 'b -> 'c) (a : 'a[]) (b : 'b[]) : 'c[] =
        if a.Length <> b.Length then failwith "the arrays have different lengths"
        let r = zeroCreate a.Length
        let mutable i = 0
        while i < a.Length do
            r.[i] <- f a.[i] b.[i]
            i <- i + 1
        r
    let iter (f : 'a -> unit) (xs : 'a[]) =
        let mutable i = 0
        while i < xs.Length do
            f xs.[i]
            i <- i + 1
    let iteri (f : int -> 'a -> unit) (xs : 'a[]) =
        let mutable i = 0
        while i < xs.Length do
            f i xs.[i]
            i <- i + 1
    let exists (p : 'a -> bool) (xs : 'a[]) =
        let mutable found = false
        let mutable i = 0
        while i < xs.Length && not found do
            if p xs.[i] then found <- true
            i <- i + 1
        found
    let forall (p : 'a -> bool) (xs : 'a[]) =
        let mutable ok = true
        let mutable i = 0
        while i < xs.Length && ok do
            if not (p xs.[i]) then ok <- false
            i <- i + 1
        ok
    let contains (value : 'a) (xs : 'a[]) = exists (fun x -> x = value) xs
    let tryFind (p : 'a -> bool) (xs : 'a[]) : option<'a> =
        let mutable found = None
        let mutable i = 0
        while i < xs.Length && (match found with None -> true | Some _ -> false) do
            if p xs.[i] then found <- Some xs.[i]
            i <- i + 1
        found
    let find (p : 'a -> bool) (xs : 'a[]) =
        match tryFind p xs with
        | Some x -> x
        | None -> raise (KeyNotFoundException "no element matches the predicate")
    let tryPick (f : 'a -> option<'b>) (xs : 'a[]) : option<'b> =
        let mutable picked = None
        let mutable i = 0
        while i < xs.Length && (match picked with None -> true | Some _ -> false) do
            picked <- f xs.[i]
            i <- i + 1
        picked
    let pick (f : 'a -> option<'b>) (xs : 'a[]) =
        match tryPick f xs with
        | Some x -> x
        | None -> raise (KeyNotFoundException "no element was picked")
    let filter (p : 'a -> bool) (xs : 'a[]) : 'a[] =
        let mutable acc = []
        let mutable n = 0
        for x in xs do
            if p x then
                acc <- x :: acc
                n <- n + 1
        let r = zeroCreate n
        let mutable i = n - 1
        for x in acc do
            r.[i] <- x
            i <- i - 1
        r
    let choose (f : 'a -> option<'b>) (xs : 'a[]) : 'b[] =
        let mutable acc = []
        let mutable n = 0
        for x in xs do
            match f x with
            | Some y ->
                acc <- y :: acc
                n <- n + 1
            | None -> ()
        let r = zeroCreate n
        let mutable i = n - 1
        for y in acc do
            r.[i] <- y
            i <- i - 1
        r
    let collect (f : 'a -> 'b[]) (xs : 'a[]) : 'b[] =
        let mutable acc = []
        let mutable n = 0
        for x in xs do
            let ys = f x
            acc <- ys :: acc
            n <- n + ys.Length
        let r = zeroCreate n
        let mutable i = n
        for ys in acc do
            i <- i - ys.Length
            let mutable j = 0
            while j < ys.Length do
                r.[i + j] <- ys.[j]
                j <- j + 1
        r
    let fold (f : 's -> 'a -> 's) (state : 's) (xs : 'a[]) =
        let mutable acc = state
        for x in xs do
            acc <- f acc x
        acc
    let foldBack (f : 'a -> 's -> 's) (xs : 'a[]) (state : 's) =
        let mutable acc = state
        let mutable i = xs.Length - 1
        while i >= 0 do
            acc <- f xs.[i] acc
            i <- i - 1
        acc
    let reduce (f : 'a -> 'a -> 'a) (xs : 'a[]) =
        if xs.Length = 0 then failwith "the array is empty"
        let mutable acc = xs.[0]
        let mutable i = 1
        while i < xs.Length do
            acc <- f acc xs.[i]
            i <- i + 1
        acc
    let sum (xs : 'a[]) : 'a when Num<'a> =
        let mutable acc = Zero
        for x in xs do
            acc <- acc + x
        acc
    let sumBy (f : 'a -> 'b) (xs : 'a[]) : 'b when Num<'b> =
        let mutable acc = Zero
        for x in xs do
            acc <- acc + f x
        acc
    let max (xs : 'a[]) : 'a when Ordered<'a> =
        reduce (fun a b -> if compare a b >= 0 then a else b) xs
    let min (xs : 'a[]) : 'a when Ordered<'a> =
        reduce (fun a b -> if compare a b <= 0 then a else b) xs
    let maxBy (f : 'a -> 'k) (xs : 'a[]) : 'a when Ordered<'k> =
        reduce (fun a b -> if compare (f a) (f b) >= 0 then a else b) xs
    let minBy (f : 'a -> 'k) (xs : 'a[]) : 'a when Ordered<'k> =
        reduce (fun a b -> if compare (f a) (f b) <= 0 then a else b) xs
    let sortWith (cmp : 'a -> 'a -> int) (xs : 'a[]) : 'a[] =
        // bottom-up stable merge sort into a swap buffer
        let n = xs.Length
        let mutable a = copy xs
        let mutable b = zeroCreate n
        let mutable width = 1
        while width < n do
            let mutable lo = 0
            while lo < n do
                let mid = if lo + width < n then lo + width else n
                let hi = if lo + width + width < n then lo + width + width else n
                let mutable i = lo
                let mutable j = mid
                let mutable k = lo
                while k < hi do
                    if i < mid && (j >= hi || cmp a.[i] a.[j] <= 0) then
                        b.[k] <- a.[i]
                        i <- i + 1
                    else
                        b.[k] <- a.[j]
                        j <- j + 1
                    k <- k + 1
                lo <- lo + width + width
            let t = a
            a <- b
            b <- t
            width <- width + width
        a
    let sort (xs : 'a[]) : 'a[] when Ordered<'a> = sortWith compare xs
    let sortBy (f : 'a -> 'k) (xs : 'a[]) : 'a[] when Ordered<'k> =
        sortWith (fun a b -> compare (f a) (f b)) xs
    let toList (xs : 'a[]) : 'a list =
        let mutable acc = []
        let mutable i = xs.Length - 1
        while i >= 0 do
            acc <- xs.[i] :: acc
            i <- i - 1
        acc
    let ofList (xs : 'a list) : 'a[] =
        let mutable n = 0
        for _ in xs do n <- n + 1
        let r = zeroCreate n
        let mutable i = 0
        for x in xs do
            r.[i] <- x
            i <- i + 1
        r
    let toSeq (xs : 'a[]) : seq<'a> = xs :> seq<'a>
    let ofSeq (xs : seq<'a>) : 'a[] =
        let mutable n = 0
        for _ in xs do n <- n + 1
        let r = zeroCreate n
        let mutable i = 0
        for x in xs do
            r.[i] <- x
            i <- i + 1
        r
    let zip (a : 'a[]) (b : 'b[]) : ('a * 'b)[] =
        if a.Length <> b.Length then failwith "the arrays have different lengths"
        let r = zeroCreate a.Length
        let mutable i = 0
        while i < a.Length do
            r.[i] <- (a.[i], b.[i])
            i <- i + 1
        r
    let unzip (xs : ('a * 'b)[]) : 'a[] * 'b[] =
        let a = zeroCreate xs.Length
        let b = zeroCreate xs.Length
        let mutable i = 0
        while i < xs.Length do
            let x, y = xs.[i]
            a.[i] <- x
            b.[i] <- y
            i <- i + 1
        a, b
// ---- List: the F# List module ----
module List =
    let length (xs : 'a list) =
        let mutable n = 0
        for _ in xs do n <- n + 1
        n
    let isEmpty (xs : 'a list) =
        match xs with
        | [] -> true
        | _ -> false
    let head (xs : 'a list) =
        match xs with
        | x :: _ -> x
        | [] -> failwith "the list is empty"
    let tryHead (xs : 'a list) =
        match xs with
        | x :: _ -> Some x
        | [] -> None
    let tail (xs : 'a list) =
        match xs with
        | _ :: t -> t
        | [] -> failwith "the list is empty"
    let rec last (xs : 'a list) =
        match xs with
        | [ x ] -> x
        | _ :: t -> last t
        | [] -> failwith "the list is empty"
    let rec tryLast (xs : 'a list) =
        match xs with
        | [ x ] -> Some x
        | _ :: t -> tryLast t
        | [] -> None
    let rev (xs : 'a list) =
        let mutable acc = []
        for x in xs do
            acc <- x :: acc
        acc
    let append (a : 'a list) (b : 'a list) =
        let mutable acc = b
        for x in rev a do
            acc <- x :: acc
        acc
    let concat (xss : list<list<'a>>) =
        let mutable acc = []
        for xs in xss do
            for x in xs do
                acc <- x :: acc
        rev acc
    let map (f : 'a -> 'b) (xs : 'a list) =
        let mutable acc = []
        for x in xs do
            acc <- f x :: acc
        rev acc
    let mapi (f : int -> 'a -> 'b) (xs : 'a list) =
        let mutable acc = []
        let mutable i = 0
        for x in xs do
            acc <- f i x :: acc
            i <- i + 1
        rev acc
    let map2 (f : 'a -> 'b -> 'c) (a : 'a list) (b : 'b list) =
        let mutable acc = []
        let mutable l = a
        let mutable r = b
        let mutable go = true
        while go do
            match l, r with
            | x :: lt, y :: rt ->
                acc <- f x y :: acc
                l <- lt
                r <- rt
            | [], [] -> go <- false
            | _ -> failwith "the lists have different lengths"
        rev acc
    let iter (f : 'a -> unit) (xs : 'a list) =
        for x in xs do f x
    let iteri (f : int -> 'a -> unit) (xs : 'a list) =
        let mutable i = 0
        for x in xs do
            f i x
            i <- i + 1
    let exists (p : 'a -> bool) (xs : 'a list) =
        let mutable found = false
        for x in xs do
            if not found then found <- p x
        found
    let forall (p : 'a -> bool) (xs : 'a list) =
        let mutable ok = true
        for x in xs do
            if ok then ok <- p x
        ok
    let contains (value : 'a) (xs : 'a list) = exists (fun x -> x = value) xs
    let filter (p : 'a -> bool) (xs : 'a list) =
        let mutable acc = []
        for x in xs do
            if p x then acc <- x :: acc
        rev acc
    let choose (f : 'a -> option<'b>) (xs : 'a list) =
        let mutable acc = []
        for x in xs do
            match f x with
            | Some y -> acc <- y :: acc
            | None -> ()
        rev acc
    let collect (f : 'a -> 'b list) (xs : 'a list) =
        let mutable acc = []
        for x in xs do
            for y in f x do
                acc <- y :: acc
        rev acc
    let fold (f : 's -> 'a -> 's) (state : 's) (xs : 'a list) =
        let mutable acc = state
        for x in xs do
            acc <- f acc x
        acc
    let foldBack (f : 'a -> 's -> 's) (xs : 'a list) (state : 's) =
        let mutable acc = state
        for x in rev xs do
            acc <- f x acc
        acc
    let reduce (f : 'a -> 'a -> 'a) (xs : 'a list) =
        match xs with
        | [] -> failwith "the list is empty"
        | x :: t -> fold f x t
    let tryFind (p : 'a -> bool) (xs : 'a list) : option<'a> =
        let mutable found = None
        for x in xs do
            match found with
            | None -> if p x then found <- Some x
            | Some _ -> ()
        found
    let find (p : 'a -> bool) (xs : 'a list) =
        match tryFind p xs with
        | Some x -> x
        | None -> raise (KeyNotFoundException "no element matches the predicate")
    let tryPick (f : 'a -> option<'b>) (xs : 'a list) : option<'b> =
        let mutable picked = None
        for x in xs do
            match picked with
            | None -> picked <- f x
            | Some _ -> ()
        picked
    let pick (f : 'a -> option<'b>) (xs : 'a list) =
        match tryPick f xs with
        | Some x -> x
        | None -> raise (KeyNotFoundException "no element was picked")
    let init (n : int) (f : int -> 'a) =
        let mutable acc = []
        let mutable i = n - 1
        while i >= 0 do
            acc <- f i :: acc
            i <- i - 1
        acc
    let replicate (n : int) (value : 'a) =
        let mutable acc = []
        let mutable i = 0
        while i < n do
            acc <- value :: acc
            i <- i + 1
        acc
    let item (n : int) (xs : 'a list) =
        let mutable rest = xs
        let mutable i = 0
        while i < n do
            rest <- tail rest
            i <- i + 1
        head rest
    let tryItem (n : int) (xs : 'a list) : option<'a> =
        let mutable rest = xs
        let mutable i = 0
        let mutable ok = n >= 0
        while ok && i < n do
            match rest with
            | _ :: t ->
                rest <- t
                i <- i + 1
            | [] -> ok <- false
        if ok then tryHead rest else None
    let splitAt (n : int) (xs : 'a list) =
        let mutable front = []
        let mutable rest = xs
        let mutable i = 0
        while i < n do
            (match rest with
             | x :: t ->
                 front <- x :: front
                 rest <- t
             | [] -> failwith "the list is shorter than the split point")
            i <- i + 1
        rev front, rest
    let sum (xs : 'a list) : 'a when Num<'a> =
        let mutable acc = Zero
        for x in xs do
            acc <- acc + x
        acc
    let sumBy (f : 'a -> 'b) (xs : 'a list) : 'b when Num<'b> =
        let mutable acc = Zero
        for x in xs do
            acc <- acc + f x
        acc
    let max (xs : 'a list) : 'a when Ordered<'a> =
        reduce (fun a b -> if compare a b >= 0 then a else b) xs
    let min (xs : 'a list) : 'a when Ordered<'a> =
        reduce (fun a b -> if compare a b <= 0 then a else b) xs
    let maxBy (f : 'a -> 'k) (xs : 'a list) : 'a when Ordered<'k> =
        reduce (fun a b -> if compare (f a) (f b) >= 0 then a else b) xs
    let minBy (f : 'a -> 'k) (xs : 'a list) : 'a when Ordered<'k> =
        reduce (fun a b -> if compare (f a) (f b) <= 0 then a else b) xs
    let rec sortWith (cmp : 'a -> 'a -> int) (xs : 'a list) : 'a list =
        // stable merge sort: split in the middle, merge preferring the left
        match xs with
        | [] -> xs
        | [ _ ] -> xs
        | _ ->
            let front, back = splitAt (length xs / 2) xs
            let mutable l = sortWith cmp front
            let mutable r = sortWith cmp back
            let mutable acc = []
            let mutable go = true
            while go do
                match l, r with
                | x :: lt, y :: rt ->
                    if cmp x y <= 0 then
                        acc <- x :: acc
                        l <- lt
                    else
                        acc <- y :: acc
                        r <- rt
                | x :: t, [] ->
                    acc <- x :: acc
                    l <- t
                | [], y :: t ->
                    acc <- y :: acc
                    r <- t
                | [], [] -> go <- false
            rev acc
    let sort (xs : 'a list) : 'a list when Ordered<'a> = sortWith compare xs
    let sortBy (f : 'a -> 'k) (xs : 'a list) : 'a list when Ordered<'k> =
        sortWith (fun a b -> compare (f a) (f b)) xs
    let zip (a : 'a list) (b : 'b list) = map2 (fun x y -> (x, y)) a b
    let unzip (xs : list<'a * 'b>) =
        let mutable la = []
        let mutable lb = []
        for p in xs do
            let x, y = p
            la <- x :: la
            lb <- y :: lb
        rev la, rev lb
    let toArray (xs : 'a list) : 'a[] = Array.ofList xs
    let ofArray (xs : 'a[]) : 'a list = Array.toList xs
    let toSeq (xs : 'a list) : seq<'a> = xs :> seq<'a>
    let ofSeq (xs : seq<'a>) : 'a list =
        let mutable acc = []
        for x in xs do
            acc <- x :: acc
        rev acc
// ---- Seq: lazy combinators over the enumerator protocol ----
module Seq =
    let map (f : 'a -> 'b) (xs : seq<'a>) : seq<'b> =
        { new IEnumerable<'b> with
            member _.GetEnumerator() =
                let en = xs.GetEnumerator()
                { new IEnumerator<'b> with
                    member _.MoveNext() = en.MoveNext()
                    member _.Current = f en.Current } }
    let filter (p : 'a -> bool) (xs : seq<'a>) : seq<'a> =
        { new IEnumerable<'a> with
            member _.GetEnumerator() =
                let en = xs.GetEnumerator()
                { new IEnumerator<'a> with
                    member _.MoveNext() =
                        let mutable found = false
                        let mutable more = true
                        while more && not found do
                            if en.MoveNext() then found <- p en.Current
                            else more <- false
                        found
                    member _.Current = en.Current } }
    let truncate (n : int) (xs : seq<'a>) : seq<'a> =
        { new IEnumerable<'a> with
            member _.GetEnumerator() =
                let en = xs.GetEnumerator()
                let mutable k = 0
                { new IEnumerator<'a> with
                    member _.MoveNext() =
                        if k >= n then false
                        elif en.MoveNext() then
                            k <- k + 1
                            true
                        else false
                    member _.Current = en.Current } }
    let take (n : int) (xs : seq<'a>) : seq<'a> =
        { new IEnumerable<'a> with
            member _.GetEnumerator() =
                let en = xs.GetEnumerator()
                let mutable k = 0
                { new IEnumerator<'a> with
                    member _.MoveNext() =
                        if k >= n then false
                        elif en.MoveNext() then
                            k <- k + 1
                            true
                        else failwith "the sequence has fewer elements than Seq.take asked for"
                    member _.Current = en.Current } }
    let skip (n : int) (xs : seq<'a>) : seq<'a> =
        { new IEnumerable<'a> with
            member _.GetEnumerator() =
                let en = xs.GetEnumerator()
                let mutable skipped = false
                { new IEnumerator<'a> with
                    member _.MoveNext() =
                        if not skipped then
                            skipped <- true
                            let mutable i = 0
                            let mutable ok = true
                            while ok && i < n do
                                if en.MoveNext() then i <- i + 1
                                else ok <- false
                            if ok then en.MoveNext() else false
                        else en.MoveNext()
                    member _.Current = en.Current } }
    let append (a : seq<'a>) (b : seq<'a>) : seq<'a> =
        { new IEnumerable<'a> with
            member _.GetEnumerator() =
                let mutable second = false
                let mutable en = a.GetEnumerator()
                { new IEnumerator<'a> with
                    member _.MoveNext() =
                        if en.MoveNext() then true
                        elif second then false
                        else
                            second <- true
                            en <- b.GetEnumerator()
                            en.MoveNext()
                    member _.Current = en.Current } }
    let init (n : int) (f : int -> 'a) : seq<'a> =
        { new IEnumerable<'a> with
            member _.GetEnumerator() =
                let mutable i = -1
                { new IEnumerator<'a> with
                    member _.MoveNext() =
                        if i + 1 < n then
                            i <- i + 1
                            true
                        else false
                    member _.Current = f i } }
    let singleton (value : 'a) : seq<'a> = init 1 (fun _ -> value)
    let replicate (n : int) (value : 'a) : seq<'a> = init n (fun _ -> value)
    let mapi (f : int -> 'a -> 'b) (xs : seq<'a>) : seq<'b> =
        { new IEnumerable<'b> with
            member _.GetEnumerator() =
                let en = xs.GetEnumerator()
                let mutable i = -1
                { new IEnumerator<'b> with
                    member _.MoveNext() =
                        if en.MoveNext() then
                            i <- i + 1
                            true
                        else false
                    member _.Current = f i en.Current } }
    let choose (f : 'a -> option<'b>) (xs : seq<'a>) : seq<'b> =
        { new IEnumerable<'b> with
            member _.GetEnumerator() =
                let en = xs.GetEnumerator()
                let mutable cur = None
                { new IEnumerator<'b> with
                    member _.MoveNext() =
                        let mutable found = false
                        let mutable more = true
                        while more && not found do
                            if en.MoveNext() then
                                match f en.Current with
                                | Some y ->
                                    cur <- Some y
                                    found <- true
                                | None -> ()
                            else more <- false
                        found
                    member _.Current =
                        match cur with
                        | Some y -> y
                        | None -> failwith "the sequence is exhausted" } }
    let collect (f : 'a -> seq<'b>) (xs : seq<'a>) : seq<'b> =
        { new IEnumerable<'b> with
            member _.GetEnumerator() =
                let outer = xs.GetEnumerator()
                let mutable inner = None
                { new IEnumerator<'b> with
                    member _.MoveNext() =
                        let mutable moved = false
                        let mutable searching = true
                        while searching do
                            match inner with
                            | Some en ->
                                if en.MoveNext() then
                                    moved <- true
                                    searching <- false
                                else inner <- None
                            | None ->
                                if outer.MoveNext() then inner <- Some ((f outer.Current).GetEnumerator())
                                else searching <- false
                        moved
                    member _.Current =
                        match inner with
                        | Some en -> en.Current
                        | None -> failwith "the sequence is exhausted" } }
    let exists (p : 'a -> bool) (xs : seq<'a>) =
        let mutable found = false
        for x in xs do
            if not found then found <- p x
        found
    let forall (p : 'a -> bool) (xs : seq<'a>) =
        let mutable ok = true
        for x in xs do
            if ok then ok <- p x
        ok
    let contains (value : 'a) (xs : seq<'a>) = exists (fun x -> x = value) xs
    let tryFind (p : 'a -> bool) (xs : seq<'a>) : option<'a> =
        let mutable found = None
        for x in xs do
            match found with
            | None -> if p x then found <- Some x
            | Some _ -> ()
        found
    let find (p : 'a -> bool) (xs : seq<'a>) =
        match tryFind p xs with
        | Some x -> x
        | None -> raise (KeyNotFoundException "no element matches the predicate")
    let tryPick (f : 'a -> option<'b>) (xs : seq<'a>) : option<'b> =
        let mutable picked = None
        for x in xs do
            match picked with
            | None -> picked <- f x
            | Some _ -> ()
        picked
    let pick (f : 'a -> option<'b>) (xs : seq<'a>) =
        match tryPick f xs with
        | Some x -> x
        | None -> raise (KeyNotFoundException "no element was picked")
    let fold (f : 's -> 'a -> 's) (state : 's) (xs : seq<'a>) =
        let mutable acc = state
        for x in xs do
            acc <- f acc x
        acc
    let reduce (f : 'a -> 'a -> 'a) (xs : seq<'a>) =
        let en = xs.GetEnumerator()
        if not (en.MoveNext()) then failwith "the sequence is empty"
        let mutable acc = en.Current
        while en.MoveNext() do
            acc <- f acc en.Current
        acc
    let iter (f : 'a -> unit) (xs : seq<'a>) =
        for x in xs do f x
    let iteri (f : int -> 'a -> unit) (xs : seq<'a>) =
        let mutable i = 0
        for x in xs do
            f i x
            i <- i + 1
    let length (xs : seq<'a>) =
        let mutable k = 0
        for x in xs do
            k <- k + 1
        k
    let isEmpty (xs : seq<'a>) =
        let en = xs.GetEnumerator()
        not (en.MoveNext())
    let head (xs : seq<'a>) =
        let en = xs.GetEnumerator()
        if en.MoveNext() then en.Current
        else failwith "the sequence is empty"
    let tryHead (xs : seq<'a>) : option<'a> =
        let en = xs.GetEnumerator()
        if en.MoveNext() then Some en.Current
        else None
    let last (xs : seq<'a>) =
        let en = xs.GetEnumerator()
        if not (en.MoveNext()) then failwith "the sequence is empty"
        let mutable acc = en.Current
        while en.MoveNext() do
            acc <- en.Current
        acc
    let tryLast (xs : seq<'a>) : option<'a> =
        let mutable acc = None
        for x in xs do
            acc <- Some x
        acc
    let sum (xs : seq<'a>) : 'a when Num<'a> =
        let mutable acc = Zero
        for x in xs do
            acc <- acc + x
        acc
    let sumBy (f : 'a -> 'b) (xs : seq<'a>) : 'b when Num<'b> =
        let mutable acc = Zero
        for x in xs do
            acc <- acc + f x
        acc
    let max (xs : seq<'a>) : 'a when Ordered<'a> =
        reduce (fun a b -> if compare a b >= 0 then a else b) xs
    let min (xs : seq<'a>) : 'a when Ordered<'a> =
        reduce (fun a b -> if compare a b <= 0 then a else b) xs
    let toList (xs : seq<'a>) : 'a list = List.ofSeq xs
    let ofList (xs : 'a list) : seq<'a> = xs :> seq<'a>
    let toArray (xs : seq<'a>) : 'a[] = Array.ofSeq xs
    let ofArray (xs : 'a[]) : seq<'a> = xs :> seq<'a>
    let rev (xs : seq<'a>) : seq<'a> = Array.toSeq (Array.rev (Array.ofSeq xs))
    let sortWith (cmp : 'a -> 'a -> int) (xs : seq<'a>) : seq<'a> =
        Array.toSeq (Array.sortWith cmp (Array.ofSeq xs))
    let sort (xs : seq<'a>) : seq<'a> when Ordered<'a> = sortWith compare xs
    let sortBy (f : 'a -> 'k) (xs : seq<'a>) : seq<'a> when Ordered<'k> =
        sortWith (fun a b -> compare (f a) (f b)) xs

// ---- Set: the F# Set module ----
// Comparison-ordered like F#'s, but backed by a sorted array rather than a
// tree: membership is a binary search, and the structure-sharing a tree buys
// on `add`/`remove` is traded for a copy. Persistent either way — a Set value
// is never mutated once built.
type Set<'a> = { SetItems : 'a[] }

module Set =
    /// index of `x`, or -(insertion point) - 1 when absent
    let private search (s : Set<'a>) (x : 'a) : int when Ordered<'a> =
        let mutable lo = 0
        let mutable hi = s.SetItems.Length - 1
        let mutable found = -1
        while found < 0 && lo <= hi do
            let mid = lo + (hi - lo) / 2
            let c = compare s.SetItems.[mid] x
            if c = 0 then found <- mid
            elif c < 0 then lo <- mid + 1
            else hi <- mid - 1
        if found >= 0 then found else -lo - 1

    let count (s : Set<'a>) : int = s.SetItems.Length
    let isEmpty (s : Set<'a>) : bool = s.SetItems.Length = 0
    let toArray (s : Set<'a>) : 'a[] = Array.copy s.SetItems
    let toList (s : Set<'a>) : 'a list = Array.toList s.SetItems
    let toSeq (s : Set<'a>) : seq<'a> = Array.toSeq (Array.copy s.SetItems)
    let contains (x : 'a) (s : Set<'a>) : bool when Ordered<'a> = search s x >= 0

    let ofArray (xs : 'a[]) : Set<'a> when Ordered<'a> =
        let sorted = Array.sort xs
        let items : 'a[] = Array.zeroCreate sorted.Length
        let mutable n = 0
        let mutable i = 0
        while i < sorted.Length do
            if n = 0 || compare items.[n - 1] sorted.[i] <> 0 then
                items.[n] <- sorted.[i]
                n <- n + 1
            i <- i + 1
        { SetItems = Array.sub items 0 n }

    let ofList (xs : 'a list) : Set<'a> when Ordered<'a> = ofArray (List.toArray xs)
    let ofSeq (xs : seq<'a>) : Set<'a> when Ordered<'a> = ofArray (Array.ofSeq xs)
    let singleton (x : 'a) : Set<'a> = { SetItems = Array.create 1 x }
    let empty (u : unit) : Set<'a> = { SetItems = Array.zeroCreate 0 }

    let add (x : 'a) (s : Set<'a>) : Set<'a> when Ordered<'a> =
        let at = search s x
        if at >= 0 then s
        else
            let ip = -at - 1
            let items : 'a[] = Array.zeroCreate (s.SetItems.Length + 1)
            let mutable i = 0
            while i < ip do
                items.[i] <- s.SetItems.[i]
                i <- i + 1
            items.[ip] <- x
            while i < s.SetItems.Length do
                items.[i + 1] <- s.SetItems.[i]
                i <- i + 1
            { SetItems = items }

    let remove (x : 'a) (s : Set<'a>) : Set<'a> when Ordered<'a> =
        let at = search s x
        if at < 0 then s
        else
            let items : 'a[] = Array.zeroCreate (s.SetItems.Length - 1)
            let mutable i = 0
            while i < at do
                items.[i] <- s.SetItems.[i]
                i <- i + 1
            while i < s.SetItems.Length - 1 do
                items.[i] <- s.SetItems.[i + 1]
                i <- i + 1
            { SetItems = items }

    let filter (p : 'a -> bool) (s : Set<'a>) : Set<'a> = { SetItems = Array.filter p s.SetItems }
    let exists (p : 'a -> bool) (s : Set<'a>) : bool = Array.exists p s.SetItems
    let forall (p : 'a -> bool) (s : Set<'a>) : bool = Array.forall p s.SetItems
    let iter (f : 'a -> unit) (s : Set<'a>) : unit = Array.iter f s.SetItems
    let fold (f : 'b -> 'a -> 'b) (state : 'b) (s : Set<'a>) : 'b = Array.fold f state s.SetItems
    let map (f : 'a -> 'b) (s : Set<'a>) : Set<'b> when Ordered<'b> = ofArray (Array.map f s.SetItems)
    let minElement (s : Set<'a>) : 'a = s.SetItems.[0]
    let maxElement (s : Set<'a>) : 'a = s.SetItems.[s.SetItems.Length - 1]

    let union (a : Set<'a>) (b : Set<'a>) : Set<'a> when Ordered<'a> =
        ofArray (Array.append a.SetItems b.SetItems)
    let difference (a : Set<'a>) (b : Set<'a>) : Set<'a> when Ordered<'a> =
        { SetItems = Array.filter (fun x -> search b x < 0) a.SetItems }
    let intersect (a : Set<'a>) (b : Set<'a>) : Set<'a> when Ordered<'a> =
        { SetItems = Array.filter (fun x -> search b x >= 0) a.SetItems }
    let isSubset (a : Set<'a>) (b : Set<'a>) : bool when Ordered<'a> =
        Array.forall (fun x -> search b x >= 0) a.SetItems
    let isSuperset (a : Set<'a>) (b : Set<'a>) : bool when Ordered<'a> = isSubset b a
