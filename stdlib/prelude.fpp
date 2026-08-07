[<AutoOpen>]
class Add<'a, 'b>
    type Result
    static (+) : 'a -> 'b -> Result
[<AutoOpen>]
class Sub<'a, 'b>
    type Result
    static (-) : 'a -> 'b -> Result
[<AutoOpen>]
class Mul<'a, 'b>
    type Result
    static (*) : 'a -> 'b -> Result
[<AutoOpen>]
class Div<'a, 'b>
    type Result
    static (/) : 'a -> 'b -> Result
[<AutoOpen>]
class Rem<'a, 'b>
    type Result
    static (%) : 'a -> 'b -> Result
[<AutoOpen>]
class Num<'a>
    when Add<'a, 'a> = 'a
    when Sub<'a, 'a> = 'a
    when Mul<'a, 'a> = 'a
    static Zero : 'a
    static One : 'a
[<AutoOpen>]
class Fractional<'a>
    when Num<'a>
    when Div<'a, 'a> = 'a
[<AutoOpen>]
class Integral<'a>
    when Num<'a>
    when Div<'a, 'a> = 'a
    when Rem<'a, 'a> = 'a
/// F#'s `unmanaged` constraint: the type is BLITTABLE — no references, a
/// fixed size, and a layout that matches C's. It is what the compiler
/// already decides when it lays out a POD array or matches emscripten's
/// struct padding; as a class, user code can demand it too, which is what a
/// zero-copy buffer needs.
///
/// A marker: the instance carries the size, because that is the fact a
/// caller actually wants and the one the layout already knows.
[<AutoOpen>]
class Unmanaged<'a>
    static byteSize : int

[<AutoOpen>]
class Ordered<'a>
    static compare : 'a -> 'a -> int
[<AutoOpen>]
class Neg<'a>
    static (~-) : 'a -> 'a
[<AutoOpen>]
class Abs<'a>
    static abs : 'a -> 'a
[<AutoOpen>]
class MinMax<'a>
    static min : 'a -> 'a -> 'a
    static max : 'a -> 'a -> 'a
[<AutoOpen>]
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
// ---- uint64: the same tower as uint32, on the 64-bit rail --------------
instance Add<uint64, uint64>
    type Result = uint64
instance Sub<uint64, uint64>
    type Result = uint64
instance Mul<uint64, uint64>
    type Result = uint64
instance Div<uint64, uint64>
    type Result = uint64
instance Rem<uint64, uint64>
    type Result = uint64
instance Num<uint64>
    static Zero = 0UL
    static One = 1UL
instance Integral<uint64>
instance Ordered<uint64>
instance MinMax<uint64>
    static min a b = if a < b then a else b
    static max a b = if a > b then a else b

// ---- int16 and uint16: int-SHAPED, so the operators are the integer ones
// and only the WIDTH (and, for int16, the sign extension) differs
instance Add<int16, int16>
    type Result = int16
instance Sub<int16, int16>
    type Result = int16
instance Mul<int16, int16>
    type Result = int16
instance Div<int16, int16>
    type Result = int16
instance Rem<int16, int16>
    type Result = int16
instance Num<int16>
    static Zero = 0s
    static One = 1s
instance Integral<int16>
instance Ordered<int16>
instance Neg<int16>
instance Abs<int16>
instance MinMax<int16>
    static min a b = if a < b then a else b
    static max a b = if a > b then a else b

instance Add<uint16, uint16>
    type Result = uint16
instance Sub<uint16, uint16>
    type Result = uint16
instance Mul<uint16, uint16>
    type Result = uint16
instance Div<uint16, uint16>
    type Result = uint16
instance Rem<uint16, uint16>
    type Result = uint16
instance Num<uint16>
    static Zero = 0us
    static One = 1us
instance Integral<uint16>
instance Ordered<uint16>
instance MinMax<uint16>
    static min a b = if a < b then a else b
    static max a b = if a > b then a else b

// byte and sbyte carry the whole tower too: int-SHAPED like int16, so the
// operators are the integer ones and the conversion is what narrows
instance Add<byte, byte>
    type Result = byte
instance Sub<byte, byte>
    type Result = byte
instance Mul<byte, byte>
    type Result = byte
instance Div<byte, byte>
    type Result = byte
instance Rem<byte, byte>
    type Result = byte
instance Num<byte>
    static Zero = 0uy
    static One = 1uy
instance Integral<byte>
instance Unmanaged<int>
    static byteSize = 4
instance Unmanaged<uint32>
    static byteSize = 4
instance Unmanaged<int64>
    static byteSize = 8
instance Unmanaged<uint64>
    static byteSize = 8
instance Unmanaged<float>
    static byteSize = 8
instance Unmanaged<float32>
    static byteSize = 4
instance Unmanaged<float16>
    static byteSize = 2
instance Unmanaged<byte>
    static byteSize = 1
instance Unmanaged<sbyte>
    static byteSize = 1
instance Unmanaged<int16>
    static byteSize = 2
instance Unmanaged<uint16>
    static byteSize = 2
instance Unmanaged<char>
    static byteSize = 2
instance Unmanaged<bool>
    static byteSize = 1

instance Ordered<byte>
instance MinMax<byte>
    static min a b = if a < b then a else b
    static max a b = if a > b then a else b
instance Add<sbyte, sbyte>
    type Result = sbyte
instance Sub<sbyte, sbyte>
    type Result = sbyte
instance Mul<sbyte, sbyte>
    type Result = sbyte
instance Div<sbyte, sbyte>
    type Result = sbyte
instance Rem<sbyte, sbyte>
    type Result = sbyte
instance Num<sbyte>
    static Zero = 0y
    static One = 1y
instance Integral<sbyte>
instance Neg<sbyte>
instance Abs<sbyte>
instance Ordered<sbyte>
instance MinMax<sbyte>
    static min a b = if a < b then a else b
    static max a b = if a > b then a else b
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
/// `use x = e` calls this at the end of the scope. wasm-GC has no
/// finalizers, so disposal is only ever what the program asks for — there is
/// no collector to fall back on, and a leaked handle stays leaked.
type IDisposable =
    abstract member Dispose : unit -> unit
/// .NET's `IEnumerator<'T>` inherits `IDisposable`, and real F# relies on it:
/// `use e = xs.GetEnumerator()` is how a library walks a sequence it did not
/// build. Every implementation therefore carries a `Dispose`, and a wrapping
/// enumerator passes it on to the one it wraps.
type IEnumerator<'a> =
    abstract member MoveNext : unit -> bool
    abstract member Current : 'a
    abstract member Dispose : unit -> unit
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

// The result of a multi-case ACTIVE PATTERN. `let (|Add|Rem|) x = ...`
// compiles to a function returning one of these, and both the constructors
// in its body and the case patterns at its use sites are rewritten onto the
// corresponding case. One type per case count; the payload of a case that
// carries several values is a tuple, which is what F# does too.
/// A BYREF parameter — `member x.TryGetValue (k, value : byref<'v>)`.
///
/// wasm has no address of a local, so a byref is a one-field CELL and the
/// call site copies in and out around the call: `f (&x)` builds a cell from
/// `x`, calls, and writes the cell back into `x`. Single-threaded, that is
/// exactly what a real byref does; what it is not is an alias, so two
/// byrefs to the same variable do not see each other's writes mid-call.
/// One cell, two jobs. F# has `byref<'T>` for a location a callee may write
/// and `Ref<'T>` for one a program passes around; wasm-GC has no address of
/// a local, so both are this. What tells them apart is the DECLARATION: a
/// parameter written `byref` reads as its value, and a `ref` cell reads as
/// itself, which is exactly how the two behave in F#.
type ByRefCell<'a> = { mutable Value : 'a }
/// A TRUE byref: an aliasing view over a location. `&location` builds one;
/// reads and writes through it reach the original. A plain ByRefCell still
/// flows wherever a byref is expected (out-params, `ref` identity), so
/// every byref deref dispatches on which of the two arrived.
type ByRefView<'a> = { Get : (unit -> 'a); Set : ('a -> unit) }
type byref<'a> = ByRefCell<'a>
type outref<'a> = ByRefCell<'a>
type Ref<'a> = ByRefCell<'a>
/// `ref` is a type AND a function, as it is in F#: `ref<int>` is the cell's
/// type and `ref 5` makes one.
type ref<'a> = ByRefCell<'a>
let ref (value : 'a) : Ref<'a> = { Value = value }


type ActiveChoice2<'a, 'b> =
    | Choice2Of1 of 'a
    | Choice2Of2 of 'b
type ActiveChoice3<'a, 'b, 'c> =
    | Choice3Of1 of 'a
    | Choice3Of2 of 'b
    | Choice3Of3 of 'c
type ActiveChoice4<'a, 'b, 'c, 'd> =
    | Choice4Of1 of 'a
    | Choice4Of2 of 'b
    | Choice4Of3 of 'c
    | Choice4Of4 of 'd
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
instance Ordered<StructTuple2<'a, 'b>> when Ordered<'a> when Ordered<'b>
    static compare (x : StructTuple2<'a, 'b>) (y : StructTuple2<'a, 'b>) =
        let c = compare x.Item1 y.Item1
        if c <> 0 then c else compare x.Item2 y.Item2
[<Struct>]
type StructTuple3<'a, 'b, 'c> = { Item1 : 'a; Item2 : 'b; Item3 : 'c }
[<Struct>]
type StructTuple4<'a, 'b, 'c, 'd> = { Item1 : 'a; Item2 : 'b; Item3 : 'c; Item4 : 'd }
/// .NET's ordering hook. `Compare(a, b)` is negative, zero or positive —
/// the tupled member shape is what ported code calls.
type IComparer<'a> =
    abstract member Compare : 'a * 'a -> int
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
// ---- the identity function ----
let id (x : 'a) : 'a = x
/// first-class: `ignore` passed as a VALUE (a callback slot, a constructor
/// argument) has to be a real function. Applied directly it still emits as
/// the backend's drop.
let ignore (_ : 'a) : unit = ()

// Boxing is a TYPE-level operation here: every value is already a reference
// at runtime, so both of these lower to their argument. `obj` is the top
// type the subtyping check already knows.
extern let box : 'a -> obj
/// A half's 16 BITS, as an int. The runtime representation of float16 IS
/// that bit pattern, so this is the identity — it exists to give source a
/// way to name the pattern rather than the number.
extern let float16Bits : float16 -> int
/// A double's/single's IEEE bits — what a binary emitter writes for a float
/// constant. Lowered to the wasm reinterpret instructions.
extern let doubleBits : float -> int64
extern let singleBits : float32 -> int
extern let unbox : obj -> 'a

// ---- Option: the F# Option module ----
/// The F# math surface the Floating class does not carry as a member:
/// these are ordinary functions over the class operations above.
let floor (x : float) : float =
    let t = truncate x
    if x < 0.0 && t <> x then t - 1.0 else t
let ceil (x : float) : float =
    let t = truncate x
    if x > 0.0 && t <> x then t + 1.0 else t
/// F#'s `round` is Math.Round: HALF-TO-EVEN, so 2.5 -> 2 and 3.5 -> 4
let round (x : float) : float =
    let f = floor x
    let d = x - f
    if d > 0.5 then f + 1.0
    elif d < 0.5 then f
    else
        let half = f / 2.0
        if truncate half = half then f else f + 1.0
let log10 (x : float) : float = log x / log 10.0
let infinity : float = 1.0 / 0.0
let nan : float = 0.0 / 0.0
/// integer power, by squaring — F#'s pown
let pown (x : float) (n : int) : float =
    let mutable acc = 1.0
    let mutable b = if n < 0 then 1.0 / x else x
    let mutable k = if n < 0 then 0 - n else n
    while k > 0 do
        if k % 2 = 1 then acc <- acc * b
        b <- b * b
        k <- k / 2
    acc

/// System.Double's statics, as F# spells them
module Double =
    let IsNaN (x : float) : bool = x <> x
    let IsInfinity (x : float) : bool = x = infinity || x = 0.0 - infinity
    let IsPositiveInfinity (x : float) : bool = x = infinity
    let IsNegativeInfinity (x : float) : bool = x = 0.0 - infinity
    let IsFinite (x : float) : bool = not (IsNaN x) && not (IsInfinity x)
    // COMPUTED, not written as decimal literals: the two hosts parse floats
    // with different code (.NET's correctly-rounded Double.Parse vs the
    // bootstrap prelude's own parseFloat), and an extreme literal lands on
    // different bits in the two stages — which the byte fixpoint catches.
    // Every step below is exact in IEEE double.
    let MaxValue : float = (2.0 - pown 2.0 (0 - 52)) * pown 2.0 1023
    let MinValue : float = 0.0 - MaxValue
    /// the smallest positive denormal, 2^-1074
    let Epsilon : float =
        let mutable e = 1.0
        for _ in 1 .. 1074 do
            e <- e / 2.0
        e

/// Parsing, shared by every integral Parse below. .NET accepts leading and
/// trailing whitespace and an optional sign, and REFUSES everything else —
/// including an empty string and a lone sign.
let private parseDigits (s : string) : int64 =
    let mutable i = 0
    let mutable j = s.Length
    while i < j && (s.[i] = ' ' || s.[i] = '\t' || s.[i] = '\n' || s.[i] = '\r') do i <- i + 1
    while j > i && (s.[j - 1] = ' ' || s.[j - 1] = '\t' || s.[j - 1] = '\n' || s.[j - 1] = '\r') do j <- j - 1
    let neg = i < j && s.[i] = '-'
    if i < j && (s.[i] = '-' || s.[i] = '+') then i <- i + 1
    if i >= j then failwith ("The input string '" + s + "' was not in a correct format.")
    let mutable acc = 0L
    while i < j do
        let c = s.[i]
        if c < '0' || c > '9' then failwith ("The input string '" + s + "' was not in a correct format.")
        acc <- acc * 10L + int64 (int c - int '0')
        i <- i + 1
    if neg then 0L - acc else acc

module Int32 =
    let MaxValue : int = 2147483647
    // written as an expression: `-2147483648` lexes as unary minus applied
    // to 2147483648, which does not fit in an int
    let MinValue : int = 0 - 2147483647 - 1
    let Parse (s : string) : int = int (parseDigits s)

/// F#'s `sign`, which is Math.Sign: -1, 0 or 1, at any ordered number.
let sign (x : 'a) : int when Num<'a> when Ordered<'a> =
    if x < Zero then 0 - 1
    elif x > Zero then 1
    else 0

/// System.Math. Everything here is a .NET STATIC, so it is called in tuple
/// form where it takes more than one argument (`Math.Max (a, b)`) — the same
/// source has to compile under F#. The single-argument ones are the class
/// operations under their .NET names, so `Math.Abs -3` is an int exactly as
/// A deterministic PRNG for property-based generation: same seed, same
/// values, on every platform.
type Rand(seed : int) =
    let mutable state = seed
    member x.Next (bound : int) : int =
        state <- (state * 1103515245 + 12345) &&& 0x3FFFFFFF
        if bound <= 0 then 0 else state % bound
    member x.NextFloat () : float =
        float (x.Next 1000000) / 1000000.0

/// Property-based generation. Instances are written ONLY for primitives and
/// containers: the compiler DERIVES an instance for any record or union
/// that declares none — fields generate recursively, a union picks a case
/// at random and generates its payload.
[<AutoOpen>]
class Arb<'a>
    static arbitrary : Rand -> 'a

instance Arb<int>
    static arbitrary (r : Rand) = r.Next 201 - 100
instance Arb<int64>
    static arbitrary (r : Rand) = int64 (r.Next 201 - 100)
instance Arb<bool>
    static arbitrary (r : Rand) = r.Next 2 = 1
instance Arb<float>
    static arbitrary (r : Rand) = r.NextFloat () * 200.0 - 100.0
instance Arb<string>
    static arbitrary (r : Rand) = string (r.Next 100000)
instance Arb<list<'a>> when Arb<'a>
    static arbitrary (r : Rand) =
        let n = r.Next 8
        let mutable out : list<'a> = []
        let mutable i = 0
        while i < n do
            out <- arbitrary r :: out
            i <- i + 1
        out
instance Arb<'a[]> when Arb<'a>
    static arbitrary (r : Rand) =
        let n = r.Next 8
        let mutable out : list<'a> = []
        let mutable i = 0
        while i < n do
            out <- arbitrary r :: out
            i <- i + 1
        Array.ofList out
instance Arb<option<'a>> when Arb<'a>
    static arbitrary (r : Rand) = if r.Next 4 = 0 then None else Some (arbitrary r)
instance Arb<'a * 'b> when Arb<'a> when Arb<'b>
    static arbitrary (r : Rand) = (arbitrary r, arbitrary r)
instance Arb<'a * 'b * 'c> when Arb<'a> when Arb<'b> when Arb<'c>
    static arbitrary (r : Rand) = (arbitrary r, arbitrary r, arbitrary r)

/// The list a countable range denotes: `[ a .. b ]` and a range used as a
/// VALUE both lower to this, at every Integral element. For-loops keep
/// their direct while lowering and never allocate the list.
type RangeOps =
    static member Seq (lo : 'a, hi : 'a) : list<'a> when Integral<'a> when Ordered<'a> =
        let mutable i = hi
        let mutable out : list<'a> = []
        while i >= lo do
            out <- i :: out
            i <- i - One
        out

/// it is in .NET, not a float.
module Math =
    let PI : float = 3.141592653589793
    let E : float = 2.718281828459045
    let Abs (x : 'a) : 'a when Abs<'a> = abs x
    let Sign (x : 'a) : int when Num<'a> when Ordered<'a> = sign x
    let Max (a : 'a, b : 'a) : 'a when MinMax<'a> = max a b
    let Min (a : 'a, b : 'a) : 'a when MinMax<'a> = min a b
    let Sqrt (x : float) : float = sqrt x
    let Pow (a : float, b : float) : float = pow a b
    let Exp (x : float) : float = exp x
    let Log (x : float) : float = log x
    let Log10 (x : float) : float = log10 x
    let Floor (x : float) : float = floor x
    /// .NET spells it Ceiling; F#'s operator is `ceil`
    let Ceiling (x : float) : float = ceil x
    /// HALF-TO-EVEN, like Math.Round and F#'s `round`
    let Round (x : float) : float = round x
    let Truncate (x : float) : float = truncate x
    let Sin (x : float) : float = sin x
    let Cos (x : float) : float = cos x
    let Tan (x : float) : float = tan x
    let Asin (x : float) : float = asin x
    let Acos (x : float) : float = acos x
    let Atan (x : float) : float = atan x
    let Atan2 (y : float, x : float) : float = atan2 y x
    let Sinh (x : float) : float = sinh x
    let Cosh (x : float) : float = cosh x
    let Tanh (x : float) : float = tanh x

/// The remaining numeric statics, spelled as .NET spells them. Written as
/// expressions rather than literals wherever the literal would not lex: a
/// minimum is one past the negated maximum, and `-2147483648` is unary minus
/// applied to a number that does not fit.
module Int64 =
    let MaxValue : int64 = 9223372036854775807L
    let MinValue : int64 = 0L - 9223372036854775807L - 1L
    let Parse (s : string) : int64 = parseDigits s

module UInt32 =
    let MaxValue : uint32 = 4294967295u
    let MinValue : uint32 = 0u

module UInt64 =
    // 2^64 - 1, built rather than written: the literal does not fit an int64
    // and the two hosts must not disagree about what it parsed to
    let MaxValue : uint64 = 0UL - 1UL
    let MinValue : uint64 = 0UL

module Int16 =
    let MaxValue : int16 = 32767s
    let MinValue : int16 = 0s - 32767s - 1s

module UInt16 =
    let MaxValue : uint16 = 65535us
    let MinValue : uint16 = 0us

module Boolean =
    /// .NET compares case-insensitively and trims, and accepts nothing else
    let Parse (s : string) : bool =
        let t = s.Trim ()
        if t = "true" || t = "True" || t = "TRUE" then true
        elif t = "false" || t = "False" || t = "FALSE" then false
        else failwith "String was not recognized as a valid Boolean."

module Byte =
    let MaxValue : byte = 255uy
    let MinValue : byte = 0uy

module SByte =
    let MaxValue : sbyte = 127y
    let MinValue : sbyte = 0y - 127y - 1y

module Single =
    let MaxValue : float32 = 3.4028234663852886e38f
    let MinValue : float32 = 0.0f - 3.4028234663852886e38f
    let Epsilon : float32 = 1.401298464324817e-45f
    let IsNaN (x : float32) : bool = x <> x
    let IsInfinity (x : float32) : bool =
        x = 1.0f / 0.0f || x = 0.0f - 1.0f / 0.0f
    let IsPositiveInfinity (x : float32) : bool = x = 1.0f / 0.0f
    let IsNegativeInfinity (x : float32) : bool = x = 0.0f - 1.0f / 0.0f
    let IsFinite (x : float32) : bool = not (IsNaN x) && not (IsInfinity x)

module Option =
    let isSome (o : 'a option) : bool = match o with Some _ -> true | None -> false
    let isNone (o : 'a option) : bool = match o with Some _ -> false | None -> true
    let map (f : 'a -> 'b) (o : 'a option) : 'b option =
        match o with
        | Some x -> Some (f x)
        | None -> None
    let bind (f : 'a -> 'b option) (o : 'a option) : 'b option =
        match o with
        | Some x -> f x
        | None -> None
    let filter (p : 'a -> bool) (o : 'a option) : 'a option =
        match o with
        | Some x -> if p x then Some x else None
        | None -> None
    let forall (p : 'a -> bool) (o : 'a option) : bool =
        match o with
        | Some x -> p x
        | None -> true
    let exists (p : 'a -> bool) (o : 'a option) : bool =
        match o with
        | Some x -> p x
        | None -> false
    let iter (f : 'a -> unit) (o : 'a option) : unit =
        match o with
        | Some x -> f x
        | None -> ()
    let defaultValue (fallback : 'a) (o : 'a option) : 'a =
        match o with
        | Some x -> x
        | None -> fallback
    let toList (o : 'a option) : 'a list = match o with Some x -> [ x ] | None -> []

// ---- tuple projections ----
    let defaultWith (f : unit -> 'a) (o : 'a option) : 'a =
        match o with Some x -> x | None -> f ()
    let orElse (ifNone : 'a option) (o : 'a option) : 'a option =
        match o with Some _ -> o | None -> ifNone
    let orElseWith (f : unit -> 'a option) (o : 'a option) : 'a option =
        match o with Some _ -> o | None -> f ()
    let map2 (f : 'a -> 'b -> 'c) (a : 'a option) (b : 'b option) : 'c option =
        match a, b with
        | Some x, Some y -> Some (f x y)
        | _ -> None
    let map3 (f : 'a -> 'b -> 'c -> 'd) (a : 'a option) (b : 'b option) (c : 'c option) : 'd option =
        match a, b, c with
        | Some x, Some y, Some z -> Some (f x y z)
        | _ -> None
    let flatten (o : 'a option option) : 'a option =
        match o with Some x -> x | None -> None
    let count (o : 'a option) : int =
        match o with Some _ -> 1 | None -> 0
    let fold (f : 's -> 'a -> 's) (st : 's) (o : 'a option) : 's =
        match o with Some x -> f st x | None -> st
    let foldBack (f : 'a -> 's -> 's) (o : 'a option) (st : 's) : 's =
        match o with Some x -> f x st | None -> st
    let contains (v : 'a) (o : 'a option) : bool =
        match o with Some x -> x = v | None -> false
    let toArray (o : 'a option) : 'a[] =
        match o with Some x -> [| x |] | None -> [||]
    let get (o : 'a option) : 'a =
        match o with
        | Some x -> x
        | None -> failwith "The option value was None"

/// Result: the other half of F#'s error-handling pair. Ok/Error already
/// exist as the type's cases; this is the module of operations over them.
module Result =
    let map (f : 'a -> 'b) (r : Result<'a, 'e>) : Result<'b, 'e> =
        match r with
        | Ok x -> Ok (f x)
        | Error e -> Error e
    let mapError (f : 'e -> 'f) (r : Result<'a, 'e>) : Result<'a, 'f> =
        match r with
        | Ok x -> Ok x
        | Error e -> Error (f e)
    let bind (f : 'a -> Result<'b, 'e>) (r : Result<'a, 'e>) : Result<'b, 'e> =
        match r with
        | Ok x -> f x
        | Error e -> Error e
    let isOk (r : Result<'a, 'e>) : bool =
        match r with Ok _ -> true | Error _ -> false
    let isError (r : Result<'a, 'e>) : bool =
        match r with Ok _ -> false | Error _ -> true
    let defaultValue (v : 'a) (r : Result<'a, 'e>) : 'a =
        match r with Ok x -> x | Error _ -> v
    let defaultWith (f : 'e -> 'a) (r : Result<'a, 'e>) : 'a =
        match r with Ok x -> x | Error e -> f e
    let toOption (r : Result<'a, 'e>) : 'a option =
        match r with Ok x -> Some x | Error _ -> None
    let toList (r : Result<'a, 'e>) : 'a list =
        match r with Ok x -> [ x ] | Error _ -> []
    let toArray (r : Result<'a, 'e>) : 'a[] =
        match r with Ok x -> [| x |] | Error _ -> [||]
    let count (r : Result<'a, 'e>) : int =
        match r with Ok _ -> 1 | Error _ -> 0
    let fold (f : 's -> 'a -> 's) (st : 's) (r : Result<'a, 'e>) : 's =
        match r with Ok x -> f st x | Error _ -> st
    let foldBack (f : 'a -> 's -> 's) (r : Result<'a, 'e>) (st : 's) : 's =
        match r with Ok x -> f x st | Error _ -> st
    let iter (f : 'a -> unit) (r : Result<'a, 'e>) : unit =
        match r with Ok x -> f x | Error _ -> ()
    let iterError (f : 'e -> unit) (r : Result<'a, 'e>) : unit =
        match r with Ok _ -> () | Error e -> f e
    let exists (p : 'a -> bool) (r : Result<'a, 'e>) : bool =
        match r with Ok x -> p x | Error _ -> false
    let forall (p : 'a -> bool) (r : Result<'a, 'e>) : bool =
        match r with Ok x -> p x | Error _ -> true
    let contains (v : 'a) (r : Result<'a, 'e>) : bool =
        match r with Ok x -> x = v | Error _ -> false

/// Char: the System.Char predicates, ASCII-faithful. Values at or above 128
/// are left alone — F++ strings are byte sequences, so a "letter" beyond
/// ASCII is a UTF-8 continuation the classifier must not claim.
module Char =
    let IsDigit (c : char) : bool = c >= '0' && c <= '9'
    let IsLetter (c : char) : bool =
        (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
    let IsLetterOrDigit (c : char) : bool = IsLetter c || IsDigit c
    let IsWhiteSpace (c : char) : bool =
        c = ' ' || c = '\t' || c = '\n' || c = '\r' || int c = 11 || int c = 12
    let IsUpper (c : char) : bool = c >= 'A' && c <= 'Z'
    let IsLower (c : char) : bool = c >= 'a' && c <= 'z'
    let ToUpper (c : char) : char = if IsLower c then char (int c - 32) else c
    let ToLower (c : char) : char = if IsUpper c then char (int c + 32) else c
    let IsPunctuation (c : char) : bool =
        let i = int c
        (i >= 33 && i <= 47) || (i >= 58 && i <= 64)
        || (i >= 91 && i <= 96) || (i >= 123 && i <= 126)
let defaultArg (o : 'a option) (dflt : 'a) : 'a =
    match o with
    | Some v -> v
    | None -> dflt
let fst (t : 'a * 'b) : 'a = match t with (a, _) -> a
let snd (t : 'a * 'b) : 'b = match t with (_, b) -> b

// ---- Memory: the raw linear memory a pinned POD array lives in ----
// `Array.pin` hands out an address in here, and the image at that address is
// the C layout of the element struct. That is what makes shipping a V2d[]
// a `memory.copy` rather than a walk over its elements: the bytes are
// already the wire format.
module Memory =
    extern let memAlloc : int -> int
    extern let memSize : unit -> int
    extern let memCopy : int -> int -> int -> unit
    extern let memLoadByte : int -> int
    extern let memStoreByte : int -> int -> unit
    extern let memLoadInt : int -> int
    extern let memStoreInt : int -> int -> unit
    extern let memLoadInt64 : int -> int64
    extern let memStoreInt64 : int -> int64 -> unit
    extern let memLoadFloat : int -> float
    extern let memStoreFloat : int -> float -> unit
    /// Bump-allocate `n` bytes, 8-aligned. This heap is never freed: it holds
    /// pinned arrays and message buffers, both of which outlive the call that
    /// made them and are handed to foreign code by address.
    let alloc (n : int) : int = memAlloc n
    /// Total linear memory, in bytes.
    let size () : int = memSize ()
    /// `copy dst src n` — one wasm memory.copy instruction.
    let copy (dst : int) (src : int) (n : int) : unit = memCopy dst src n
    let loadByte (p : int) : int = memLoadByte p
    let storeByte (p : int) (v : int) : unit = memStoreByte p v
    let loadInt (p : int) : int = memLoadInt p
    let storeInt (p : int) (v : int) : unit = memStoreInt p v
    let loadInt64 (p : int) : int64 = memLoadInt64 p
    let storeInt64 (p : int) (v : int64) : unit = memStoreInt64 p v
    let loadFloat (p : int) : float = memLoadFloat p
    let storeFloat (p : int) (v : float) : unit = memStoreFloat p v

// ---- String: the F# String module ----
module Array =
    extern let create : int -> 'a -> 'a[]
    extern let zeroCreate : int -> 'a[]
    extern let pin : 'a[] -> int
    extern let unpin : 'a[] -> int
    /// The bytes a pinned POD struct array occupies — what a blit has to
    /// move. Not `Length * sizeof`: an element is padded out to whole words,
    /// so this is the only number that is right for every struct.
    extern let byteSize : 'a[] -> int
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
    // ---- the two-array family, matching List's ----
    let iter2 (f : 'a -> 'b -> unit) (a : 'a[]) (b : 'b[]) : unit =
        if a.Length <> b.Length then failwith "the arrays have different lengths"
        let mutable i = 0
        while i < a.Length do
            f a.[i] b.[i]
            i <- i + 1
    let forall2 (p : 'a -> 'b -> bool) (a : 'a[]) (b : 'b[]) : bool =
        if a.Length <> b.Length then failwith "the arrays have different lengths"
        let mutable ok = true
        let mutable i = 0
        while i < a.Length && ok do
            if not (p a.[i] b.[i]) then ok <- false
            i <- i + 1
        ok
    let exists2 (p : 'a -> 'b -> bool) (a : 'a[]) (b : 'b[]) : bool =
        if a.Length <> b.Length then failwith "the arrays have different lengths"
        let mutable found = false
        let mutable i = 0
        while i < a.Length && not found do
            if p a.[i] b.[i] then found <- true
            i <- i + 1
        found
    let fold2 (f : 's -> 'a -> 'b -> 's) (state : 's) (a : 'a[]) (b : 'b[]) : 's =
        if a.Length <> b.Length then failwith "the arrays have different lengths"
        let mutable acc = state
        let mutable i = 0
        while i < a.Length do
            acc <- f acc a.[i] b.[i]
            i <- i + 1
        acc
    let indexed (xs : 'a[]) : (int * 'a)[] = mapi (fun i x -> (i, x)) xs
    let scan (f : 's -> 'a -> 's) (state : 's) (xs : 'a[]) : 's[] =
        let out = zeroCreate (xs.Length + 1)
        let mutable acc = state
        out.[0] <- state
        let mutable i = 0
        while i < xs.Length do
            acc <- f acc xs.[i]
            out.[i + 1] <- acc
            i <- i + 1
        out
    let pairwise (xs : 'a[]) : ('a * 'a)[] =
        if xs.Length < 2 then zeroCreate 0
        else init (xs.Length - 1) (fun i -> (xs.[i], xs.[i + 1]))
    let skip (n : int) (xs : 'a[]) : 'a[] =
        if n > xs.Length then failwith "the array is shorter than the skip count"
        sub xs n (xs.Length - n)
    let take (n : int) (xs : 'a[]) : 'a[] =
        if n > xs.Length then failwith "the array has fewer elements than take asked for"
        sub xs 0 n
    let truncate (n : int) (xs : 'a[]) : 'a[] =
        sub xs 0 (if n < xs.Length then n else xs.Length)
    let windowed (size : int) (xs : 'a[]) : 'a[][] =
        if size > xs.Length then zeroCreate 0
        else init (xs.Length - size + 1) (fun i -> sub xs i size)
    let chunkBySize (size : int) (xs : 'a[]) : 'a[][] =
        let n = (xs.Length + size - 1) / size
        init n (fun i ->
            let start = i * size
            let len = if start + size <= xs.Length then size else xs.Length - start
            sub xs start len)
    let distinct (xs : 'a[]) : 'a[] = ofList (List.distinct (toList xs))
    let distinctBy (key : 'a -> 'k) (xs : 'a[]) : 'a[] = ofList (List.distinctBy key (toList xs))
    let except (excluded : 'a[]) (xs : 'a[]) : 'a[] = filter (fun x -> not (contains x excluded)) xs
    let sortDescending (xs : 'a[]) : 'a[] when Ordered<'a> = sortWith (fun a b -> compare b a) xs
    let sortByDescending (f : 'a -> 'k) (xs : 'a[]) : 'a[] when Ordered<'k> =
        sortWith (fun a b -> compare (f b) (f a)) xs


    let zip3 (a : 'a[]) (b : 'b[]) (c : 'c[]) : ('a * 'b * 'c)[] =
        let r = zeroCreate (length a)
        let mutable i = 0
        while i < length a do
            r.[i] <- (a.[i], b.[i], c.[i])
            i <- i + 1
        r
    let unzip3 (xs : ('a * 'b * 'c)[]) : 'a[] * 'b[] * 'c[] =
        let ra = zeroCreate (length xs)
        let rb = zeroCreate (length xs)
        let rc = zeroCreate (length xs)
        let mutable i = 0
        while i < length xs do
            let a, b, c = xs.[i]
            ra.[i] <- a
            rb.[i] <- b
            rc.[i] <- c
            i <- i + 1
        ra, rb, rc
    let map3 (f : 'a -> 'b -> 'c -> 'd) (a : 'a[]) (b : 'b[]) (c : 'c[]) : 'd[] =
        let r = zeroCreate (length a)
        let mutable i = 0
        while i < length a do
            r.[i] <- f a.[i] b.[i] c.[i]
            i <- i + 1
        r
    let mapi2 (f : int -> 'a -> 'b -> 'c) (a : 'a[]) (b : 'b[]) : 'c[] =
        let r = zeroCreate (length a)
        let mutable i = 0
        while i < length a do
            r.[i] <- f i a.[i] b.[i]
            i <- i + 1
        r
    let iteri2 (f : int -> 'a -> 'b -> unit) (a : 'a[]) (b : 'b[]) : unit =
        let mutable i = 0
        while i < length a do
            f i a.[i] b.[i]
            i <- i + 1
    let foldBack2 (f : 'a -> 'b -> 's -> 's) (a : 'a[]) (b : 'b[]) (st : 's) : 's =
        let mutable acc = st
        let mutable i = length a - 1
        while i >= 0 do
            acc <- f a.[i] b.[i] acc
            i <- i - 1
        acc
    let scanBack (f : 'a -> 's -> 's) (xs : 'a[]) (st : 's) : 's[] =
        let r = zeroCreate (length xs + 1)
        r.[length xs] <- st
        let mutable i = length xs - 1
        while i >= 0 do
            r.[i] <- f xs.[i] r.[i + 1]
            i <- i - 1
        r
    let mapFoldBack (f : 'a -> 's -> 'b * 's) (xs : 'a[]) (st : 's) : 'b[] * 's =
        let r = zeroCreate (length xs)
        let mutable acc = st
        let mutable i = length xs - 1
        while i >= 0 do
            let y, s2 = f xs.[i] acc
            r.[i] <- y
            acc <- s2
            i <- i - 1
        r, acc
    let transpose (xss : 'a[][]) : 'a[][] =
        if length xss = 0 then [||]
        else
            let cols = length xss.[0]
            let r = zeroCreate cols
            let mutable j = 0
            while j < cols do
                let col = zeroCreate (length xss)
                let mutable i = 0
                while i < length xss do
                    col.[i] <- xss.[i].[j]
                    i <- i + 1
                r.[j] <- col
                j <- j + 1
            r
    let permute (f : int -> int) (xs : 'a[]) : 'a[] =
        let r = zeroCreate (length xs)
        let mutable i = 0
        while i < length xs do
            r.[f i] <- xs.[i]
            i <- i + 1
        r
    let insertManyAt (i : int) (vs : 'a[]) (xs : 'a[]) : 'a[] =
        let r = zeroCreate (length xs + length vs)
        let mutable k = 0
        while k < i do
            r.[k] <- xs.[k]
            k <- k + 1
        let mutable j = 0
        while j < length vs do
            r.[i + j] <- vs.[j]
            j <- j + 1
        while k < length xs do
            r.[k + length vs] <- xs.[k]
            k <- k + 1
        r
    let removeManyAt (i : int) (n : int) (xs : 'a[]) : 'a[] =
        let r = zeroCreate (length xs - n)
        let mutable k = 0
        while k < length xs do
            if k < i then r.[k] <- xs.[k]
            elif k >= i + n then r.[k - n] <- xs.[k]
            k <- k + 1
        r
    let unfold (f : 's -> ('a * 's) option) (st : 's) : 'a[] =
        let mutable acc = []
        let mutable cur = st
        let mutable go = true
        while go do
            match f cur with
            | Some (v, s2) ->
                acc <- v :: acc
                cur <- s2
            | None -> go <- false
        // acc is reversed; write it back to front
        let n =
            let mutable c = 0
            for _ in acc do c <- c + 1
            c
        let r = zeroCreate n
        let mutable i = n - 1
        for v in acc do
            r.[i] <- v
            i <- i - 1
        r
    /// F#'s sortInPlace* mutate; these do too, and return unit
    let sortInPlaceWith (cmp : 'a -> 'a -> int) (xs : 'a[]) : unit =
        let sorted = sortWith cmp xs
        let mutable i = 0
        while i < length xs do
            xs.[i] <- sorted.[i]
            i <- i + 1
    let sortInPlace (xs : 'a[]) : unit when Ordered<'a> = sortInPlaceWith compare xs
    let sortInPlaceBy (f : 'a -> 'k) (xs : 'a[]) : unit when Ordered<'k> =
        sortInPlaceWith (fun a b -> compare (f a) (f b)) xs
// ---- List: the F# List module ----
    let singleton (x : 'a) : 'a[] = [| x |]
    let head (xs : 'a[]) : 'a =
        if length xs = 0 then failwith "The input array was empty" else xs.[0]
    let last (xs : 'a[]) : 'a =
        if length xs = 0 then failwith "The input array was empty" else xs.[length xs - 1]
    let tryHead (xs : 'a[]) : 'a option =
        if length xs = 0 then None else Some xs.[0]
    let tryLast (xs : 'a[]) : 'a option =
        if length xs = 0 then None else Some xs.[length xs - 1]
    let tryItem (i : int) (xs : 'a[]) : 'a option =
        if i < 0 || i >= length xs then None else Some xs.[i]
    let tail (xs : 'a[]) : 'a[] =
        if length xs = 0 then failwith "The input array was empty" else skip 1 xs
    let findIndex (p : 'a -> bool) (xs : 'a[]) : int =
        let mutable i = 0
        let mutable found = -1
        while found < 0 && i < length xs do
            if p xs.[i] then found <- i
            i <- i + 1
        if found < 0 then failwith "An index satisfying the predicate was not found in the collection."
        else found
    let tryFindIndex (p : 'a -> bool) (xs : 'a[]) : int option =
        let mutable i = 0
        let mutable found = None
        while (match found with None -> true | Some _ -> false) && i < length xs do
            if p xs.[i] then found <- Some i
            i <- i + 1
        found
    let findBack (p : 'a -> bool) (xs : 'a[]) : 'a =
        let mutable i = length xs - 1
        let mutable found = None
        while (match found with None -> true | Some _ -> false) && i >= 0 do
            if p xs.[i] then found <- Some xs.[i]
            i <- i - 1
        match found with
        | Some v -> v
        | None -> failwith "An element satisfying the predicate was not found in the collection."
    let tryFindBack (p : 'a -> bool) (xs : 'a[]) : 'a option =
        let mutable i = length xs - 1
        let mutable found = None
        while (match found with None -> true | Some _ -> false) && i >= 0 do
            if p xs.[i] then found <- Some xs.[i]
            i <- i - 1
        found
    let tryFindIndexBack (p : 'a -> bool) (xs : 'a[]) : int option =
        let mutable i = length xs - 1
        let mutable found = None
        while (match found with None -> true | Some _ -> false) && i >= 0 do
            if p xs.[i] then found <- Some i
            i <- i - 1
        found
    let takeWhile (p : 'a -> bool) (xs : 'a[]) : 'a[] =
        let mutable n = 0
        let mutable go = true
        while go && n < length xs do
            if p xs.[n] then n <- n + 1 else go <- false
        sub xs 0 n
    let skipWhile (p : 'a -> bool) (xs : 'a[]) : 'a[] =
        let mutable n = 0
        let mutable go = true
        while go && n < length xs do
            if p xs.[n] then n <- n + 1 else go <- false
        sub xs n (length xs - n)
    let partition (p : 'a -> bool) (xs : 'a[]) : 'a[] * 'a[] =
        filter p xs, filter (fun x -> not (p x)) xs
    let where (p : 'a -> bool) (xs : 'a[]) : 'a[] = filter p xs
    let concat (xss : 'a[] list) : 'a[] =
        let mutable total = 0
        for xs in xss do total <- total + length xs
        if total = 0 then [||]
        else
            let mutable first = [||]
            for xs in xss do
                if length xs > 0 && length first = 0 then first <- xs
            let r = create total first.[0]
            let mutable k = 0
            for xs in xss do
                for x in xs do
                    r.[k] <- x
                    k <- k + 1
            r
    let allPairs (xs : 'a[]) (ys : 'b[]) : ('a * 'b)[] =
        let r = zeroCreate (length xs * length ys)
        let mutable k = 0
        for x in xs do
            for y in ys do
                r.[k] <- (x, y)
                k <- k + 1
        r
    // Array is declared BEFORE List in this prelude, so these carry their
    // own implementations rather than delegating. Key order is
    // first-occurrence, as F#'s is.
    let countBy (f : 'a -> 'k) (xs : 'a[]) : ('k * int)[] =
        let keys = zeroCreate (length xs)
        let counts = zeroCreate (length xs)
        let mutable n = 0
        for x in xs do
            let k = f x
            let mutable at = -1
            let mutable i = 0
            while at < 0 && i < n do
                if keys.[i] = k then at <- i
                i <- i + 1
            if at < 0 then
                keys.[n] <- k
                counts.[n] <- 1
                n <- n + 1
            else counts.[at] <- counts.[at] + 1
        let r = zeroCreate n
        let mutable j = 0
        while j < n do
            r.[j] <- (keys.[j], counts.[j])
            j <- j + 1
        r
    let groupBy (f : 'a -> 'k) (xs : 'a[]) : ('k * 'a[])[] =
        let keys = zeroCreate (length xs)
        let mutable n = 0
        for x in xs do
            let k = f x
            let mutable at = -1
            let mutable i = 0
            while at < 0 && i < n do
                if keys.[i] = k then at <- i
                i <- i + 1
            if at < 0 then
                keys.[n] <- k
                n <- n + 1
        let r = zeroCreate n
        let mutable j = 0
        while j < n do
            let kj = keys.[j]
            r.[j] <- (kj, filter (fun x -> f x = kj) xs)
            j <- j + 1
        r
    let splitInto (n : int) (xs : 'a[]) : 'a[][] =
        let len = length xs
        if len = 0 then [||]
        else
            let count = if n < len then n else len
            let sz = len / count
            let extra = len % count
            let r = zeroCreate count
            let mutable at = 0
            let mutable i = 0
            while i < count do
                let take_ = if i < extra then sz + 1 else sz
                r.[i] <- sub xs at take_
                at <- at + take_
                i <- i + 1
            r
    let splitAt (n : int) (xs : 'a[]) : 'a[] * 'a[] =
        sub xs 0 n, sub xs n (length xs - n)
    let exactlyOne (xs : 'a[]) : 'a =
        if length xs = 1 then xs.[0]
        elif length xs = 0 then failwith "The input sequence was empty"
        else failwith "The input sequence contains more than one element"
    let tryExactlyOne (xs : 'a[]) : 'a option =
        if length xs = 1 then Some xs.[0] else None
    let reduceBack (f : 'a -> 'a -> 'a) (xs : 'a[]) : 'a =
        if length xs = 0 then failwith "The input array was empty"
        else
            let mutable acc = xs.[length xs - 1]
            let mutable i = length xs - 2
            while i >= 0 do
                acc <- f xs.[i] acc
                i <- i - 1
            acc
    let mapFold (f : 's -> 'a -> 'b * 's) (st : 's) (xs : 'a[]) : 'b[] * 's =
        let r = zeroCreate (length xs)
        let mutable s2 = st
        let mutable i = 0
        while i < length xs do
            let y, s3 = f s2 xs.[i]
            r.[i] <- y
            s2 <- s3
            i <- i + 1
        r, s2
    let insertAt (i : int) (v : 'a) (xs : 'a[]) : 'a[] =
        let r = zeroCreate (length xs + 1)
        let mutable k = 0
        while k < i do
            r.[k] <- xs.[k]
            k <- k + 1
        r.[i] <- v
        while k < length xs do
            r.[k + 1] <- xs.[k]
            k <- k + 1
        r
    let removeAt (i : int) (xs : 'a[]) : 'a[] =
        let r = zeroCreate (length xs - 1)
        let mutable k = 0
        while k < length xs do
            if k < i then r.[k] <- xs.[k]
            elif k > i then r.[k - 1] <- xs.[k]
            k <- k + 1
        r
    let updateAt (i : int) (v : 'a) (xs : 'a[]) : 'a[] =
        let r = copy xs
        r.[i] <- v
        r
    let replicate (n : int) (v : 'a) : 'a[] = create n v
    let average (xs : float[]) : float =
        if length xs = 0 then failwith "The input array was empty"
        else sum xs / float (length xs)
    let averageBy (f : 'a -> float) (xs : 'a[]) : float =
        if length xs = 0 then failwith "The input array was empty"
        else sumBy f xs / float (length xs)
    let reverse (xs : 'a[]) : 'a[] = rev xs
    let findIndexBack (p : 'a -> bool) (xs : 'a[]) : int =
        match tryFindIndexBack p xs with
        | Some i -> i
        | None -> failwith "An index satisfying the predicate was not found in the collection."
    /// LEXICOGRAPHIC: the first non-zero comparison decides, and a prefix
    /// comes before the array it is a prefix of
    let compareWith (cmp : 'a -> 'a -> int) (a : 'a[]) (b : 'a[]) : int =
        let n = if length a < length b then length a else length b
        let mutable r = 0
        let mutable i = 0
        while r = 0 && i < n do
            r <- cmp a.[i] b.[i]
            i <- i + 1
        if r <> 0 then r
        elif length a < length b then 0 - 1
        elif length a > length b then 1
        else 0
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
        // F# applies `f` in ASCENDING index order, and a generator with side
        // effects makes that observable: walking down from n-1 built the same
        // list while running the effects backwards. The compiler's own vtable
        // builder appends to a vector inside `f`, so this emitted its adapter
        // functions in reverse — a self-hosting divergence the byte fixpoint
        // caught and nothing else did.
        let mutable acc = []
        let mutable i = 0
        while i < n do
            acc <- f i :: acc
            i <- i + 1
        rev acc
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
    /// First occurrence wins, order preserved — F#'s own rule.
    let distinctBy (key : 'a -> 'k) (xs : 'a list) : 'a list =
        let mutable seenKeys = []
        let mutable acc = []
        for x in xs do
            let k = key x
            if not (List.exists (fun s -> s = k) seenKeys) then
                seenKeys <- k :: seenKeys
                acc <- x :: acc
        List.rev acc
    let distinct (xs : 'a list) : 'a list = distinctBy (fun x -> x) xs
    /// At most `n` elements — fewer is not an error, as in F#.
    let truncate (n : int) (xs : 'a list) : 'a list =
        let mutable acc = []
        let mutable k = 0
        let mutable rest = xs
        while k < n && not (List.isEmpty rest) do
            acc <- List.head rest :: acc
            rest <- List.tail rest
            k <- k + 1
        List.rev acc
    /// Exactly `n` elements — unlike `truncate`, a short list is an error.
    let take (n : int) (xs : 'a list) : 'a list =
        let mutable acc = []
        let mutable k = 0
        let mutable rest = xs
        while k < n do
            if List.isEmpty rest then failwith "the list is too short"
            acc <- List.head rest :: acc
            rest <- List.tail rest
            k <- k + 1
        List.rev acc
    let tryFindIndex (p : 'a -> bool) (xs : 'a list) : int option =
        let mutable i = 0
        let mutable found = -1
        for x in xs do
            if found < 0 && p x then found <- i
            i <- i + 1
        if found < 0 then None else Some found
    let findIndex (p : 'a -> bool) (xs : 'a list) : int =
        match tryFindIndex p xs with
        | Some i -> i
        | None -> raise (KeyNotFoundException "no element matches the predicate")
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

    // ---- the two-list family: F# spells these *2, and they exist for the
    // same reason zip does — walking a pair of lists in step is common and
    // building an intermediate list of tuples to do it is waste
    let iter2 (f : 'a -> 'b -> unit) (a : 'a list) (b : 'b list) : unit =
        let mutable l = a
        let mutable r = b
        let mutable go = true
        while go do
            match l, r with
            | x :: lt, y :: rt ->
                f x y
                l <- lt
                r <- rt
            | [], [] -> go <- false
            | _ -> failwith "the lists have different lengths"
    let forall2 (p : 'a -> 'b -> bool) (a : 'a list) (b : 'b list) : bool =
        let mutable l = a
        let mutable r = b
        let mutable ok = true
        let mutable go = true
        while go do
            match l, r with
            | x :: lt, y :: rt ->
                if not (p x y) then
                    ok <- false
                    go <- false
                else
                    l <- lt
                    r <- rt
            | [], [] -> go <- false
            | _ -> failwith "the lists have different lengths"
        ok
    let exists2 (p : 'a -> 'b -> bool) (a : 'a list) (b : 'b list) : bool =
        let mutable l = a
        let mutable r = b
        let mutable found = false
        let mutable go = true
        while go do
            match l, r with
            | x :: lt, y :: rt ->
                if p x y then
                    found <- true
                    go <- false
                else
                    l <- lt
                    r <- rt
            | [], [] -> go <- false
            | _ -> failwith "the lists have different lengths"
        found
    let fold2 (f : 's -> 'a -> 'b -> 's) (state : 's) (a : 'a list) (b : 'b list) : 's =
        let mutable acc = state
        let mutable l = a
        let mutable r = b
        let mutable go = true
        while go do
            match l, r with
            | x :: lt, y :: rt ->
                acc <- f acc x y
                l <- lt
                r <- rt
            | [], [] -> go <- false
            | _ -> failwith "the lists have different lengths"
        acc
    // ---- position-aware and shape-changing combinators ----
    let indexed (xs : 'a list) : (int * 'a) list = mapi (fun i x -> (i, x)) xs
    let scan (f : 's -> 'a -> 's) (state : 's) (xs : 'a list) : 's list =
        let mutable acc = state
        let mutable out = [ state ]
        for x in xs do
            acc <- f acc x
            out <- acc :: out
        rev out
    let pairwise (xs : 'a list) : ('a * 'a) list =
        match xs with
        | [] -> []
        | h :: t ->
            let mutable prev = h
            let mutable out = []
            for x in t do
                out <- (prev, x) :: out
                prev <- x
            rev out
    let unfold (gen : 's -> ('a * 's) option) (state : 's) : 'a list =
        let mutable acc = []
        let mutable cur = state
        let mutable go = true
        while go do
            match gen cur with
            | Some (x, next) ->
                acc <- x :: acc
                cur <- next
            | None -> go <- false
        rev acc
    let skip (n : int) (xs : 'a list) : 'a list =
        let mutable rest = xs
        let mutable i = 0
        while i < n do
            match rest with
            | _ :: t -> rest <- t
            | [] -> failwith "the list is shorter than the skip count"
            i <- i + 1
        rest
    let truncate (n : int) (xs : 'a list) : 'a list =
        let mutable out = []
        let mutable rest = xs
        let mutable i = 0
        while i < n && not (isEmpty rest) do
            out <- head rest :: out
            rest <- tail rest
            i <- i + 1
        rev out
    let windowed (size : int) (xs : 'a list) : 'a list list =
        let arr = toArray xs
        let mutable out = []
        let mutable i = 0
        while i + size <= arr.Length do
            out <- ofArray (Array.sub arr i size) :: out
            i <- i + 1
        rev out
    let chunkBySize (size : int) (xs : 'a list) : 'a list list =
        let arr = toArray xs
        let mutable out = []
        let mutable i = 0
        while i < arr.Length do
            let take = if i + size <= arr.Length then size else arr.Length - i
            out <- ofArray (Array.sub arr i take) :: out
            i <- i + size
        rev out
    let except (excluded : 'a list) (xs : 'a list) : 'a list =
        filter (fun x -> not (contains x excluded)) xs
    let distinct (xs : 'a list) : 'a list =
        let mutable seen = []
        let mutable out = []
        for x in xs do
            if not (contains x seen) then
                seen <- x :: seen
                out <- x :: out
        rev out
    let distinctBy (key : 'a -> 'k) (xs : 'a list) : 'a list =
        let mutable seen = []
        let mutable out = []
        for x in xs do
            let k = key x
            if not (contains k seen) then
                seen <- k :: seen
                out <- x :: out
        rev out
    let sortDescending (xs : 'a list) : 'a list when Ordered<'a> =
        sortWith (fun a b -> compare b a) xs
    let sortByDescending (f : 'a -> 'k) (xs : 'a list) : 'a list when Ordered<'k> =
        sortWith (fun a b -> compare (f b) (f a)) xs

    let zip3 (a : 'a list) (b : 'b list) (c : 'c list) : ('a * 'b * 'c) list =
        let mutable acc = []
        let mutable i = 0
        let n = length a
        while i < n do
            acc <- (item i a, item i b, item i c) :: acc
            i <- i + 1
        rev acc
    let unzip3 (xs : ('a * 'b * 'c) list) : 'a list * 'b list * 'c list =
        let mutable ra = []
        let mutable rb = []
        let mutable rc = []
        for a, b, c in xs do
            ra <- a :: ra
            rb <- b :: rb
            rc <- c :: rc
        rev ra, rev rb, rev rc
    let map3 (f : 'a -> 'b -> 'c -> 'd) (a : 'a list) (b : 'b list) (c : 'c list) : 'd list =
        let mutable acc = []
        let mutable i = 0
        let n = length a
        while i < n do
            acc <- f (item i a) (item i b) (item i c) :: acc
            i <- i + 1
        rev acc
    let mapi2 (f : int -> 'a -> 'b -> 'c) (a : 'a list) (b : 'b list) : 'c list =
        let mutable acc = []
        let mutable i = 0
        let n = length a
        while i < n do
            acc <- f i (item i a) (item i b) :: acc
            i <- i + 1
        rev acc
    let iteri2 (f : int -> 'a -> 'b -> unit) (a : 'a list) (b : 'b list) : unit =
        let mutable i = 0
        let n = length a
        while i < n do
            f i (item i a) (item i b)
            i <- i + 1
    let foldBack2 (f : 'a -> 'b -> 's -> 's) (a : 'a list) (b : 'b list) (st : 's) : 's =
        let mutable acc = st
        let mutable i = length a - 1
        while i >= 0 do
            acc <- f (item i a) (item i b) acc
            i <- i - 1
        acc
    let scanBack (f : 'a -> 's -> 's) (xs : 'a list) (st : 's) : 's list =
        let mutable acc = [ st ]
        let mutable cur = st
        let mutable i = length xs - 1
        while i >= 0 do
            cur <- f (item i xs) cur
            acc <- cur :: acc
            i <- i - 1
        acc
    let transpose (xss : 'a list list) : 'a list list =
        if isEmpty xss then []
        else
            let cols = length (head xss)
            let mutable out = []
            let mutable j = cols - 1
            while j >= 0 do
                out <- map (fun (r : 'a list) -> item j r) xss :: out
                j <- j - 1
            out
    let permute (f : int -> int) (xs : 'a list) : 'a list =
        // f maps SOURCE index to DESTINATION index, as F# does
        let n = length xs
        let dst = Array.zeroCreate n
        let mutable i = 0
        for x in xs do
            dst.[f i] <- x
            i <- i + 1
        Array.toList dst
    let insertManyAt (i : int) (vs : 'a list) (xs : 'a list) : 'a list =
        take i xs @ vs @ skip i xs
    let removeManyAt (i : int) (n : int) (xs : 'a list) : 'a list =
        take i xs @ skip (i + n) xs
// ---- Seq: lazy combinators over the enumerator protocol ----
    let empty : 'a list = []
    let singleton (x : 'a) : 'a list = [ x ]
    let partition (p : 'a -> bool) (xs : 'a list) : 'a list * 'a list =
        let mutable yes = []
        let mutable no = []
        for x in xs do
            if p x then yes <- x :: yes else no <- x :: no
        rev yes, rev no
    let takeWhile (p : 'a -> bool) (xs : 'a list) : 'a list =
        let mutable acc = []
        let mutable go = true
        for x in xs do
            if go then
                if p x then acc <- x :: acc else go <- false
        rev acc
    let skipWhile (p : 'a -> bool) (xs : 'a list) : 'a list =
        let mutable rest = xs
        let mutable go = true
        while go do
            match rest with
            | h :: t when p h -> rest <- t
            | _ -> go <- false
        rest
    let countBy (f : 'a -> 'k) (xs : 'a list) : ('k * int) list =
        // first-occurrence key order, like F#
        let mutable keys = []
        let mutable counts = []
        for x in xs do
            let k = f x
            if contains k keys then
                counts <- map (fun (k2, c) -> if k2 = k then k2, c + 1 else k2, c) counts
            else
                keys <- k :: keys
                counts <- counts @ [ k, 1 ]
        counts
    let groupBy (f : 'a -> 'k) (xs : 'a list) : ('k * 'a list) list =
        let mutable keys = []
        let mutable groups = []
        for x in xs do
            let k = f x
            if contains k keys then
                groups <- map (fun (k2, g) -> if k2 = k then k2, g @ [ x ] else k2, g) groups
            else
                keys <- k :: keys
                groups <- groups @ [ k, [ x ] ]
        groups
    let allPairs (xs : 'a list) (ys : 'b list) : ('a * 'b) list =
        let mutable acc = []
        for x in xs do
            for y in ys do
                acc <- (x, y) :: acc
        rev acc
    let exactlyOne (xs : 'a list) : 'a =
        match xs with
        | [ x ] -> x
        | [] -> failwith "The input sequence was empty"
        | _ -> failwith "The input sequence contains more than one element"
    let tryExactlyOne (xs : 'a list) : 'a option =
        match xs with [ x ] -> Some x | _ -> None
    let findBack (p : 'a -> bool) (xs : 'a list) : 'a = find p (rev xs)
    let tryFindBack (p : 'a -> bool) (xs : 'a list) : 'a option = tryFind p (rev xs)
    let findIndexBack (p : 'a -> bool) (xs : 'a list) : int =
        length xs - 1 - findIndex p (rev xs)
    let tryFindIndexBack (p : 'a -> bool) (xs : 'a list) : int option =
        match tryFindIndex p (rev xs) with
        | Some i -> Some (length xs - 1 - i)
        | None -> None
    let reduceBack (f : 'a -> 'a -> 'a) (xs : 'a list) : 'a =
        match rev xs with
        | [] -> failwith "The input list was empty"
        | h :: t -> fold (fun acc x -> f x acc) h t
    let where (p : 'a -> bool) (xs : 'a list) : 'a list = filter p xs
    let insertAt (i : int) (v : 'a) (xs : 'a list) : 'a list =
        let mutable acc = []
        let mutable k = 0
        for x in xs do
            if k = i then acc <- x :: v :: acc else acc <- x :: acc
            k <- k + 1
        if i = k then acc <- v :: acc
        rev acc
    let removeAt (i : int) (xs : 'a list) : 'a list =
        let mutable acc = []
        let mutable k = 0
        for x in xs do
            if k <> i then acc <- x :: acc
            k <- k + 1
        rev acc
    let updateAt (i : int) (v : 'a) (xs : 'a list) : 'a list =
        let mutable acc = []
        let mutable k = 0
        for x in xs do
            acc <- (if k = i then v else x) :: acc
            k <- k + 1
        rev acc
    let mapFold (f : 's -> 'a -> 'b * 's) (st : 's) (xs : 'a list) : 'b list * 's =
        let mutable acc = []
        let mutable s2 = st
        for x in xs do
            let y, s3 = f s2 x
            acc <- y :: acc
            s2 <- s3
        rev acc, s2
    let splitInto (n : int) (xs : 'a list) : 'a list list =
        // F# spreads the remainder over the EARLIER chunks
        let len = length xs
        if len = 0 then []
        else
            let count = if n < len then n else len
            let sz = len / count
            let extra = len % count
            let mutable out = []
            let mutable rest = xs
            let mutable i = 0
            while i < count do
                let take_ = if i < extra then sz + 1 else sz
                out <- take take_ rest :: out
                rest <- skip take_ rest
                i <- i + 1
            rev out
    let average (xs : float list) : float =
        if isEmpty xs then failwith "The input list was empty"
        else sum xs / float (length xs)
    let averageBy (f : 'a -> float) (xs : 'a list) : float =
        if isEmpty xs then failwith "The input list was empty"
        else sumBy f xs / float (length xs)
    /// lexicographic, like Array.compareWith
    let rec compareWith (cmp : 'a -> 'a -> int) (a : 'a list) (b : 'a list) : int =
        match a, b with
        | [], [] -> 0
        | [], _ -> 0 - 1
        | _, [] -> 1
        | x :: xs, y :: ys ->
            let r = cmp x y
            if r <> 0 then r else compareWith cmp xs ys
// String sits AFTER Array and List: toArray/toList/mapi are written in
// terms of Array.init, Array.length and List.init, and a module only sees
// what precedes it.
module String =
    extern let strsub : string -> int -> int -> string
    /// `sub s start count` — the slice, copied. A primitive because building
    /// it out of concatenation is quadratic, and the lexer lives on it.
    let sub (s : string) (start : int) (count : int) : string = strsub s start count
    let length (s : string) = s.Length
    /// Pairwise MERGE, not a left fold. `acc <- acc + sep + x` copies the
    /// whole accumulator at every step, so joining n chunks of total length
    /// L costs O(n*L) — and the compiler's own emitter joins a six-megabyte
    /// module out of hundreds of thousands of chunks, which is why the
    /// compiler compiled to wasm spent hours on a job it does natively in
    /// seconds. Merging adjacent pairs copies each character O(log n) times.
    ///
    /// Cons and `+` are the only tools used: `Array` and `List` are declared
    /// further down this file, and the merge is written as loops rather than
    /// recursion because the first pass is half as long as the input.
    let concat (sep : string) (strings : seq<string>) =
        let mutable cur : string list = []
        let mutable n = 0
        let mutable first = true
        for x in strings do
            // the separator is folded in once, on the way into the merge
            cur <- (if first then x else sep + x) :: cur
            first <- false
            n <- n + 1
        // `cur` is REVERSED, and every pass flips the order again, so which
        // side of a pair comes first alternates with it
        let mutable reversed = true
        while n > 1 do
            let mutable out : string list = []
            let mutable rest = cur
            let mutable more = true
            while more do
                match rest with
                | x :: y :: tail ->
                    out <- (if reversed then y + x else x + y) :: out
                    rest <- tail
                | [ x ] ->
                    out <- x :: out
                    rest <- []
                    more <- false
                | [] -> more <- false
            cur <- out
            reversed <- not reversed
            n <- (n + 1) / 2
        match cur with
        | [ one ] -> one
        | _ -> ""

    // both build through `concat`, for the reason spelled out there: a left
    // fold over `+` copies the accumulator every step
    let replicate (n : int) (s : string) =
        let mutable parts : string list = []
        let mutable i = 0
        while i < n do
            parts <- s :: parts
            i <- i + 1
        concat "" parts
    let init (n : int) (f : int -> string) =
        // ascending, like F# — see the note on List.init
        let mutable parts : string list = []
        let mutable i = 0
        while i < n do
            parts <- f i :: parts
            i <- i + 1
        concat "" (List.rev parts)
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
    let filter (p : char -> bool) (s : string) : string =
        let mutable acc = ""
        let mutable i = 0
        while i < s.Length do
            if p s.[i] then acc <- acc + string s.[i]
            i <- i + 1
        acc
    let collect (f : char -> string) (s : string) : string =
        let mutable acc = ""
        let mutable i = 0
        while i < s.Length do
            acc <- acc + f s.[i]
            i <- i + 1
        acc
    let toArray (s : string) : char[] = Array.init s.Length (fun i -> s.[i])
    let toList (s : string) : char list = List.init s.Length (fun i -> s.[i])
    let ofArray (cs : char[]) : string =
        let mutable acc = ""
        for c in cs do acc <- acc + string c
        acc
    let ofList (cs : char list) : string =
        let mutable acc = ""
        for c in cs do acc <- acc + string c
        acc
    let map (f : char -> char) (s : string) =
        let mutable acc = ""
        let mutable i = 0
        while i < s.Length do
            acc <- acc + string (f s.[i])
            i <- i + 1
        acc
// ---- Array: the F# Array module ----
    let mapi (f : int -> char -> char) (s : string) : string =
        let cs = toArray s
        let mutable i = 0
        while i < Array.length cs do
            cs.[i] <- f i cs.[i]
            i <- i + 1
        ofArray cs
    /// System.String.Join is a .NET static: it is CALLED IN TUPLE FORM, and
    /// the same source has to compile under F#, so the parameter is a tuple
    let Join (sep : string, xs : string list) : string = concat sep xs
    let IsNullOrEmpty (s : string) : bool = isNull s || length s = 0
    let IsNullOrWhiteSpace (s : string) : bool =
        if isNull s then true
        else
            let mutable ws = true
            for c in toArray s do
                if not (c = ' ' || c = '\t' || c = '\n' || c = '\r') then ws <- false
            ws
module Seq =
    let map (f : 'a -> 'b) (xs : seq<'a>) : seq<'b> =
        { new IEnumerable<'b> with
            member _.GetEnumerator() =
                let en = xs.GetEnumerator()
                { new IEnumerator<'b> with
                    member _.MoveNext() = en.MoveNext()
                    member _.Current = f en.Current
                    member _.Dispose() = en.Dispose() } }
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
                    member _.Current = en.Current
                    member _.Dispose() = en.Dispose() } }
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
                    member _.Current = en.Current
                    member _.Dispose() = en.Dispose() } }
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
                    member _.Current = en.Current
                    member _.Dispose() = en.Dispose() } }
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
                    member _.Current = en.Current
                    member _.Dispose() = en.Dispose() } }
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
                    member _.Current = en.Current
                    member _.Dispose() = en.Dispose() } }
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
                    member _.Current = f i
                    member _.Dispose() = () } }
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
                    member _.Current = f i en.Current
                    member _.Dispose() = en.Dispose() } }
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
                        | None -> failwith "the sequence is exhausted"
                    member _.Dispose() = en.Dispose() } }
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
                        | None -> failwith "the sequence is exhausted"
                    member _.Dispose() =
                        (match inner with
                         | Some en -> en.Dispose()
                         | None -> ())
                        outer.Dispose() } }
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

    // ---- the two-sequence family and the position-aware combinators,
    // completing the same surface List and Array carry ----
    let iter2 (f : 'a -> 'b -> unit) (a : seq<'a>) (b : seq<'b>) : unit =
        let ea = a.GetEnumerator()
        let eb = b.GetEnumerator()
        let mutable go = true
        while go do
            if ea.MoveNext() then
                if eb.MoveNext() then f ea.Current eb.Current
                else failwith "the sequences have different lengths"
            else
                if eb.MoveNext() then failwith "the sequences have different lengths"
                go <- false
    let forall2 (p : 'a -> 'b -> bool) (a : seq<'a>) (b : seq<'b>) : bool =
        let mutable ok = true
        iter2 (fun x y -> if not (p x y) then ok <- false) a b
        ok
    let exists2 (p : 'a -> 'b -> bool) (a : seq<'a>) (b : seq<'b>) : bool =
        let mutable found = false
        iter2 (fun x y -> if p x y then found <- true) a b
        found
    let fold2 (f : 's -> 'a -> 'b -> 's) (state : 's) (a : seq<'a>) (b : seq<'b>) : 's =
        let mutable acc = state
        iter2 (fun x y -> acc <- f acc x y) a b
        acc
    let indexed (xs : seq<'a>) : seq<int * 'a> = mapi (fun i x -> (i, x)) xs
    let scan (f : 's -> 'a -> 's) (state : 's) (xs : seq<'a>) : seq<'s> =
        List.toSeq (List.scan f state (toList xs))
    let pairwise (xs : seq<'a>) : seq<'a * 'a> = List.toSeq (List.pairwise (toList xs))
    let unfold (gen : 's -> ('a * 's) option) (state : 's) : seq<'a> =
        List.toSeq (List.unfold gen state)
    let distinct (xs : seq<'a>) : seq<'a> = List.toSeq (List.distinct (toList xs))
    let distinctBy (key : 'a -> 'k) (xs : seq<'a>) : seq<'a> =
        List.toSeq (List.distinctBy key (toList xs))
    let except (excluded : seq<'a>) (xs : seq<'a>) : seq<'a> =
        let ex = List.ofSeq excluded
        filter (fun x -> not (List.contains x ex)) xs
    let windowed (size : int) (xs : seq<'a>) : seq<'a list> =
        List.toSeq (List.windowed size (toList xs))
    let chunkBySize (size : int) (xs : seq<'a>) : seq<'a list> =
        List.toSeq (List.chunkBySize size (toList xs))
    let sortDescending (xs : seq<'a>) : seq<'a> when Ordered<'a> =
        sortWith (fun a b -> compare b a) xs
    let sortByDescending (f : 'a -> 'k) (xs : seq<'a>) : seq<'a> when Ordered<'k> =
        sortWith (fun a b -> compare (f b) (f a)) xs
    let fold2 (f : 's -> 'a -> 'b -> 's) (st : 's) (a : seq<'a>) (b : seq<'b>) : 's =
        List.fold2 f st (toList a) (toList b)
    let forall2 (p : 'a -> 'b -> bool) (a : seq<'a>) (b : seq<'b>) : bool =
        List.forall2 p (toList a) (toList b)
    let zip3 (a : seq<'a>) (b : seq<'b>) (c : seq<'c>) : seq<'a * 'b * 'c> =
        List.toSeq (List.zip3 (toList a) (toList b) (toList c))
    let cast (xs : seq<'a>) : seq<'a> = xs
    let unfold (f : 's -> ('a * 's) option) (st : 's) : seq<'a> =
        List.toSeq (List.unfold f st)
// ---- Set: the F# Set module ----
// Comparison-ordered like F#'s, but backed by a sorted array rather than a
// tree: membership is a binary search, and the structure-sharing a tree buys
// on `add`/`remove` is traded for a copy. Persistent either way — a Set value
// is never mutated once built.
    let empty : seq<'a> = List.toSeq []
    let map2 (f : 'a -> 'b -> 'c) (a : seq<'a>) (b : seq<'b>) : seq<'c> =
        List.toSeq (List.map2 f (toList a) (toList b))
    let map3 (f : 'a -> 'b -> 'c -> 'd) (a : seq<'a>) (b : seq<'b>) (c : seq<'c>) : seq<'d> =
        let la = toList a
        let lb = toList b
        let lc = toList c
        let mutable acc = []
        let mutable i = 0
        let n = List.length la
        while i < n do
            acc <- f (List.item i la) (List.item i lb) (List.item i lc) :: acc
            i <- i + 1
        List.toSeq (List.rev acc)
    let concat (xss : seq<seq<'a>>) : seq<'a> =
        let mutable acc = []
        for xs in xss do
            for x in xs do acc <- x :: acc
        List.toSeq (List.rev acc)
    let item (i : int) (xs : seq<'a>) : 'a = List.item i (toList xs)
    let tryItem (i : int) (xs : seq<'a>) : 'a option = List.tryItem i (toList xs)
    let findIndex (p : 'a -> bool) (xs : seq<'a>) : int = List.findIndex p (toList xs)
    let tryFindIndex (p : 'a -> bool) (xs : seq<'a>) : int option = List.tryFindIndex p (toList xs)
    let maxBy (f : 'a -> 'k) (xs : seq<'a>) : 'a = List.maxBy f (toList xs)
    let minBy (f : 'a -> 'k) (xs : seq<'a>) : 'a = List.minBy f (toList xs)
    let takeWhile (p : 'a -> bool) (xs : seq<'a>) : seq<'a> =
        List.toSeq (List.takeWhile p (toList xs))
    let skipWhile (p : 'a -> bool) (xs : seq<'a>) : seq<'a> =
        List.toSeq (List.skipWhile p (toList xs))
    let countBy (f : 'a -> 'k) (xs : seq<'a>) : seq<'k * int> =
        List.toSeq (List.countBy f (toList xs))
    let groupBy (f : 'a -> 'k) (xs : seq<'a>) : seq<'k * seq<'a>> =
        List.toSeq (List.map (fun (k, g) -> k, List.toSeq g) (List.groupBy f (toList xs)))
    let allPairs (xs : seq<'a>) (ys : seq<'b>) : seq<'a * 'b> =
        List.toSeq (List.allPairs (toList xs) (toList ys))
    let exactlyOne (xs : seq<'a>) : 'a = List.exactlyOne (toList xs)
    let tryExactlyOne (xs : seq<'a>) : 'a option = List.tryExactlyOne (toList xs)
    let where (p : 'a -> bool) (xs : seq<'a>) : seq<'a> = filter p xs
    let foldBack (f : 'a -> 's -> 's) (xs : seq<'a>) (st : 's) : 's =
        List.foldBack f (toList xs) st
    let mapFold (f : 's -> 'a -> 'b * 's) (st : 's) (xs : seq<'a>) : seq<'b> * 's =
        let ys, s2 = List.mapFold f st (toList xs)
        List.toSeq ys, s2
    let average (xs : seq<float>) : float = List.average (toList xs)
    let averageBy (f : 'a -> float) (xs : seq<'a>) : float = List.averageBy f (toList xs)
    let splitInto (n : int) (xs : seq<'a>) : seq<'a list> =
        List.toSeq (List.splitInto n (toList xs))
    let zip (a : seq<'a>) (b : seq<'b>) : seq<'a * 'b> =
        List.toSeq (List.zip (toList a) (toList b))
    let cache (xs : seq<'a>) : seq<'a> = List.toSeq (toList xs)
    let readonly (xs : seq<'a>) : seq<'a> = xs
    /// Really delayed: the thunk runs once per enumeration, not once when
    /// the sequence is built. `seq { }` leans on this — it is where the
    /// laziness of a computation expression comes from.
    let delay (f : unit -> seq<'a>) : seq<'a> =
        { new IEnumerable<'a> with
            member _.GetEnumerator () = (f ()).GetEnumerator () }

    // ---- the rest of the F# Seq surface. Most are the List version over a
    // materialised copy: a seq here is an IEnumerable, and every one of
    // these has to walk it anyway.
    /// The one that must NOT materialise: it has no end.
    let initInfinite (f : int -> 'a) : seq<'a> =
        { new IEnumerable<'a> with
            member _.GetEnumerator () =
                let mutable i = 0 - 1
                { new IEnumerator<'a> with
                    member _.MoveNext () =
                        i <- i + 1
                        true
                    member _.Current = f i
                    member _.Dispose () = () } }
    let tail (xs : seq<'a>) : seq<'a> = List.toSeq (List.tail (toList xs))
    let mapi2 (f : int -> 'a -> 'b -> 'c) (a : seq<'a>) (b : seq<'b>) : seq<'c> =
        List.toSeq (List.mapi2 f (toList a) (toList b))
    let iteri2 (f : int -> 'a -> 'b -> unit) (a : seq<'a>) (b : seq<'b>) : unit =
        List.iteri2 f (toList a) (toList b)
    let foldBack2 (f : 'a -> 'b -> 's -> 's) (a : seq<'a>) (b : seq<'b>) (s : 's) : 's =
        List.foldBack2 f (toList a) (toList b) s
    let scanBack (f : 'a -> 's -> 's) (xs : seq<'a>) (s : 's) : seq<'s> =
        List.toSeq (List.scanBack f (toList xs) s)
    let reduceBack (f : 'a -> 'a -> 'a) (xs : seq<'a>) : 'a =
        List.reduceBack f (toList xs)
    let tryFindBack (p : 'a -> bool) (xs : seq<'a>) : 'a option =
        List.tryFindBack p (toList xs)
    let findBack (p : 'a -> bool) (xs : seq<'a>) : 'a =
        List.findBack p (toList xs)
    let tryFindIndexBack (p : 'a -> bool) (xs : seq<'a>) : int option =
        List.tryFindIndexBack p (toList xs)
    let findIndexBack (p : 'a -> bool) (xs : seq<'a>) : int =
        List.findIndexBack p (toList xs)
    let transpose (xss : seq<seq<'a>>) : seq<seq<'a>> =
        List.toSeq (List.map List.toSeq (List.transpose (List.map toList (toList xss))))
    let permute (f : int -> int) (xs : seq<'a>) : seq<'a> =
        List.toSeq (List.permute f (toList xs))
    let insertAt (i : int) (v : 'a) (xs : seq<'a>) : seq<'a> =
        List.toSeq (List.insertAt i v (toList xs))
    let insertManyAt (i : int) (vs : seq<'a>) (xs : seq<'a>) : seq<'a> =
        List.toSeq (List.insertManyAt i (toList vs) (toList xs))
    let removeAt (i : int) (xs : seq<'a>) : seq<'a> =
        List.toSeq (List.removeAt i (toList xs))
    let removeManyAt (i : int) (n : int) (xs : seq<'a>) : seq<'a> =
        List.toSeq (List.removeManyAt i n (toList xs))
    let updateAt (i : int) (v : 'a) (xs : seq<'a>) : seq<'a> =
        List.toSeq (List.updateAt i v (toList xs))
    let compareWith (cmp : 'a -> 'a -> int) (a : seq<'a>) (b : seq<'a>) : int =
        List.compareWith cmp (toList a) (toList b)
/// Lists and arrays compare LEXICOGRAPHICALLY — element by element, and a
/// prefix comes before what extends it. That is F#'s ordering for both, and
/// without it `List.sort` on a list of lists has no instance to reach for.
instance Ordered<list<'a>> when Ordered<'a>
    static compare (a : list<'a>) (b : list<'a>) : int =
        let mutable x = a
        let mutable y = b
        let mutable r = 0
        while r = 0 && not (List.isEmpty x) && not (List.isEmpty y) do
            r <- compare (List.head x) (List.head y)
            x <- List.tail x
            y <- List.tail y
        if r <> 0 then r
        elif List.isEmpty x then (if List.isEmpty y then 0 else -1)
        else 1
instance Ordered<'a[]> when Ordered<'a>
    static compare (a : 'a[]) (b : 'a[]) : int = Array.compareWith compare a b

/// The builder behind `seq { }`. Every method returns a sequence that is
/// still lazy, so the computation expression is too: `Combine` appends
/// without walking, `Delay` defers to enumeration time, and `For` collects.
///
/// `Using`, `TryWith` and `TryFinally` are absent. Scoping a resource or a
/// handler ACROSS a suspension needs the enumerator to own it, which this
/// representation — a sequence built from combinators — cannot express. The
/// desugaring emits them, so `use` or `try` inside a `seq { }` is an error
/// naming the missing member rather than a wrong answer.
type SeqBuilder() =
    member _.Zero () : seq<'a> = Seq.empty
    member _.Yield (v : 'a) : seq<'a> = Seq.singleton v
    member _.YieldFrom (vs : seq<'a>) : seq<'a> = vs
    member _.Combine (a : seq<'a>, b : seq<'a>) : seq<'a> = Seq.append a b
    member _.Delay (f : unit -> seq<'a>) : seq<'a> = Seq.delay f
    member _.For (xs : seq<'a>, f : 'a -> seq<'b>) : seq<'b> = Seq.collect f xs
    /// The body is a DELAYED sequence, so enumerating it again re-runs it —
    /// which is what makes an iteration of the loop repeatable.
    member _.While (cond : unit -> bool, body : seq<'a>) : seq<'a> =
        { new IEnumerable<'a> with
            member _.GetEnumerator () =
                let mutable cur : IEnumerator<'a> option = None
                { new IEnumerator<'a> with
                    member _.MoveNext () =
                        let mutable answer = false
                        let mutable searching = true
                        while searching do
                            match cur with
                            | Some e ->
                                if e.MoveNext () then
                                    answer <- true
                                    searching <- false
                                else cur <- None
                            | None ->
                                if cond () then cur <- Some (body.GetEnumerator ())
                                else searching <- false
                        answer
                    member _.Current =
                        match cur with
                        | Some e -> e.Current
                        | None -> failwith "the sequence is exhausted"
                    member _.Dispose () =
                        match cur with
                        | Some e -> e.Dispose ()
                        | None -> () } }
let seq = SeqBuilder()

/// The delta vocabulary MapExt/HashMap deltas are expressed in. Named
/// SetOp/RemoveOp because `Set` is already a type here (FSharp.Data.Adaptive
/// spells the cases `Set` and `Remove`).
type ElementOperation<'v> =
    | SetOp of 'v
    | RemoveOp

/// Set is the same AVL tree Map is, with the value slot dropped: a node
/// carries the element, its two children, its height and its count. That
/// buys O(log n) add/remove (the old sorted-array form paid O(n) per insert)
/// and the MapExt combinator surface below.
type Set<'a> =
    | SetEmpty
    | SetNode of 'a * Set<'a> * Set<'a> * int * int

    /// the elements in order — the CANONICAL form of a set, independent of
    /// whatever rotations the insertion order happened to produce
    member x.Items () =
        match x with
        | SetEmpty -> []
        | SetNode (v, l, r, _, _) -> l.Items () @ (v :: r.Items ())

    /// Content equality. Derived equality would compare the TREE, so the same
    /// elements added in a different order could compare unequal; F# compares
    /// content, and so must this.
    member x.Equals (o : Set<'a>) = x.Items () = o.Items ()

    /// must agree with Equals, or a set used as a hash key goes missing
    member x.GetHashCode () = hash (x.Items ())

module Set =
    /// SetEmpty carries no payload, so this is a VALUE — the array form had
    /// to be a unit function (see DIVERGENCES.md), which F# is not
    let empty : Set<'a> = SetEmpty

    let height (s : Set<'a>) : int =
        match s with
        | SetEmpty -> 0
        | SetNode (k, l, r, h, c) -> h

    let count (s : Set<'a>) : int =
        match s with
        | SetEmpty -> 0
        | SetNode (k, l, r, h, c) -> c

    let isEmpty (s : Set<'a>) : bool =
        match s with
        | SetEmpty -> true
        | SetNode (k, l, r, h, c) -> false

    let private mk (k : 'a) (l : Set<'a>) (r : Set<'a>) : Set<'a> =
        let hl = height l
        let hr = height r
        let h = 1 + (if hl > hr then hl else hr)
        SetNode (k, l, r, h, 1 + count l + count r)

    let private rebalance (k : 'a) (l : Set<'a>) (r : Set<'a>) : Set<'a> =
        let hl = height l
        let hr = height r
        if hl > hr + 1 then
            match l with
            | SetNode (lk, ll, lr, lh, lc) ->
                if height ll >= height lr then mk lk ll (mk k lr r)
                else
                    match lr with
                    | SetNode (lrk, lrl, lrr, lrh, lrc) -> mk lrk (mk lk ll lrl) (mk k lrr r)
                    | SetEmpty -> mk k l r
            | SetEmpty -> mk k l r
        elif hr > hl + 1 then
            match r with
            | SetNode (rk, rl, rr, rh, rc) ->
                if height rr >= height rl then mk rk (mk k l rl) rr
                else
                    match rl with
                    | SetNode (rlk, rll, rlr, rlh, rlc) -> mk rlk (mk k l rll) (mk rk rlr rr)
                    | SetEmpty -> mk k l r
            | SetEmpty -> mk k l r
        else mk k l r

    let rec add (x : 'a) (s : Set<'a>) : Set<'a> when Ordered<'a> =
        match s with
        | SetEmpty -> SetNode (x, SetEmpty, SetEmpty, 1, 1)
        | SetNode (k, l, r, h, c) ->
            let d = compare x k
            if d = 0 then SetNode (x, l, r, h, c)
            elif d < 0 then rebalance k (add x l) r
            else rebalance k l (add x r)

    let rec contains (x : 'a) (s : Set<'a>) : bool when Ordered<'a> =
        match s with
        | SetEmpty -> false
        | SetNode (k, l, r, h, c) ->
            let d = compare x k
            if d = 0 then true
            elif d < 0 then contains x l
            else contains x r

    let rec tryMin (s : Set<'a>) : 'a option =
        match s with
        | SetEmpty -> None
        | SetNode (k, l, r, h, c) ->
            match l with
            | SetEmpty -> Some k
            | SetNode (a, b, cc, d, e) -> tryMin l

    let rec tryMax (s : Set<'a>) : 'a option =
        match s with
        | SetEmpty -> None
        | SetNode (k, l, r, h, c) ->
            match r with
            | SetEmpty -> Some k
            | SetNode (a, b, cc, d, e) -> tryMax r

    let rec private removeMinNode (s : Set<'a>) : Set<'a> when Ordered<'a> =
        match s with
        | SetEmpty -> SetEmpty
        | SetNode (k, l, r, h, c) ->
            match l with
            | SetEmpty -> r
            | SetNode (a, b, cc, d, e) -> rebalance k (removeMinNode l) r

    let rec remove (x : 'a) (s : Set<'a>) : Set<'a> when Ordered<'a> =
        match s with
        | SetEmpty -> SetEmpty
        | SetNode (k, l, r, h, c) ->
            let d = compare x k
            if d < 0 then rebalance k (remove x l) r
            elif d > 0 then rebalance k l (remove x r)
            else
                match l, r with
                | SetEmpty, _ -> r
                | _, SetEmpty -> l
                | _, _ ->
                    match tryMin r with
                    | Some m -> rebalance m l (removeMinNode r)
                    | None -> l

    let rec fold (f : 's -> 'a -> 's) (st : 's) (s : Set<'a>) : 's =
        match s with
        | SetEmpty -> st
        | SetNode (k, l, r, h, c) -> fold f (f (fold f st l) k) r

    let rec foldBack (f : 'a -> 's -> 's) (s : Set<'a>) (st : 's) : 's =
        match s with
        | SetEmpty -> st
        | SetNode (k, l, r, h, c) -> foldBack f l (f k (foldBack f r st))

    let toList (s : Set<'a>) : 'a list = foldBack (fun k acc -> k :: acc) s []
    let iter (f : 'a -> unit) (s : Set<'a>) : unit = fold (fun acc k -> f k) () s
    let singleton (x : 'a) : Set<'a> = SetNode (x, SetEmpty, SetEmpty, 1, 1)
    let ofList (xs : 'a list) : Set<'a> when Ordered<'a> =
        List.fold (fun acc x -> add x acc) SetEmpty xs
    let ofArray (xs : 'a[]) : Set<'a> when Ordered<'a> =
        Array.fold (fun acc x -> add x acc) SetEmpty xs
    let ofSeq (xs : seq<'a>) : Set<'a> when Ordered<'a> = ofList (Seq.toList xs)
    let toArray (s : Set<'a>) : 'a[] = Array.ofList (toList s)
    let toSeq (s : Set<'a>) : seq<'a> = List.toSeq (toList s)
    let exists (p : 'a -> bool) (s : Set<'a>) : bool =
        fold (fun acc k -> acc || p k) false s
    let forall (p : 'a -> bool) (s : Set<'a>) : bool =
        fold (fun acc k -> acc && p k) true s
    let filter (p : 'a -> bool) (s : Set<'a>) : Set<'a> when Ordered<'a> =
        fold (fun acc k -> if p k then add k acc else acc) SetEmpty s
    let map (f : 'a -> 'b) (s : Set<'a>) : Set<'b> when Ordered<'b> =
        fold (fun acc k -> add (f k) acc) SetEmpty s
    let choose (f : 'a -> 'b option) (s : Set<'a>) : Set<'b> when Ordered<'b> =
        fold (fun acc k -> match f k with Some b -> add b acc | None -> acc) SetEmpty s
    let minElement (s : Set<'a>) : 'a =
        match tryMin s with
        | Some k -> k
        | None -> failwith "The input set was empty"
    let maxElement (s : Set<'a>) : 'a =
        match tryMax s with
        | Some k -> k
        | None -> failwith "The input set was empty"
    let removeMin (s : Set<'a>) : Set<'a> when Ordered<'a> = removeMinNode s
    let removeMax (s : Set<'a>) : Set<'a> when Ordered<'a> =
        match tryMax s with
        | Some k -> remove k s
        | None -> s
    let tryRemove (x : 'a) (s : Set<'a>) : Set<'a> option when Ordered<'a> =
        if contains x s then Some (remove x s) else None
    let tryItem (i : int) (s : Set<'a>) : 'a option = List.tryItem i (toList s)
    let union (a : Set<'a>) (b : Set<'a>) : Set<'a> when Ordered<'a> =
        // fold the SMALLER into the larger
        if count a < count b then fold (fun acc k -> add k acc) b a
        else fold (fun acc k -> add k acc) a b
    let unionMany (ss : Set<'a> list) : Set<'a> when Ordered<'a> =
        List.fold (fun acc s -> union acc s) SetEmpty ss
    let intersect (a : Set<'a>) (b : Set<'a>) : Set<'a> when Ordered<'a> =
        fold (fun acc k -> if contains k b then add k acc else acc) SetEmpty a
    let intersectMany (ss : Set<'a> list) : Set<'a> when Ordered<'a> =
        match ss with
        | [] -> failwith "The input sequence was empty"
        | h :: t -> List.fold (fun acc s -> intersect acc s) h t
    let difference (a : Set<'a>) (b : Set<'a>) : Set<'a> when Ordered<'a> =
        fold (fun acc k -> if contains k b then acc else add k acc) SetEmpty a
    let partition (p : 'a -> bool) (s : Set<'a>) : Set<'a> * Set<'a> when Ordered<'a> =
        filter p s, filter (fun k -> not (p k)) s
    let isSubset (a : Set<'a>) (b : Set<'a>) : bool when Ordered<'a> =
        forall (fun k -> contains k b) a
    let isSuperset (a : Set<'a>) (b : Set<'a>) : bool when Ordered<'a> = isSubset b a
    let isProperSubset (a : Set<'a>) (b : Set<'a>) : bool when Ordered<'a> =
        isSubset a b && count a < count b
    let isProperSuperset (a : Set<'a>) (b : Set<'a>) : bool when Ordered<'a> =
        isSubset b a && count a > count b
    /// everything strictly below / above an element, and whether it is present
    let split (x : 'a) (s : Set<'a>) : Set<'a> * bool * Set<'a> when Ordered<'a> =
        let mutable lo = SetEmpty
        let mutable hi = SetEmpty
        for k in toList s do
            if k < x then lo <- add k lo
            elif k > x then hi <- add k hi
        lo, contains x s, hi
    let withMin (x : 'a) (s : Set<'a>) : Set<'a> when Ordered<'a> = filter (fun k -> k >= x) s
    let withMax (x : 'a) (s : Set<'a>) : Set<'a> when Ordered<'a> = filter (fun k -> k <= x) s
    let range (lo : 'a) (hi : 'a) (s : Set<'a>) : Set<'a> when Ordered<'a> =
        filter (fun k -> k >= lo && k <= hi) s
    /// Set deltas are stated in SETS, not in a keyed map: Set is declared
    /// before Map here, and (added, removed) is the natural shape for a
    /// collection with no values. HashSet's delta IS keyed, because HashSet
    /// is defined over HashMap (see HashSet.computeDelta).
    let computeDelta (a : Set<'a>) (b : Set<'a>) : Set<'a> * Set<'a> when Ordered<'a> =
        difference b a, difference a b
    /// apply (added, removed); returns the new state and what took effect
    let applyDelta (s : Set<'a>) (added : Set<'a>) (removed : Set<'a>) : Set<'a> * Set<'a> * Set<'a> when Ordered<'a> =
        let effAdded = difference added s
        let effRemoved = intersect removed s
        let mutable state = s
        for k in toList effAdded do
            state <- add k state
        for k in toList effRemoved do
            state <- remove k state
        state, effAdded, effRemoved
    let neighbours (x : 'a) (s : Set<'a>) : 'a option * bool * 'a option when Ordered<'a> =
        let mutable below = None
        let mutable above = None
        for k in toList s do
            if k < x then below <- Some k
            elif k > x && (match above with None -> true | Some _ -> false) then above <- Some k
        below, contains x s, above

type Map<'k, 'v> =
    | MapEmpty
    | MapNode of 'k * 'v * Map<'k, 'v> * Map<'k, 'v> * int * int

    /// the entries in key order — the CANONICAL form of a map, independent of
    /// whatever rotations the insertion order happened to produce
    member x.Pairs () =
        match x with
        | MapEmpty -> []
        | MapNode (k, v, l, r, _, _) -> l.Pairs () @ ((k, v) :: r.Pairs ())

    /// Content equality. Derived equality would compare the TREE, so the same
    /// entries added in a different order could compare unequal; F# compares
    /// content, and so must this.
    member x.Equals (o : Map<'k, 'v>) = x.Pairs () = o.Pairs ()

    /// must agree with Equals, or a map used as a hash key goes missing
    member x.GetHashCode () = hash (x.Pairs ())

module Map =
    let empty = MapEmpty

    let height (t : Map<'k, 'v>) : int =
        match t with
        | MapEmpty -> 0
        | MapNode (k, v, l, r, h, c) -> h

    let count (t : Map<'k, 'v>) : int =
        match t with
        | MapEmpty -> 0
        | MapNode (k, v, l, r, h, c) -> c

    let isEmpty (t : Map<'k, 'v>) : bool =
        match t with
        | MapEmpty -> true
        | MapNode (k, v, l, r, h, c) -> false

    let private mk (k : 'k) (v : 'v) (l : Map<'k, 'v>) (r : Map<'k, 'v>) : Map<'k, 'v> =
        let hl = height l
        let hr = height r
        let h = (if hl > hr then hl else hr) + 1
        MapNode (k, v, l, r, h, count l + count r + 1)

    let private rebalance (k : 'k) (v : 'v) (l : Map<'k, 'v>) (r : Map<'k, 'v>) : Map<'k, 'v> =
        let hl = height l
        let hr = height r
        if hr > hl + 2 then
            match r with
            | MapNode (rk, rv, rl, rr, rh, rc) ->
                if height rl > height rr then
                    match rl with
                    | MapNode (rlk, rlv, rll, rlr, rlh, rlc) ->
                        mk rlk rlv (mk k v l rll) (mk rk rv rlr rr)
                    | MapEmpty -> mk k v l r
                else mk rk rv (mk k v l rl) rr
            | MapEmpty -> mk k v l r
        elif hl > hr + 2 then
            match l with
            | MapNode (lk, lv, ll, lr, lh, lc) ->
                if height lr > height ll then
                    match lr with
                    | MapNode (lrk, lrv, lrl, lrr, lrh, lrc) ->
                        mk lrk lrv (mk lk lv ll lrl) (mk k v lrr r)
                    | MapEmpty -> mk k v l r
                else mk lk lv ll (mk k v lr r)
            | MapEmpty -> mk k v l r
        else mk k v l r

    let rec add (key : 'k) (value : 'v) (t : Map<'k, 'v>) : Map<'k, 'v> when Ordered<'k> =
        match t with
        | MapEmpty -> MapNode (key, value, MapEmpty, MapEmpty, 1, 1)
        | MapNode (k, v, l, r, h, c) ->
            let d = compare key k
            if d < 0 then rebalance k v (add key value l) r
            elif d > 0 then rebalance k v l (add key value r)
            else MapNode (key, value, l, r, h, c)

    let rec tryFind (key : 'k) (t : Map<'k, 'v>) : 'v option when Ordered<'k> =
        match t with
        | MapEmpty -> None
        | MapNode (k, v, l, r, h, c) ->
            let d = compare key k
            if d < 0 then tryFind key l
            elif d > 0 then tryFind key r
            else Some v

    let containsKey (key : 'k) (t : Map<'k, 'v>) : bool when Ordered<'k> =
        match tryFind key t with
        | Some v -> true
        | None -> false

    let find (key : 'k) (t : Map<'k, 'v>) : 'v when Ordered<'k> =
        match tryFind key t with
        | Some v -> v
        | None -> raise (KeyNotFoundException "the key was not present in the map")

    let findOr (dflt : 'v) (key : 'k) (t : Map<'k, 'v>) : 'v when Ordered<'k> =
        match tryFind key t with
        | Some v -> v
        | None -> dflt

    let rec private tryMin (t : Map<'k, 'v>) : ('k * 'v) option =
        match t with
        | MapEmpty -> None
        | MapNode (k, v, l, r, h, c) ->
            match l with
            | MapEmpty -> Some (k, v)
            | MapNode (a, b, cc, d, e, f) -> tryMin l

    let rec private removeMin (t : Map<'k, 'v>) : Map<'k, 'v> =
        match t with
        | MapEmpty -> MapEmpty
        | MapNode (k, v, l, r, h, c) ->
            match l with
            | MapEmpty -> r
            | MapNode (a, b, cc, d, e, f) -> rebalance k v (removeMin l) r

    let rec remove (key : 'k) (t : Map<'k, 'v>) : Map<'k, 'v> when Ordered<'k> =
        match t with
        | MapEmpty -> MapEmpty
        | MapNode (k, v, l, r, h, c) ->
            let d = compare key k
            if d < 0 then rebalance k v (remove key l) r
            elif d > 0 then rebalance k v l (remove key r)
            else
                match l, r with
                | MapEmpty, _ -> r
                | _, MapEmpty -> l
                | _, _ ->
                    match tryMin r with
                    | Some (sk, sv) -> rebalance sk sv l (removeMin r)
                    | None -> l

    let rec fold (f : 's -> 'k -> 'v -> 's) (s : 's) (t : Map<'k, 'v>) : 's =
        match t with
        | MapEmpty -> s
        | MapNode (k, v, l, r, h, c) -> fold f (f (fold f s l) k v) r

    let rec foldBack (f : 'k -> 'v -> 's -> 's) (t : Map<'k, 'v>) (s : 's) : 's =
        match t with
        | MapEmpty -> s
        | MapNode (k, v, l, r, h, c) -> foldBack f l (f k v (foldBack f r s))

    let iter (f : 'k -> 'v -> unit) (t : Map<'k, 'v>) : unit =
        fold (fun s k v -> f k v) () t

    let toList (t : Map<'k, 'v>) : ('k * 'v) list = foldBack (fun k v acc -> (k, v) :: acc) t []
    let toSeq (t : Map<'k, 'v>) : ('k * 'v) seq = List.toSeq (toList t)
    let keys (t : Map<'k, 'v>) : 'k list = foldBack (fun k v acc -> k :: acc) t []
    /// O(1) key VIEW: the same tree with its values left unread. Sound
    /// because every value shares one runtime representation and no value is
    /// ever read through it.
    let keySetView (t : Map<'k, 'v>) : Map<'k, int> = unbox (box t)
    /// the keys as a real Set. O(n): Set drops the value slot, so its nodes
    /// are a different shape and the tree has to be rebuilt — the O(1) view
    /// above is the one that shares structure.
    let keySet (t : Map<'k, 'v>) : Set<'k> when Ordered<'k> =
        foldBack (fun k v acc -> Set.add k acc) t SetEmpty
    let values (t : Map<'k, 'v>) : 'v list = foldBack (fun k v acc -> v :: acc) t []

    let rec private ofListInto (acc : Map<'k, 'v>) (xs : ('k * 'v) list) : Map<'k, 'v> when Ordered<'k> =
        match xs with
        | (k, v) :: rest -> ofListInto (add k v acc) rest
        | [] -> acc
    let ofList (xs : ('k * 'v) list) : Map<'k, 'v> when Ordered<'k> = ofListInto MapEmpty xs
    let ofSeq (xs : ('k * 'v) seq) : Map<'k, 'v> when Ordered<'k> = ofListInto MapEmpty (List.ofSeq xs)
    let ofArray (xs : ('k * 'v)[]) : Map<'k, 'v> when Ordered<'k> = ofListInto MapEmpty (Array.toList xs)

    let change (key : 'k) (f : 'v option -> 'v option) (t : Map<'k, 'v>) : Map<'k, 'v> when Ordered<'k> =
        match f (tryFind key t) with
        | Some nv -> add key nv t
        | None -> remove key t

    let map (f : 'k -> 'v -> 'w) (t : Map<'k, 'v>) : Map<'k, 'w> when Ordered<'k> =
        fold (fun acc k v -> add k (f k v) acc) MapEmpty t

    let filter (p : 'k -> 'v -> bool) (t : Map<'k, 'v>) : Map<'k, 'v> when Ordered<'k> =
        fold (fun acc k v -> if p k v then add k v acc else acc) MapEmpty t

    let exists (p : 'k -> 'v -> bool) (t : Map<'k, 'v>) : bool =
        fold (fun acc k v -> if acc then true else p k v) false t

    let forall (p : 'k -> 'v -> bool) (t : Map<'k, 'v>) : bool =
        fold (fun acc k v -> if acc then p k v else false) true t
    let tryFindKey (p : 'k -> 'v -> bool) (m : Map<'k, 'v>) : 'k option =
        let mutable found = None
        for k, v in toList m do
            match found with
            | None -> if p k v then found <- Some k
            | Some _ -> ()
        found
    let findKey (p : 'k -> 'v -> bool) (m : Map<'k, 'v>) : 'k =
        match tryFindKey p m with
        | Some k -> k
        | None -> failwith "An index satisfying the predicate was not found in the collection."
    let tryPick (f : 'k -> 'v -> 'r option) (m : Map<'k, 'v>) : 'r option =
        let mutable found = None
        for k, v in toList m do
            match found with
            | None -> found <- f k v
            | Some _ -> ()
        found
    let pick (f : 'k -> 'v -> 'r option) (m : Map<'k, 'v>) : 'r =
        match tryPick f m with
        | Some r -> r
        | None -> failwith "An index satisfying the predicate was not found in the collection."
    let partition (p : 'k -> 'v -> bool) (m : Map<'k, 'v>) : Map<'k, 'v> * Map<'k, 'v> =
        filter p m, filter (fun k v -> not (p k v)) m
    let toArray (m : Map<'k, 'v>) : ('k * 'v)[] = Array.ofList (toList m)
    /// F# 8's Map.minKeyValue / maxKeyValue — the entries are kept ordered,
    /// so these are the ends of the list
    let minKeyValue (m : Map<'k, 'v>) : 'k * 'v =
        match toList m with
        | [] -> failwith "The input map was empty"
        | h :: _ -> h
    let maxKeyValue (m : Map<'k, 'v>) : 'k * 'v =
        match List.rev (toList m) with
        | [] -> failwith "The input map was empty"
        | h :: _ -> h

    // ---- MapExt: the combinator surface, tree-structural ------------------
    /// the smallest binding, or None
    let minBinding (t : Map<'k, 'v>) : ('k * 'v) option = tryMin t
    /// the largest binding, or None
    let maxBinding (t : Map<'k, 'v>) : ('k * 'v) option = tryMax t
    let single (k : 'k) (v : 'v) : Map<'k, 'v> = MapNode (k, v, MapEmpty, MapEmpty, 1, 1)
    let tryItem (i : int) (t : Map<'k, 'v>) : ('k * 'v) option = List.tryItem i (toList t)
    /// remove the smallest binding; the map unchanged when empty
    let removeMinBinding (t : Map<'k, 'v>) : Map<'k, 'v> when Ordered<'k> =
        match tryMin t with
        | Some (k, _) -> remove k t
        | None -> t
    let removeMaxBinding (t : Map<'k, 'v>) : Map<'k, 'v> when Ordered<'k> =
        match tryMax t with
        | Some (k, _) -> remove k t
        | None -> t
    /// Some (removed value, rest) when the key was present
    let tryRemove (k : 'k) (t : Map<'k, 'v>) : ('v * Map<'k, 'v>) option when Ordered<'k> =
        match tryFind k t with
        | Some v -> Some (v, remove k t)
        | None -> None
    /// rewrite one key: the function sees its current binding and returns the
    /// new one (None removes)
    let alter (k : 'k) (f : 'v option -> 'v option) (t : Map<'k, 'v>) : Map<'k, 'v> when Ordered<'k> =
        match f (tryFind k t) with
        | Some v -> add k v t
        | None -> remove k t
    /// map one key's value, inserting `dflt` first when it is absent
    let update (k : 'k) (f : 'v -> 'v) (dflt : 'v) (t : Map<'k, 'v>) : Map<'k, 'v> when Ordered<'k> =
        match tryFind k t with
        | Some v -> add k (f v) t
        | None -> add k dflt t
    let mapValues (f : 'v -> 'w) (t : Map<'k, 'v>) : Map<'k, 'w> =
        map (fun k v -> f v) t
    let choose (f : 'k -> 'v -> 'w option) (t : Map<'k, 'v>) : Map<'k, 'w> when Ordered<'k> =
        fold (fun acc k v ->
                match f k v with
                | Some w -> add k w acc
                | None -> acc) MapEmpty t
    let unionWith (resolve : 'k -> 'v -> 'v -> 'v) (a : Map<'k, 'v>) (b : Map<'k, 'v>) : Map<'k, 'v> when Ordered<'k> =
        // b wins by default, so fold a INTO b and resolve on collision
        fold (fun acc k v ->
                match tryFind k acc with
                | Some other -> add k (resolve k v other) acc
                | None -> add k v acc) b a
    let union (a : Map<'k, 'v>) (b : Map<'k, 'v>) : Map<'k, 'v> when Ordered<'k> =
        unionWith (fun k x y -> y) a b
    let unionMany (ts : Map<'k, 'v> list) : Map<'k, 'v> when Ordered<'k> =
        List.fold (fun acc t -> union acc t) MapEmpty ts
    let intersectWith (resolve : 'k -> 'v -> 'w -> 'x) (a : Map<'k, 'v>) (b : Map<'k, 'w>) : Map<'k, 'x> when Ordered<'k> =
        fold (fun acc k v ->
                match tryFind k b with
                | Some other -> add k (resolve k v other) acc
                | None -> acc) MapEmpty a
    let intersect (a : Map<'k, 'v>) (b : Map<'k, 'w>) : Map<'k, 'v * 'w> when Ordered<'k> =
        intersectWith (fun k x y -> (x, y)) a b
    let difference (a : Map<'k, 'v>) (b : Map<'k, 'w>) : Map<'k, 'v> when Ordered<'k> =
        fold (fun acc k v -> if containsKey k b then acc else add k v acc) MapEmpty a
    /// over the UNION of both key sets: each key is offered whatever the two
    /// maps hold for it, and None drops it from the result
    let choose2 (f : 'k -> 'v option -> 'w option -> 'x option) (a : Map<'k, 'v>) (b : Map<'k, 'w>) : Map<'k, 'x> when Ordered<'k> =
        let withA =
            fold (fun acc k v ->
                    match f k (Some v) (tryFind k b) with
                    | Some x -> add k x acc
                    | None -> acc) MapEmpty a
        fold (fun acc k w ->
                if containsKey k a then acc
                else
                    match f k None (Some w) with
                    | Some x -> add k x acc
                    | None -> acc) withA b
    let map2 (f : 'k -> 'v option -> 'w option -> 'x) (a : Map<'k, 'v>) (b : Map<'k, 'w>) : Map<'k, 'x> when Ordered<'k> =
        choose2 (fun k x y -> Some (f k x y)) a b
    /// the delta that carries `a` to `b`: SetOp for added or changed keys,
    /// RemoveOp for the ones only `a` had
    let computeDelta (a : Map<'k, 'v>) (b : Map<'k, 'v>) : Map<'k, ElementOperation<'v>> when Ordered<'k> =
        choose2 (fun k x y ->
                    match x, y with
                    | Some ov, Some nv -> if ov = nv then None else Some (SetOp nv)
                    | None, Some nv -> Some (SetOp nv)
                    | Some _, None -> Some RemoveOp
                    | None, None -> None) a b
    /// apply a delta, returning the new state AND the delta that actually
    /// took effect (a Remove of an absent key changes nothing)
    let applyDelta (t : Map<'k, 'v>) (delta : Map<'k, ElementOperation<'v>>) : Map<'k, 'v> * Map<'k, ElementOperation<'v>> when Ordered<'k> =
        let mutable state = t
        let mutable eff = MapEmpty
        for k, op in toList delta do
            match op with
            | SetOp v ->
                match tryFind k state with
                | Some old when old = v -> ()
                | _ ->
                    state <- add k v state
                    eff <- add k (SetOp v) eff
            | RemoveOp ->
                if containsKey k state then
                    state <- remove k state
                    eff <- add k RemoveOp eff
        state, eff
    /// the bindings on either side of a key, and the key's own binding
    let neighbours (k : 'k) (t : Map<'k, 'v>) : ('k * 'v) option * ('k * 'v) option * ('k * 'v) option when Ordered<'k> =
        let mutable below = None
        let mutable above = None
        for kk, vv in toList t do
            if kk < k then below <- Some (kk, vv)
            elif kk > k && (match above with None -> true | Some _ -> false) then above <- Some (kk, vv)
        below, (match tryFind k t with Some v -> Some (k, v) | None -> None), above
    /// everything strictly below / above a key, and the key's own binding
    let split (k : 'k) (t : Map<'k, 'v>) : Map<'k, 'v> * 'v option * Map<'k, 'v> when Ordered<'k> =
        let mutable lo = MapEmpty
        let mutable hi = MapEmpty
        for kk, vv in toList t do
            if kk < k then lo <- add kk vv lo
            elif kk > k then hi <- add kk vv hi
        lo, tryFind k t, hi
    let withMin (k : 'k) (t : Map<'k, 'v>) : Map<'k, 'v> when Ordered<'k> =
        filter (fun kk vv -> kk >= k) t
    let withMax (k : 'k) (t : Map<'k, 'v>) : Map<'k, 'v> when Ordered<'k> =
        filter (fun kk vv -> kk <= k) t
    let range (lo : 'k) (hi : 'k) (t : Map<'k, 'v>) : Map<'k, 'v> when Ordered<'k> =
        filter (fun kk vv -> kk >= lo && kk <= hi) t

/// HashMap: the patricia-trie port (big-endian Okasaki-Gill over hashes with
/// collision chains and cached counts). The types live at the top level so
/// HashSet can share them.
// ---------------------------------------------------------------------------
// HashMap / HashSet
//
// The representation is the one the original (FSharp.Data.Adaptive) uses: a
// CLASS HIERARCHY over a big-endian patricia trie on the key hash, not a
// union.  Every node stores its own Count, and TryFind / AddWith / RemoveKey /
// FoldWith are abstract members, so walking the trie dispatches virtually
// instead of testing a tag.
//
//   HashNode          abstract base, carries Count
//    +- HashEmpty      no entries
//    +- HashLeaf       exactly one entry (the no-collision leaf)
//    +- HashCollision  one entry plus a chain of further entries with the
//                      SAME hash (`rest` is a HashLeaf or HashCollision)
//    +- HashInner      a trie branch: prefix, mask, two non-empty children
//
// The bit twiddling lives in top-level functions because the node members
// need it and a type only sees what precedes it.
// ---------------------------------------------------------------------------

let hmMaskHash (h : int) = h &&& 1073741823

let hmHighestBitMask (x0 : int) =
    let mutable x = x0
    x <- x ||| (x >>> 1)
    x <- x ||| (x >>> 2)
    x <- x ||| (x >>> 4)
    x <- x ||| (x >>> 8)
    x <- x ||| (x >>> 16)
    x ^^^ (x >>> 1)

let hmGetPrefix (k : int) (m : int) = k &&& ~~~((m <<< 1) - 1)
let hmZeroBit (k : int) (m : int) = if (k &&& m) <> 0 then 1 else 0

/// 0 = go left, 1 = go right, 2 = the hash does not live under this prefix
let hmMatchPrefixAndGetBit (h : int) (prefix : int) (m : int) =
    if hmGetPrefix h m = prefix then hmZeroBit h m else 2

[<AbstractClass>]
type HashNode<'k, 'v>(count : int) =
    /// entries in this subtree, O(1) — for callers OUTSIDE the hierarchy
    member x.Count = count

    /// Inside the hierarchy the count has to go through a METHOD: a property
    /// read on a base-typed value does not resolve within the declaring
    /// recursive group (it falls back to a field lookup under the member's
    /// own name). Method calls resolve fine, so every internal use is one.
    abstract member CountOf : unit -> int
    abstract member TryFind : int -> 'k -> Option<'v>
    abstract member AddWith : int -> 'k -> 'v -> HashNode<'k, 'v>
    abstract member RemoveKey : int -> 'k -> HashNode<'k, 'v>
    abstract member FoldWith : ('s -> 'k -> 'v -> 's) -> 's -> 's

    /// Content equality: the same entries, whatever trie shape or collision
    /// order produced them. Without this `=` on a class is IDENTITY, so two
    /// maps with identical entries would compare unequal.
    member x.Equals (o : HashNode<'k, 'v>) =
        x.CountOf () = o.CountOf ()
        && x.FoldWith
            (fun acc k v ->
                acc
                && (match o.TryFind (hmMaskHash (hash k)) k with
                    | Some v2 -> v2 = v
                    | None -> false))
            true

    /// order-independent, so it agrees with Equals
    member x.GetHashCode () =
        x.FoldWith (fun acc k v -> acc + hash k * 31 + hash v) 0

    /// the branch holding this node (whose hash is p0) and `other` (at p1),
    /// which disagree somewhere above their common prefix
    member x.JoinWith (p0 : int) (p1 : int) (other : HashNode<'k, 'v>) =
        let mask = hmHighestBitMask (p0 ^^^ p1)
        let prefix = hmGetPrefix p0 mask
        let total = x.CountOf () + other.CountOf ()
        if hmZeroBit p0 mask = 0 then HashInner<'k, 'v>(prefix, mask, x, other, total) :> HashNode<'k, 'v>
        else HashInner<'k, 'v>(prefix, mask, other, x, total) :> HashNode<'k, 'v>

and HashEmpty<'k, 'v>() =
    inherit HashNode<'k, 'v>(0)
    override x.CountOf () = 0
    override x.TryFind (h : int) (key : 'k) = None
    override x.AddWith (h : int) (key : 'k) (value : 'v) =
        HashLeaf<'k, 'v>(h, key, value) :> HashNode<'k, 'v>
    override x.RemoveKey (h : int) (key : 'k) = x :> HashNode<'k, 'v>
    override x.FoldWith (f : 's -> 'k -> 'v -> 's) (s : 's) = s

and HashLeaf<'k, 'v>(hash : int, key : 'k, value : 'v) =
    inherit HashNode<'k, 'v>(1)
    member x.Hash = hash
    member x.Key = key
    member x.Value = value

    override x.CountOf () = 1

    override x.TryFind (h : int) (k : 'k) =
        if h = hash && k = key then Some value else None

    override x.AddWith (h : int) (k : 'k) (v : 'v) =
        if h = hash then
            if k = key then HashLeaf<'k, 'v>(hash, k, v) :> HashNode<'k, 'v>
            else
                // same hash, different key: this leaf becomes a collision head
                HashCollision<'k, 'v>(hash, key, value, HashLeaf<'k, 'v>(hash, k, v) :> HashNode<'k, 'v>, 2) :> HashNode<'k, 'v>
        else
            (HashLeaf<'k, 'v>(h, k, v) :> HashNode<'k, 'v>).JoinWith h hash (x :> HashNode<'k, 'v>)

    override x.RemoveKey (h : int) (k : 'k) =
        if h = hash && k = key then HashEmpty<'k, 'v>() :> HashNode<'k, 'v>
        else x :> HashNode<'k, 'v>

    override x.FoldWith (f : 's -> 'k -> 'v -> 's) (s : 's) = f s key value

and HashCollision<'k, 'v>(hash : int, key : 'k, value : 'v, rest : HashNode<'k, 'v>, cnt : int) =
    // `cnt` is 1 + rest's count: the base ctor argument cannot itself call a
    // member, so whoever builds the node passes the total in
    inherit HashNode<'k, 'v>(cnt)
    member x.Hash = hash
    member x.Key = key
    member x.Value = value
    member x.Rest = rest

    override x.CountOf () = cnt

    override x.TryFind (h : int) (k : 'k) =
        if h <> hash then None
        elif k = key then Some value
        else rest.TryFind h k

    override x.AddWith (h : int) (k : 'k) (v : 'v) =
        if h = hash then
            if k = key then HashCollision<'k, 'v>(hash, k, v, rest, cnt) :> HashNode<'k, 'v>
            else
                let r = rest.AddWith h k v
                HashCollision<'k, 'v>(hash, key, value, r, 1 + r.CountOf ()) :> HashNode<'k, 'v>
        else
            (HashLeaf<'k, 'v>(h, k, v) :> HashNode<'k, 'v>).JoinWith h hash (x :> HashNode<'k, 'v>)

    override x.RemoveKey (h : int) (k : 'k) =
        if h <> hash then x :> HashNode<'k, 'v>
        elif k = key then rest
        else
            let r = rest.RemoveKey h k
            let rc = r.CountOf ()
            // one entry left: collapse the chain back to a plain leaf
            if rc = 0 then HashLeaf<'k, 'v>(hash, key, value) :> HashNode<'k, 'v>
            else HashCollision<'k, 'v>(hash, key, value, r, 1 + rc) :> HashNode<'k, 'v>

    override x.FoldWith (f : 's -> 'k -> 'v -> 's) (s : 's) = rest.FoldWith f (f s key value)

and HashInner<'k, 'v>(prefix : int, mask : int, left : HashNode<'k, 'v>, right : HashNode<'k, 'v>, cnt : int) =
    inherit HashNode<'k, 'v>(cnt)
    member x.Prefix = prefix
    member x.Mask = mask
    member x.Left = left
    member x.Right = right

    override x.CountOf () = cnt

    override x.TryFind (h : int) (k : 'k) =
        let b = hmMatchPrefixAndGetBit h prefix mask
        if b = 0 then left.TryFind h k
        elif b = 1 then right.TryFind h k
        else None

    override x.AddWith (h : int) (k : 'k) (v : 'v) =
        let b = hmMatchPrefixAndGetBit h prefix mask
        if b = 0 then
            let l = left.AddWith h k v
            HashInner<'k, 'v>(prefix, mask, l, right, l.CountOf () + right.CountOf ()) :> HashNode<'k, 'v>
        elif b = 1 then
            let r = right.AddWith h k v
            HashInner<'k, 'v>(prefix, mask, left, r, left.CountOf () + r.CountOf ()) :> HashNode<'k, 'v>
        else
            (HashLeaf<'k, 'v>(h, k, v) :> HashNode<'k, 'v>).JoinWith h prefix (x :> HashNode<'k, 'v>)

    override x.RemoveKey (h : int) (k : 'k) =
        let b = hmMatchPrefixAndGetBit h prefix mask
        if b = 0 then
            let l = left.RemoveKey h k
            let lc = l.CountOf ()
            // a branch with an empty side is not a branch any more
            if lc = 0 then right
            else HashInner<'k, 'v>(prefix, mask, l, right, lc + right.CountOf ()) :> HashNode<'k, 'v>
        elif b = 1 then
            let r = right.RemoveKey h k
            let rc = r.CountOf ()
            if rc = 0 then left
            else HashInner<'k, 'v>(prefix, mask, left, r, left.CountOf () + rc) :> HashNode<'k, 'v>
        else x :> HashNode<'k, 'v>

    override x.FoldWith (f : 's -> 'k -> 'v -> 's) (s : 's) = right.FoldWith f (left.FoldWith f s)

/// the empty node; one per instantiation, it carries nothing
let hmEmpty () : HashNode<'k, 'v> = HashEmpty<'k, 'v>() :> HashNode<'k, 'v>

module HashMap =
    let maskHash (h : int) = h &&& 1073741823

    let empty : HashNode<'k, 'v> = hmEmpty ()
    let add (key : 'k) (value : 'v) (n : HashNode<'k, 'v>) = n.AddWith (hmMaskHash (hash key)) key value
    let tryFind (key : 'k) (n : HashNode<'k, 'v>) = n.TryFind (hmMaskHash (hash key)) key
    let remove (key : 'k) (n : HashNode<'k, 'v>) = n.RemoveKey (hmMaskHash (hash key)) key
    let count (n : HashNode<'k, 'v>) = n.CountOf ()
    let isEmpty (n : HashNode<'k, 'v>) = n.CountOf () = 0
    let fold (f : 's -> 'k -> 'v -> 's) (s : 's) (n : HashNode<'k, 'v>) = n.FoldWith f s

    let containsKey (key : 'k) (n : HashNode<'k, 'v>) =
        match tryFind key n with
        | Some v -> true
        | None -> false
    let findOr (d : 'v) (key : 'k) (n : HashNode<'k, 'v>) =
        match tryFind key n with
        | Some v -> v
        | None -> d
    let toList (n : HashNode<'k, 'v>) = fold (fun acc k v -> (k, v) :: acc) [] n
    let rec ofListInto (acc : HashNode<'k, 'v>) (xs : ('k * 'v) list) =
        match xs with
        | (k, v) :: t -> ofListInto (add k v acc) t
        | [] -> acc
    let ofList (items : ('k * 'v) list) = ofListInto (hmEmpty ()) items
    let keys (n : HashNode<'k, 'v>) = fold (fun acc k v -> k :: acc) [] n
    let values (n : HashNode<'k, 'v>) = fold (fun acc k v -> v :: acc) [] n
    let alter (key : 'k) (f : Option<'v> -> Option<'v>) (n : HashNode<'k, 'v>) =
        match f (tryFind key n) with
        | Some nv -> add key nv n
        | None -> remove key n
    let change (key : 'k) (f : Option<'v> -> Option<'v>) (n : HashNode<'k, 'v>) = alter key f n
    let update (key : 'k) (f : 'v -> 'v) (dflt : 'v) (n : HashNode<'k, 'v>) =
        match tryFind key n with
        | Some v -> add key (f v) n
        | None -> add key dflt n
    let map (f : 'k -> 'v -> 'w) (n : HashNode<'k, 'v>) =
        fold (fun acc k v -> add k (f k v) acc) (hmEmpty ()) n
    let mapValues (f : 'v -> 'w) (n : HashNode<'k, 'v>) = map (fun k v -> f v) n
    let filter (p : 'k -> 'v -> bool) (n : HashNode<'k, 'v>) =
        fold (fun acc k v -> if p k v then add k v acc else acc) (hmEmpty ()) n
    let choose (f : 'k -> 'v -> Option<'w>) (n : HashNode<'k, 'v>) =
        fold (fun acc k v ->
                match f k v with
                | Some w -> add k w acc
                | None -> acc) (hmEmpty ()) n
    let exists (p : 'k -> 'v -> bool) (n : HashNode<'k, 'v>) =
        fold (fun acc k v -> if acc then true else p k v) false n
    let forall (p : 'k -> 'v -> bool) (n : HashNode<'k, 'v>) =
        fold (fun acc k v -> if acc then p k v else false) true n
    let unionWith (resolve : 'k -> 'v -> 'v -> 'v) (a : HashNode<'k, 'v>) (b : HashNode<'k, 'v>) =
        fold (fun acc k v ->
                match tryFind k acc with
                | Some old -> add k (resolve k old v) acc
                | None -> add k v acc) a b
    let union (a : HashNode<'k, 'v>) (b : HashNode<'k, 'v>) = unionWith (fun k x y -> y) a b
    let intersectWith (resolve : 'k -> 'v -> 'v -> 'v) (a : HashNode<'k, 'v>) (b : HashNode<'k, 'v>) =
        fold (fun acc k v ->
                match tryFind k b with
                | Some other -> add k (resolve k v other) acc
                | None -> acc) (hmEmpty ()) a
    let intersect (a : HashNode<'k, 'v>) (b : HashNode<'k, 'v>) = intersectWith (fun k x y -> x) a b
    let difference (a : HashNode<'k, 'v>) (b : HashNode<'k, 'v>) =
        fold (fun acc k v -> if containsKey k b then acc else add k v acc) (hmEmpty ()) a
    let partition (p : 'k -> 'v -> bool) (n : HashNode<'k, 'v>) =
        fold (fun acc k v ->
                match acc with
                | (yes, no) -> if p k v then (add k v yes, no) else (yes, add k v no))
             ((hmEmpty ()), (hmEmpty ())) n
    let choose2 (f : 'k -> Option<'v> -> Option<'w> -> Option<'x>) (a : HashNode<'k, 'v>) (b : HashNode<'k, 'w>) =
        let withA =
            fold (fun acc k v ->
                    match f k (Some v) (tryFind k b) with
                    | Some x -> add k x acc
                    | None -> acc) (hmEmpty ()) a
        fold (fun acc k w ->
                if containsKey k a then acc
                else
                    match f k None (Some w) with
                    | Some x -> add k x acc
                    | None -> acc) withA b
    let map2 (f : 'k -> Option<'v> -> Option<'w> -> 'x) (a : HashNode<'k, 'v>) (b : HashNode<'k, 'w>) =
        choose2 (fun k x y -> Some (f k x y)) a b
    // ---- the rest of the surface -------------------------------------------
    let single (k : 'k) (v : 'v) : HashNode<'k, 'v> = add k v (hmEmpty ())
    let iter (f : 'k -> 'v -> unit) (n : HashNode<'k, 'v>) : unit =
        fold (fun acc k v -> f k v) () n
    let toArray (n : HashNode<'k, 'v>) : ('k * 'v)[] = Array.ofList (toList n)
    let ofArray (xs : ('k * 'v)[]) : HashNode<'k, 'v> = ofList (Array.toList xs)
    let toSeq (n : HashNode<'k, 'v>) : seq<'k * 'v> = List.toSeq (toList n)
    let ofSeq (xs : seq<'k * 'v>) : HashNode<'k, 'v> = ofList (Seq.toList xs)
    let find (k : 'k) (n : HashNode<'k, 'v>) : 'v =
        match tryFind k n with
        | Some v -> v
        | None -> failwith "The given key was not present in the collection."
    let tryRemove (k : 'k) (n : HashNode<'k, 'v>) : ('v * HashNode<'k, 'v>) option =
        match tryFind k n with
        | Some v -> Some (v, remove k n)
        | None -> None
    let unionMany (ns : HashNode<'k, 'v> list) : HashNode<'k, 'v> =
        List.fold (fun acc n -> union acc n) (hmEmpty ()) ns
    let tryPick (f : 'k -> 'v -> 'r option) (n : HashNode<'k, 'v>) : 'r option =
        fold (fun acc k v -> match acc with Some _ -> acc | None -> f k v) None n
    let pick (f : 'k -> 'v -> 'r option) (n : HashNode<'k, 'v>) : 'r =
        match tryPick f n with
        | Some r -> r
        | None -> failwith "An index satisfying the predicate was not found in the collection."
    /// O(1): the key set is THIS TRIE with its values left unread. Values
    /// share one runtime representation, so no node is rebuilt — contrast
    /// `keys`, which is O(n) because it materializes a list.
    let keySet (n : HashNode<'k, 'v>) : HashNode<'k, int> = unbox (box n)
    /// the delta carrying `a` to `b`
    let computeDelta (a : HashNode<'k, 'v>) (b : HashNode<'k, 'v>) : HashNode<'k, ElementOperation<'v>> =
        choose2 (fun k x y ->
                    match x, y with
                    | Some ov, Some nv -> if ov = nv then None else Some (SetOp nv)
                    | None, Some nv -> Some (SetOp nv)
                    | Some _, None -> Some RemoveOp
                    | None, None -> None) a b
    /// apply a delta; returns the new state and the delta that took effect
    let applyDelta (n : HashNode<'k, 'v>) (delta : HashNode<'k, ElementOperation<'v>>) : HashNode<'k, 'v> * HashNode<'k, ElementOperation<'v>> =
        let mutable state = n
        let mutable eff = (hmEmpty ())
        for k, op in toList delta do
            match op with
            | SetOp v ->
                match tryFind k state with
                | Some old when old = v -> ()
                | _ ->
                    state <- add k v state
                    eff <- add k (SetOp v) eff
            | RemoveOp ->
                if containsKey k state then
                    state <- remove k state
                    eff <- add k RemoveOp eff
        state, eff

/// HashSet IS a HashMap whose values are never read — the same trie, so
/// HashMap.keySet is a reinterpret rather than a rebuild (see keySet).
module HashSet =
    let empty : HashNode<'k, int> = (hmEmpty ())
    let isEmpty (s : HashNode<'k, int>) : bool = HashMap.isEmpty s
    let count (s : HashNode<'k, int>) : int = HashMap.count s
    let add (k : 'k) (s : HashNode<'k, int>) : HashNode<'k, int> = HashMap.add k 0 s
    let remove (k : 'k) (s : HashNode<'k, int>) : HashNode<'k, int> = HashMap.remove k s
    let contains (k : 'k) (s : HashNode<'k, int>) : bool = HashMap.containsKey k s
    let singleton (k : 'k) : HashNode<'k, int> = add k (hmEmpty ())
    let toList (s : HashNode<'k, int>) : 'k list = HashMap.keys s
    let ofList (xs : 'k list) : HashNode<'k, int> =
        List.fold (fun acc x -> add x acc) (hmEmpty ()) xs
    let toArray (s : HashNode<'k, int>) : 'k[] = Array.ofList (toList s)
    let ofArray (xs : 'k[]) : HashNode<'k, int> = ofList (Array.toList xs)
    let toSeq (s : HashNode<'k, int>) : seq<'k> = List.toSeq (toList s)
    let ofSeq (xs : seq<'k>) : HashNode<'k, int> = ofList (Seq.toList xs)
    let fold (f : 's -> 'k -> 's) (st : 's) (s : HashNode<'k, int>) : 's =
        HashMap.fold (fun acc k v -> f acc k) st s
    let iter (f : 'k -> unit) (s : HashNode<'k, int>) : unit =
        HashMap.fold (fun acc k v -> f k) () s
    let exists (p : 'k -> bool) (s : HashNode<'k, int>) : bool =
        HashMap.exists (fun k v -> p k) s
    let forall (p : 'k -> bool) (s : HashNode<'k, int>) : bool =
        HashMap.forall (fun k v -> p k) s
    let filter (p : 'k -> bool) (s : HashNode<'k, int>) : HashNode<'k, int> =
        HashMap.filter (fun k v -> p k) s
    let union (a : HashNode<'k, int>) (b : HashNode<'k, int>) : HashNode<'k, int> =
        HashMap.union a b
    let unionMany (ss : HashNode<'k, int> list) : HashNode<'k, int> =
        List.fold (fun acc s -> union acc s) (hmEmpty ()) ss
    let intersect (a : HashNode<'k, int>) (b : HashNode<'k, int>) : HashNode<'k, int> =
        HashMap.intersect a b
    let difference (a : HashNode<'k, int>) (b : HashNode<'k, int>) : HashNode<'k, int> =
        HashMap.difference a b
    let isSubset (a : HashNode<'k, int>) (b : HashNode<'k, int>) : bool =
        forall (fun k -> contains k b) a
    let isSuperset (a : HashNode<'k, int>) (b : HashNode<'k, int>) : bool = isSubset b a
    let isProperSubset (a : HashNode<'k, int>) (b : HashNode<'k, int>) : bool =
        isSubset a b && count a < count b
    let isProperSuperset (a : HashNode<'k, int>) (b : HashNode<'k, int>) : bool =
        isSubset b a && count a > count b
    let map (f : 'k -> 'j) (s : HashNode<'k, int>) : HashNode<'j, int> =
        fold (fun acc k -> add (f k) acc) (hmEmpty ()) s
    let choose (f : 'k -> 'j option) (s : HashNode<'k, int>) : HashNode<'j, int> =
        fold (fun acc k -> match f k with Some j -> add j acc | None -> acc) (hmEmpty ()) s
    let partition (p : 'k -> bool) (s : HashNode<'k, int>) : HashNode<'k, int> * HashNode<'k, int> =
        filter p s, filter (fun k -> not (p k)) s
    /// set deltas: SetOp means "present", RemoveOp means "gone"
    let computeDelta (a : HashNode<'k, int>) (b : HashNode<'k, int>) : HashNode<'k, ElementOperation<int>> =
        HashMap.choose2 (fun k x y ->
                            match x, y with
                            | Some _, Some _ -> None
                            | None, Some _ -> Some (SetOp 0)
                            | Some _, None -> Some RemoveOp
                            | None, None -> None) a b
    let applyDelta (s : HashNode<'k, int>) (delta : HashNode<'k, ElementOperation<int>>) : HashNode<'k, int> * HashNode<'k, ElementOperation<int>> =
        let mutable state = s
        let mutable eff = (hmEmpty ())
        for k, op in HashMap.toList delta do
            match op with
            | SetOp v ->
                if not (contains k state) then
                    state <- add k state
                    eff <- HashMap.add k (SetOp 0) eff
            | RemoveOp ->
                if contains k state then
                    state <- remove k state
                    eff <- HashMap.add k RemoveOp eff
        state, eff

// ---------------------------------------------------------------------------
// Property testing: generators, shrinking, and a runner
//
// Generators are VALUES (`Gen.list Gen.int`), not typeclass instances. That is
// not only a style choice: monomorphization shares ONE canonical body across
// all reference instantiations, so a class constraint discharged inside such a
// body has no head type left to resolve against — `Arb<list<'a>>` cannot be
// found from a canonical caller. A generator passed as a value sidesteps
// resolution entirely and composes the same way.
//
// Each generator carries three things: how to draw a value, how to shrink one
// (so a failure reports the SMALLEST case, not the first), and how to print it.
// ---------------------------------------------------------------------------

/// xorshift32: tiny, deterministic, and good enough to find bugs. The state is
/// explicit so a failing run replays exactly from its seed.
///
/// Named PropRng rather than Rng because a prelude type squats on the name for
/// every program: `type Rng` is exactly what a user writes for their own
/// generator, and a user type shadowing a prelude one does not resolve cleanly
/// today. The helpers that go with it live inside `Gen` for the same reason.
type PropRng = { mutable State : int }

type Gen<'a> =
    { /// draw one value
      Draw : PropRng -> 'a
      /// strictly smaller candidates, most-shrunk first; [] when atomic
      Smaller : 'a -> list<'a>
      /// render a counterexample
      Render : 'a -> string }

/// What `<@ ... @>` evaluates to: the quoted code AS A TREE. The body was
/// resolved and type checked where it was written, and this is that same code
/// in a form a program can take apart — no source text anywhere, so nothing has
/// to be parsed a second time and composition cannot lose to precedence or
/// formatting. A quotation containing something outside this subset is a
/// compile-time error, never a silent fallback.
/// A TYPE inside quoted code — what `: %t` splices.
type QTy =
    | QTyName of string
    | QTyApp of string * QTy list

/// A pattern inside quoted code.
type QPat =
    | QWild
    | QVar of string
    | QInt of int
    /// a union case and the patterns it binds
    | QCase of string * QPat list

type CodeTree =
    | CInt of int
    | CStr of string
    | CBool of bool
    /// a name as written
    | CName of string
    /// `f a b`
    | CApp of CodeTree * CodeTree list
    /// `a + b`, operator first
    | CBin of string * CodeTree * CodeTree
    /// `let n = value` followed by the rest
    | CLet of string * CodeTree * CodeTree
    | CIf of CodeTree * CodeTree * CodeTree
    | CTuple of CodeTree list
    | CList of CodeTree list
    /// `fun a b -> body`
    | CLam of string list * CodeTree
    /// `x.Field`
    | CField of CodeTree * string
    /// `match scrutinee with | pat -> body | ...`
    | CMatch of CodeTree * (QPat * CodeTree) list
    /// a DECLARATION: `let name (p : ty) ... : ret = body`. Quoting one gives
    /// a plugin the thing it actually wants to emit; a parameter or return type
    /// that was not written is QTyName "".
    | CDLet of string * (string * QTy) list * QTy * CodeTree
    /// `member self.Name (p : ty) ... : ret = body`
    | CDMember of string * string * (string * QTy) list * QTy * CodeTree
    /// `type Name = { field : ty; ... }`
    | CDRecord of string * (string * QTy) list

/// `Code<'t>` is quoted code KNOWN TO PRODUCE a 't — that is what lets a splice
/// type check against the hole it fills. `Raw` is the tree underneath, for
/// taking the code apart.
type Code<'t> = { Raw : CodeTree }

module Code =
    let private pad (n : int) = String.replicate n " "

    let rec renderTy (t : QTy) : string =
        match t with
        | QTyName n -> n
        | QTyApp (n, args) -> n + "<" + String.concat ", " (List.map renderTy args) + ">"

    let rec renderPat (p : QPat) : string =
        match p with
        | QWild -> "_"
        | QVar v -> v
        | QInt v -> string v
        | QCase (n, []) -> n
        | QCase (n, [ one ]) -> n + " " + renderPat one
        // several payload fields are ONE tuple, and match as one
        | QCase (n, ps) -> n + " (" + String.concat ", " (List.map renderPat ps) + ")"

    /// Render a tree back to SOURCE. This is the boundary where code becomes
    /// text — a generator writing a file, a plugin printing what it produced —
    /// and nowhere else: composition happens on trees.
    let rec renderAt (ind : int) (c : CodeTree) : string =
        match c with
        | CInt v -> string v
        | CStr v -> "\"" + v + "\""
        | CBool b -> if b then "true" else "false"
        | CName n -> n
        | CApp (f, args) ->
            "(" + renderAt ind f + " " + String.concat " " (List.map (fun a -> renderAt ind a) args) + ")"
        | CBin (op, l, r) -> "(" + renderAt ind l + " " + op + " " + renderAt ind r + ")"
        | CIf (c2, t, e) -> "(if " + renderAt ind c2 + " then " + renderAt ind t + " else " + renderAt ind e + ")"
        | CTuple xs -> "(" + String.concat ", " (List.map (fun x -> renderAt ind x) xs) + ")"
        | CList xs -> "[ " + String.concat "; " (List.map (fun x -> renderAt ind x) xs) + " ]"
        | CLam (ps, b) -> "(fun " + String.concat " " ps + " -> " + renderAt ind b + ")"
        | CField (r, f) -> renderAt ind r + "." + f
        // a `let` sequence is statements: F++ has no `let ... in`
        | CLet (n, v, b) ->
            "\n" + pad (ind + 4) + "let " + n + " = " + renderAt (ind + 4) v
            + "\n" + pad (ind + 4) + renderAt (ind + 4) b
        | CMatch (sc, arms) ->
            let arm (p : QPat) (b : CodeTree) =
                "\n" + pad (ind + 4) + "| " + renderPat p + " -> " + renderAt (ind + 4) b
            "match " + renderAt ind sc + " with"
            + String.concat "" (List.map (fun (p, b) -> arm p b) arms)
        | CDMember (self, n, ps, ret, b) ->
            let ps2 =
                ps
                |> List.map (fun (pn, pt) ->
                    match pt with
                    | QTyName "" -> pn
                    | t -> "(" + pn + " : " + renderTy t + ")")
                |> String.concat " "
            let args = if List.isEmpty ps then " ()" else " " + ps2
            let retTxt = match ret with QTyName "" -> "" | t -> " : " + renderTy t
            "member " + self + "." + n + args + retTxt + " =\n" + pad (ind + 4) + renderAt (ind + 4) b
        | CDRecord (n, fields) ->
            "type " + n + " =\n" + pad (ind + 4) + "{ "
            + String.concat "; " (List.map (fun (fn, ft) -> fn + " : " + renderTy ft) fields)
            + " }"
        | CDLet (n, ps, ret, b) ->
            let ps2 =
                ps
                |> List.map (fun (pn, pt) ->
                    match pt with
                    | QTyName "" -> pn
                    | t -> "(" + pn + " : " + renderTy t + ")")
                |> String.concat " "
            let head = "let " + n + (if List.isEmpty ps then "" else " " + ps2)
            let retTxt = match ret with QTyName "" -> "" | t -> " : " + renderTy t
            head + retTxt + " =\n" + pad (ind + 4) + renderAt (ind + 4) b

    let render (c : CodeTree) : string = renderAt 0 c

    /// print a declaration as source — what an F++ generator emits
    let emit (c : CodeTree) : unit = print (render c)

/// The call stack, as the program itself can see it. A DEBUG build keeps a
/// shadow stack — wasm exposes none of its own — and these read it. In a plain
/// build the depth is 0 and every frame is 0, so code that reports a trace
/// still runs; it just has nothing to report.
/// how many frames are live right now (0 outside a debug build)
extern let stackDepth : unit -> int
/// the id of frame `i`, counting from 1 at the outermost
extern let stackFrame : int -> int

module Stack =
    let depth () : int = stackDepth ()

    /// the id of frame `i`, counting from 1 (the outermost). The id is the
    /// function's index, which the module's name section maps to a name — so a
    /// host, a source map, or the frame table beside it renders the name.
    let frame (i : int) : int = stackFrame i

    /// every live frame, outermost first
    let frames () : list<int> =
        let mutable acc = []
        let mutable i = depth ()
        while i >= 1 do
            acc <- frame i :: acc
            i <- i - 1
        acc

/// The conversions the generators need, under names `Gen` does not shadow.
/// Inside `module Gen`, `char`, `string` and `float` are the GENERATORS, and a
/// call to the conversion of the same name applies the generator record — which
/// traps at run time instead of failing to compile.
let genCharOf (i : int) : char = char i
let genStringOfChar (c : char) : string = string c
let genFloatOf (i : int) : float = float i
let genShowInt (x : int) : string = string x
let genShowFloat (x : float) : string = string x

module Gen =
    let rngCreate (seed : int) : PropRng =
        // zero is a fixed point of xorshift, so it can never be the state
        { State = if seed = 0 then 2463534242 else seed }

    let rngNext (r : PropRng) : int =
        let mutable x = r.State
        x <- x ^^^ (x <<< 13)
        x <- x ^^^ (x >>> 17)
        x <- x ^^^ (x <<< 5)
        r.State <- x
        x

    /// a non-negative draw below `n`
    let rngBelow (r : PropRng) (n : int) : int =
        if n <= 1 then 0
        else
            let v = rngNext r
            let p = if v < 0 then -(v + 1) else v
            p % n

    let rngRange (r : PropRng) (lo : int) (hi : int) : int =
        if hi <= lo then lo else lo + rngBelow r (hi - lo + 1)

    let rngBool (r : PropRng) : bool = rngBelow r 2 = 0

    let create (draw : PropRng -> 'a) (smaller : 'a -> list<'a>) (render : 'a -> string) : Gen<'a> =
        { Draw = draw; Smaller = smaller; Render = render }

    let constant (v : 'a) (render : 'a -> string) : Gen<'a> =
        { Draw = (fun r -> v); Smaller = (fun x -> []); Render = render }

    /// small values and boundaries find more bugs than uniform 32-bit noise
    let int : Gen<int> =
        { Draw =
            (fun r ->
                let k = rngBelow r 10
                if k = 0 then 0
                elif k = 1 then 1
                elif k = 2 then -1
                elif k = 3 then Int32.MaxValue
                elif k = 4 then Int32.MinValue
                elif k < 8 then rngRange r -20 20
                else rngNext r)
          Smaller =
            (fun x ->
                if x = 0 then []
                else
                    let half = x / 2
                    let toward = if half = 0 || half = x then [ 0 ] else [ 0; half ]
                    if x < 0 then toward @ [ -x ] else toward)
          Render = (fun x -> genShowInt x) }

    /// ints in a range: the generator to reach for when keys should COLLIDE
    let intRange (lo : int) (hi : int) : Gen<int> =
        { Draw = (fun r -> rngRange r lo hi)
          Smaller = (fun x -> if x = lo then [] else [ lo ])
          Render = (fun x -> genShowInt x) }

    let bool : Gen<bool> =
        { Draw = (fun r -> rngBool r)
          Smaller = (fun b -> if b then [ false ] else [])
          Render = (fun b -> if b then "true" else "false") }

    let char : Gen<char> =
        { Draw = (fun r -> genCharOf (rngRange r 97 122))
          Smaller = (fun c -> if c = 'a' then [] else [ 'a' ])
          Render = (fun c -> "'" + genStringOfChar c + "'") }

    let string : Gen<string> =
        { Draw =
            (fun r ->
                let n = rngBelow r 6
                let mutable s = ""
                for i in 1 .. n do
                    s <- s + genStringOfChar (genCharOf (rngRange r 97 122))
                s)
          Smaller =
            (fun s ->
                if s = "" then []
                elif s.Length = 1 then [ "" ]
                else [ ""; s.Substring (0, s.Length / 2) ])
          Render = (fun s -> "\"" + s + "\"") }

    let float : Gen<float> =
        { Draw =
            (fun r ->
                let k = rngBelow r 8
                if k = 0 then 0.0
                elif k = 1 then 1.0
                elif k = 2 then -1.0
                else genFloatOf (rngRange r -1000 1000) / 8.0)
          Smaller = (fun x -> if x = 0.0 then [] else [ 0.0 ])
          Render = (fun x -> genShowFloat x) }

    let option (g : Gen<'a>) : Gen<Option<'a>> =
        { Draw = (fun r -> if rngBelow r 4 = 0 then None else Some (g.Draw r))
          Smaller =
            (fun o ->
                match o with
                | None -> []
                | Some v -> None :: List.map (fun s -> Some s) (g.Smaller v))
          Render =
            (fun o ->
                match o with
                | None -> "None"
                | Some v -> "Some " + g.Render v) }

    let pair (ga : Gen<'a>) (gb : Gen<'b>) : Gen<'a * 'b> =
        { Draw = (fun r -> (ga.Draw r, gb.Draw r))
          Smaller =
            (fun p ->
                let a, b = p
                List.map (fun s -> (s, b)) (ga.Smaller a)
                @ List.map (fun s -> (a, s)) (gb.Smaller b))
          Render =
            (fun p ->
                let a, b = p
                "(" + ga.Render a + ", " + gb.Render b + ")") }

    let triple (ga : Gen<'a>) (gb : Gen<'b>) (gc : Gen<'c>) : Gen<'a * ('b * 'c)> =
        pair ga (pair gb gc)

    let listOf (maxLen : int) (g : Gen<'a>) : Gen<list<'a>> =
        { Draw =
            (fun r ->
                let n = rngBelow r (maxLen + 1)
                let mutable acc = []
                for i in 1 .. n do
                    acc <- g.Draw r :: acc
                acc)
          Smaller =
            (fun xs ->
                match xs with
                | [] -> []
                | h :: t ->
                    // empty, without the head, halved, then a smaller head
                    let halved = List.truncate (List.length xs / 2) xs
                    [ [] ; t ; halved ] @ List.map (fun s -> s :: t) (g.Smaller h))
          Render = (fun xs -> "[" + String.concat "; " (List.map (fun x -> g.Render x) xs) + "]") }

    let list (g : Gen<'a>) : Gen<list<'a>> = listOf 12 g

    let array (g : Gen<'a>) : Gen<'a[]> =
        let lg = list g
        { Draw = (fun r -> List.toArray (lg.Draw r))
          Smaller = (fun xs -> List.map List.toArray (lg.Smaller (Array.toList xs)))
          Render = (fun xs -> lg.Render (Array.toList xs)) }

    let map (gk : Gen<'k>) (gv : Gen<'v>) : Gen<Map<'k, 'v>> =
        let entries = list (pair gk gv)
        { Draw = (fun r -> Map.ofList (entries.Draw r))
          // one map with each key dropped
          Smaller = (fun m -> List.map (fun k -> Map.remove k m) (Map.keys m))
          Render =
            (fun m ->
                "map ["
                + String.concat "; " (List.map (fun (k, v) -> gk.Render k + " -> " + gv.Render v) (Map.toList m))
                + "]") }

    let set (g : Gen<'a>) : Gen<Set<'a>> =
        let items = list g
        { Draw = (fun r -> Set.ofList (items.Draw r))
          Smaller = (fun s -> List.map (fun x -> Set.remove x s) (Set.toList s))
          Render = (fun s -> "set [" + String.concat "; " (List.map (fun x -> g.Render x) (Set.toList s)) + "]") }

    let hashMap (gk : Gen<'k>) (gv : Gen<'v>) : Gen<HashNode<'k, 'v>> =
        let entries = list (pair gk gv)
        { Draw = (fun r -> HashMap.ofList (entries.Draw r))
          Smaller = (fun m -> List.map (fun k -> HashMap.remove k m) (HashMap.keys m))
          Render =
            (fun m ->
                "hashMap ["
                + String.concat "; "
                    (List.map (fun (k, v) -> gk.Render k + " -> " + gv.Render v)
                              (List.sortBy (fun (k, v) -> gk.Render k) (HashMap.toList m)))
                + "]") }

    let hashSet (g : Gen<'a>) : Gen<HashNode<'a, int>> =
        let items = list g
        { Draw = (fun r -> HashSet.ofList (items.Draw r))
          Smaller = (fun s -> List.map (fun x -> HashSet.remove x s) (HashSet.toList s))
          Render =
            (fun s ->
                "hashSet ["
                + String.concat "; " (List.map (fun x -> g.Render x) (List.sortBy (fun x -> g.Render x) (HashSet.toList s)))
                + "]") }

module Check =
    /// cases per property: enough to find real bugs without slowing a suite
    let count = 200

    /// every run starts here, so a failure reproduces exactly
    let seed = 20260730

    /// Run a property and RETURN the outcome — a test can assert on the string
    /// without a trap. A failing case is shrunk while it keeps failing, so the
    /// report names the smallest counterexample found.
    let runSeeded (sd : int) (name : string) (g : Gen<'a>) (p : 'a -> bool) : string =
        let r = Gen.rngCreate sd
        let mutable i = 0
        let mutable failure = ""
        while i < count && failure = "" do
            let v = g.Draw r
            if not (p v) then
                let mutable cur = v
                let mutable budget = 300
                let mutable going = true
                while going && budget > 0 do
                    budget <- budget - 1
                    match List.tryFind (fun c -> not (p c)) (g.Smaller cur) with
                    | Some smaller -> cur <- smaller
                    | None -> going <- false
                failure <- name + ": falsified by " + g.Render cur
            i <- i + 1
        if failure = "" then name + ": ok (" + string count + " cases)" else failure

    let run (name : string) (g : Gen<'a>) (p : 'a -> bool) : string = runSeeded seed name g p

    /// run it and say so
    let quick (name : string) (g : Gen<'a>) (p : 'a -> bool) : unit = print (run name g p)

    /// run it and FAIL the program if the property does not hold
    let required (name : string) (g : Gen<'a>) (p : 'a -> bool) : unit =
        let outcome = run name g p
        print outcome
        if outcome <> name + ": ok (" + string count + " cases)" then failwith outcome

// ---- Serialize: a wire format the compiler writes both ends of ----
// Nothing on the wire describes the wire. No header, no field name, no type
// tag: the writer and the reader are generated from the SAME declaration, so
// the shape is agreed at compile time and only the values travel. A union is
// the one exception — which case it is is genuinely dynamic, so it carries a
// one-byte tag.
//
// What makes this fast for the payloads that matter is that the interesting
// ones are already in wire form. An array of an all-scalar struct — V2d[],
// V3f[], anything `Memory` describes — is a C-layout image in linear memory,
// so shipping it is a `memory.copy` of that image rather than a walk over its
// elements. `Serialize` exposes that as `writeArray`/`readArray`: a per-
// element-type decision, so a V2d[] blits while a string[] walks, and the
// caller writes the same thing either way.

type Buffer(initial : int) =
    let mutable cap = if initial < 16 then 16 else initial
    let mutable ptr = Memory.alloc (if initial < 16 then 16 else initial)
    let mutable pos = 0
    /// where the bytes are — hand this to foreign code
    member x.Pointer = ptr
    /// how many bytes have been written
    member x.Length = pos
    member x.Reset () : unit = pos <- 0
    /// room for `n` more bytes. Growth re-allocates and copies once; a caller
    /// that knows the size up front (`Buffer size`) never pays it.
    member x.Reserve (n : int) : unit =
        if pos + n > cap then
            let mutable nc = cap * 2
            while nc < pos + n do
                nc <- nc * 2
            let np = Memory.alloc nc
            Memory.copy np ptr pos
            ptr <- np
            cap <- nc
    member x.WriteByte (v : int) : unit =
        x.Reserve 1
        Memory.storeByte (ptr + pos) v
        pos <- pos + 1
    member x.WriteInt (v : int) : unit =
        x.Reserve 4
        Memory.storeInt (ptr + pos) v
        pos <- pos + 4
    member x.WriteInt64 (v : int64) : unit =
        x.Reserve 8
        Memory.storeInt64 (ptr + pos) v
        pos <- pos + 8
    member x.WriteFloat (v : float) : unit =
        x.Reserve 8
        Memory.storeFloat (ptr + pos) v
        pos <- pos + 8
    /// THE BLIT: `n` bytes straight from `src`, one memory.copy instruction,
    /// whatever they mean.
    member x.WriteBlock (src : int) (n : int) : unit =
        x.Reserve n
        Memory.copy (ptr + pos) src n
        pos <- pos + n

type Reader(start : int) =
    let mutable p = start
    member x.Position = p
    member x.Skip (n : int) : unit = p <- p + n
    member x.ReadByte () : int =
        let v = Memory.loadByte p
        p <- p + 1
        v
    member x.ReadInt () : int =
        let v = Memory.loadInt p
        p <- p + 4
        v
    member x.ReadInt64 () : int64 =
        let v = Memory.loadInt64 p
        p <- p + 8
        v
    member x.ReadFloat () : float =
        let v = Memory.loadFloat p
        p <- p + 8
        v
    /// the address of the next `n` bytes, consumed WITHOUT copying them —
    /// the read side of `WriteBlock`
    member x.Block (n : int) : int =
        let a = p
        p <- p + n
        a

[<AutoOpen>]
class Serialize<'a>
    static write : Buffer -> 'a -> unit
    static read : Reader -> 'a
    /// A whole array, LENGTH AND ALL. Separate from `write` because this is
    /// where the element type gets to say "my arrays are already an image" —
    /// the blit. It owns the framing too, because a generic body cannot even
    /// ask a POD array for its length: such an array is a handle over a flat
    /// word image, not the uniform reference array a generic body compiles
    /// against. Keeping both the length and the data on this side means the
    /// one generic instance below never touches an array's representation.
    static writeArray : Buffer -> 'a[] -> unit
    static readArray : Reader -> 'a[]

instance Serialize<int>
    static write (b : Buffer) (v : int) = b.WriteInt v
    static read (r : Reader) = r.ReadInt ()
    static writeArray (b : Buffer) (xs : int[]) =
        let n = xs.Length
        b.WriteInt n
        b.Reserve (n * 4)
        let mutable i = 0
        while i < n do
            b.WriteInt xs.[i]
            i <- i + 1
    static readArray (r : Reader) =
        let n = r.ReadInt ()
        let xs = Array.zeroCreate n
        let mutable i = 0
        while i < n do
            xs.[i] <- r.ReadInt ()
            i <- i + 1
        xs

instance Serialize<int64>
    static write (b : Buffer) (v : int64) = b.WriteInt64 v
    static read (r : Reader) = r.ReadInt64 ()
    static writeArray (b : Buffer) (xs : int64[]) =
        let n = xs.Length
        b.WriteInt n
        b.Reserve (n * 8)
        let mutable i = 0
        while i < n do
            b.WriteInt64 xs.[i]
            i <- i + 1
    static readArray (r : Reader) =
        let n = r.ReadInt ()
        let xs = Array.zeroCreate n
        let mutable i = 0
        while i < n do
            xs.[i] <- r.ReadInt64 ()
            i <- i + 1
        xs

instance Serialize<float>
    static write (b : Buffer) (v : float) = b.WriteFloat v
    static read (r : Reader) = r.ReadFloat ()
    static writeArray (b : Buffer) (xs : float[]) =
        let n = xs.Length
        b.WriteInt n
        b.Reserve (n * 8)
        let mutable i = 0
        while i < n do
            b.WriteFloat xs.[i]
            i <- i + 1
    static readArray (r : Reader) =
        let n = r.ReadInt ()
        let xs = Array.zeroCreate n
        let mutable i = 0
        while i < n do
            xs.[i] <- r.ReadFloat ()
            i <- i + 1
        xs

instance Serialize<bool>
    static write (b : Buffer) (v : bool) = b.WriteByte (if v then 1 else 0)
    static read (r : Reader) = r.ReadByte () <> 0
    static writeArray (b : Buffer) (xs : bool[]) =
        let n = xs.Length
        b.WriteInt n
        b.Reserve n
        let mutable i = 0
        while i < n do
            b.WriteByte (if xs.[i] then 1 else 0)
            i <- i + 1
    static readArray (r : Reader) =
        let n = r.ReadInt ()
        let xs = Array.zeroCreate n
        let mutable i = 0
        while i < n do
            xs.[i] <- r.ReadByte () <> 0
            i <- i + 1
        xs

// A string is an i8 array at run time, so its characters ARE its bytes: the
// wire form is the runtime form, and it round-trips exactly what the runtime
// can hold.
instance Serialize<string>
    static write (b : Buffer) (v : string) =
        let n = v.Length
        b.WriteInt n
        b.Reserve n
        let mutable i = 0
        while i < n do
            b.WriteByte (int v.[i])
            i <- i + 1
    static read (r : Reader) =
        let n = r.ReadInt ()
        let cs = Array.zeroCreate n
        let mutable i = 0
        while i < n do
            cs.[i] <- string (char (r.ReadByte ()))
            i <- i + 1
        String.concat "" (Array.toList cs)
    static writeArray (b : Buffer) (xs : string[]) =
        let n = xs.Length
        b.WriteInt n
        let mutable i = 0
        while i < n do
            write b xs.[i]
            i <- i + 1
    static readArray (r : Reader) =
        let n = r.ReadInt ()
        let xs = Array.zeroCreate n
        let mutable i = 0
        while i < n do
            xs.[i] <- read r
            i <- i + 1
        xs

/// One array instance, delegating the interesting decision to the element
/// type. This is why a `V2d[][]` still works: the inner instance blits, the
/// outer one walks.
instance Serialize<'a[]> when Serialize<'a>
    static write (b : Buffer) (xs : 'a[]) = writeArray b xs
    static read (r : Reader) = readArray r
    // An array OF arrays is always a plain reference array whatever the leaf
    // element is, so this body may touch its length: the flat-image case is
    // one level down, and that level is `Serialize<'a>.writeArray` above.
    static writeArray (b : Buffer) (xs : 'a[][]) =
        let n = xs.Length
        b.WriteInt n
        let mutable i = 0
        while i < n do
            write b xs.[i]
            i <- i + 1
    static readArray (r : Reader) =
        let n = r.ReadInt ()
        let xs = Array.zeroCreate n
        let mutable i = 0
        while i < n do
            xs.[i] <- read r
            i <- i + 1
        xs

instance Serialize<list<'a>> when Serialize<'a>
    static write (b : Buffer) (xs : list<'a>) =
        b.WriteInt (List.length xs)
        let mutable cur = xs
        while not (List.isEmpty cur) do
            write b (List.head cur)
            cur <- List.tail cur
    static read (r : Reader) =
        let n = r.ReadInt ()
        let mutable acc = []
        let mutable i = 0
        while i < n do
            acc <- read r :: acc
            i <- i + 1
        List.rev acc
    static writeArray (b : Buffer) (xs : list<'a>[]) =
        b.WriteInt xs.Length
        let mutable i = 0
        while i < xs.Length do
            write b xs.[i]
            i <- i + 1
    static readArray (r : Reader) =
        let n = r.ReadInt ()
        let xs = Array.zeroCreate n
        let mutable i = 0
        while i < n do
            xs.[i] <- read r
            i <- i + 1
        xs

module Serialize =
    /// Serialize one value into a fresh buffer.
    let toBuffer (v : 'a) : Buffer =
        let b = Buffer 64
        write b v
        b
    /// Read one value back from an address.
    let ofPointer (p : int) : 'a = read (Reader p)

// ---- Worker: a typed message loop on the far side of a channel ----
// The channel itself is bytes — a worker has its own heap and cannot be
// handed a reference — so the types have to survive a crossing. They do
// because BOTH ends are generated from one declaration: `Command` and
// `Reply` are associated types, so the instance fixes them once and the
// encode on this side and the decode on that side cannot disagree.
//
// Nothing here knows how the bytes travel. `serve` is the worker's whole
// loop and `encodeCommand`/`decodeReply` are the host's; a `postMessage`
// transfer, a shared buffer and a pipe all carry the same message.

/// Which worker is on the other end. The type parameter is the whole point:
/// it is what makes `post` accept that worker's commands and nothing else.
/// It is also the WITNESS the four crossings below take — a member whose
/// arguments never mention 'w cannot be dispatched from inside a generic
/// body, because nothing there says which instance it belongs to.
type WorkerHandle<'w>(id : int) =
    /// the host's name for the channel
    member x.Id = id

[<AutoOpen>]
class Worker<'w>
    type Command
    type Reply
    /// The worker's state, built INSIDE the worker — it never crosses.
    static create : unit -> 'w
    static handle : 'w -> Command -> Reply
    // The four crossings. An instance writes these as `write b v` / `read r`
    // and they resolve there, where Command and Reply are concrete.
    static writeCommand : WorkerHandle<'w> -> Buffer -> Command -> unit
    static readCommand : WorkerHandle<'w> -> Reader -> Command
    static writeReply : WorkerHandle<'w> -> Buffer -> Reply -> unit
    static readReply : WorkerHandle<'w> -> Reader -> Reply

module Worker =
    /// A message is its own byte length followed by its bytes, so a host that
    /// cannot see these types still knows how much to hand over. That length
    /// is the ONLY thing on the wire that is not payload.
    let encodeCommand (h : WorkerHandle<'w>) (cmd : 'c) : Buffer
        when Worker<'w> with Command = 'c =
        let b = Buffer 64
        b.WriteInt 0
        writeCommand h b cmd
        Memory.storeInt b.Pointer (b.Length - 4)
        b

    /// Host side: the reply that came back at `p`.
    let decodeReply (h : WorkerHandle<'w>) (p : int) : 'r
        when Worker<'w> with Reply = 'r =
        readReply h (Reader (p + 4))

    /// WORKER side: the whole loop for one message. Decode the command at
    /// `p`, run it, encode the reply, and answer with its address. Export a
    /// one-line wrapper around this and the worker is done:
    ///
    ///     [<Export>]
    ///     let dispatch (p : int) : int = Worker.serve theWorker p
    let serve (self : WorkerHandle<'w>) (w : 'w) (p : int) : int when Worker<'w> =
        let cmd = readCommand self (Reader (p + 4))
        let reply = handle w cmd
        let b = Buffer 64
        b.WriteInt 0
        writeReply self b reply
        Memory.storeInt b.Pointer (b.Length - 4)
        b.Pointer

    /// How many bytes the message at `p` occupies, header included.
    let messageLength (p : int) : int = Memory.loadInt p + 4

// ==== System.Collections.Generic and System.Text ==========================
//
// The mutable collections, spelled the way .NET spells them, because the
// same source has to compile under F#. Two conventions follow from that and
// are not negotiable: a .NET method with several arguments takes a TUPLE
// (`d.Add (k, v)`), and a property with a setter is a real property, not a
// pair of functions.
//
// What is deliberately absent: `TryGetValue`, and every other method whose
// .NET signature needs a byref out-parameter. There is no byref here, and a
// `TryFind` returning an option would be a name F# does not have.
//
// All three implement `IEnumerable`, so the Seq module applies to them, and
// they hold their elements in a PACKED array — no boxing for an int. Those
// two used to be mutually exclusive: a vtable member is not specialized, so
// it read the packed array as uniform and the cast failed. Each
// instantiation of a class that implements an interface now carries its own
// vtable (DIVERGENCES.md), which is what buys both at once.

/// System.Collections.Generic.List<'a> — F# calls it ResizeArray, and so do
/// we. Backed by one array that doubles; `Item` is the .NET indexer, so
/// `xs.[i]` and `xs.[i] <- v` mean what they mean in F#.
type ResizeArray<'a>() =
    let mutable items : 'a[] = Array.zeroCreate 4
    let mutable count = 0
    /// room for `n` more elements, doubling so that n appends cost O(n)
    member x.Reserve (n : int) : unit =
        if count + n > items.Length then
            let mutable cap = items.Length * 2
            while cap < count + n do
                cap <- cap * 2
            let next : 'a[] = Array.zeroCreate cap
            Array.blit items 0 next 0 count
            items <- next
    member x.Count = count
    member x.Item
        with get (i : int) : 'a =
            if i < 0 || i >= count then failwith "Index was out of range."
            items.[i]
        and set (i : int) (v : 'a) =
            if i < 0 || i >= count then failwith "Index was out of range."
            items.[i] <- v
    member x.Add (v : 'a) : unit =
        x.Reserve 1
        items.[count] <- v
        count <- count + 1
    member x.AddRange (xs : seq<'a>) : unit =
        for v in xs do x.Add v
    member x.Insert (i : int, v : 'a) : unit =
        if i < 0 || i > count then failwith "Index was out of range."
        x.Reserve 1
        let mutable k = count
        while k > i do
            items.[k] <- items.[k - 1]
            k <- k - 1
        items.[i] <- v
        count <- count + 1
    member x.RemoveAt (i : int) : unit =
        if i < 0 || i >= count then failwith "Index was out of range."
        let mutable k = i
        while k < count - 1 do
            items.[k] <- items.[k + 1]
            k <- k + 1
        count <- count - 1
    member x.IndexOf (v : 'a) : int =
        let mutable found = -1
        let mutable i = 0
        while i < count do
            if found < 0 && items.[i] = v then found <- i
            i <- i + 1
        found
    member x.Contains (v : 'a) : bool = x.IndexOf v >= 0
    /// .NET removes the FIRST occurrence and answers whether it found one
    member x.Remove (v : 'a) : bool =
        let i = x.IndexOf v
        if i < 0 then false
        else
            x.RemoveAt i
            true
    member x.Clear () : unit = count <- 0
    member x.ToArray () : 'a[] = Array.init count (fun i -> items.[i])
    member x.Reverse () : unit =
        let mutable i = 0
        while i < count / 2 do
            let t = items.[i]
            items.[i] <- items.[count - 1 - i]
            items.[count - 1 - i] <- t
            i <- i + 1
    /// `for x in xs` is STRUCTURAL — it looks for a GetEnumerator on the type
    /// in front of it, and finds this one. The interface implementation
    /// below is what makes `xs :> seq<'a>` and the whole Seq module work;
    /// it dispatches to the copy of this member stamped at THIS element
    /// type, which is what per-instantiation vtables buy.
    member x.GetEnumerator () : IEnumerator<'a> =
        (x.ToArray () :> seq<'a>).GetEnumerator ()
    interface IEnumerable<'a> with
        member x.GetEnumerator () = (x.ToArray () :> seq<'a>).GetEnumerator ()

/// `ResizeArray<'a>` is F#'s abbreviation for this; `List<'a>` is what .NET
/// calls it, and what F# code means once `System.Collections.Generic` is
/// open. The `List` MODULE is a different thing under the same name, exactly
/// as in F# — one is a type, the other is a namespace of functions over the
/// immutable `list`.
type List<'a> = ResizeArray<'a>

/// System.Collections.Generic.Dictionary. Open-addressed over
/// INSERTION-ORDERED entries: the slot table holds one-based indices into
/// three parallel arrays, so enumeration is deterministic and the keys stay
/// in a packed array — no boxing for an `int` key. Each entry's hash is kept
/// beside it, so a probe that lands on the wrong entry is rejected on one
/// int compare instead of a structural one.
type Dictionary<'k, 'v>() =
    let mutable dkeys : 'k[] = Array.zeroCreate 8
    let mutable dvals : 'v[] = Array.zeroCreate 8
    let mutable dhashes : int[] = Array.zeroCreate 8
    let mutable dslots : int[] = Array.zeroCreate 16
    let mutable dcount = 0
    /// the slot `k` belongs in: either its entry's, or the first free one.
    /// The table is never more than half full, so this terminates.
    member x.SlotOfHash (k : 'k, h : int) : int =
        let mask = dslots.Length - 1
        let mutable i = h &&& mask
        let mutable found = -1
        while found < 0 do
            let e = dslots.[i]
            if e = 0 then found <- i
            elif dhashes.[e - 1] = h && dkeys.[e - 1] = k then found <- i
            else i <- (i + 1) &&& mask
        found
    member x.SlotOf (k : 'k) : int = x.SlotOfHash (k, hash k &&& 1073741823)
    member x.Rehash () : unit =
        let slots : int[] = Array.zeroCreate (dslots.Length * 2)
        let mask = slots.Length - 1
        let mutable e = 0
        while e < dcount do
            // the STORED hash: rehashing must not recompute what it has
            let mutable i = dhashes.[e] &&& mask
            while slots.[i] <> 0 do
                i <- (i + 1) &&& mask
            slots.[i] <- e + 1
            e <- e + 1
        dslots <- slots
    member x.Count = dcount
    member x.ContainsKey (k : 'k) : bool = dslots.[x.SlotOf k] > 0
    member x.Item
        with get (k : 'k) : 'v =
            let e = dslots.[x.SlotOf k]
            if e = 0 then failwith "The given key was not present in the dictionary."
            dvals.[e - 1]
        and set (k : 'k) (v : 'v) =
            let h = hash k &&& 1073741823
            let s = x.SlotOfHash (k, h)
            let e = dslots.[s]
            if e > 0 then dvals.[e - 1] <- v
            else
                if dcount >= dkeys.Length then
                    let keys : 'k[] = Array.zeroCreate (dkeys.Length * 2)
                    let vals : 'v[] = Array.zeroCreate (dvals.Length * 2)
                    let hs : int[] = Array.zeroCreate (dkeys.Length * 2)
                    Array.blit dkeys 0 keys 0 dcount
                    Array.blit dvals 0 vals 0 dcount
                    Array.blit dhashes 0 hs 0 dcount
                    dkeys <- keys
                    dvals <- vals
                    dhashes <- hs
                dkeys.[dcount] <- k
                dvals.[dcount] <- v
                dhashes.[dcount] <- h
                dcount <- dcount + 1
                // under half full: probes stay short, and the "never full"
                // invariant the probe relies on holds
                if dcount * 2 >= dslots.Length then x.Rehash ()
                else dslots.[s] <- dcount
    /// .NET REFUSES a duplicate here — `d.[k] <- v` is the overwriting form
    member x.Add (k : 'k, v : 'v) : unit =
        if x.ContainsKey k then failwith "An item with the same key has already been added."
        x.[k] <- v
    member x.ContainsValue (v : 'v) : bool =
        let mutable found = false
        let mutable i = 0
        while i < dcount do
            if dvals.[i] = v then found <- true
            i <- i + 1
        found
    /// The survivors SHIFT DOWN and the index is rebuilt, so entries stay
    /// insertion-ordered. A tombstone would be cheaper, but the probe walks
    /// until it finds an empty slot, and enumeration order is worth more.
    member x.Remove (k : 'k) : bool =
        let e = dslots.[x.SlotOf k]
        if e = 0 then false
        else
            let mutable i = e - 1
            while i < dcount - 1 do
                dkeys.[i] <- dkeys.[i + 1]
                dvals.[i] <- dvals.[i + 1]
                dhashes.[i] <- dhashes.[i + 1]
                i <- i + 1
            dcount <- dcount - 1
            let slots : int[] = Array.zeroCreate dslots.Length
            let mask = slots.Length - 1
            let mutable j = 0
            while j < dcount do
                let mutable p = dhashes.[j] &&& mask
                while slots.[p] <> 0 do
                    p <- (p + 1) &&& mask
                slots.[p] <- j + 1
                j <- j + 1
            dslots <- slots
            true
    member x.Clear () : unit =
        dcount <- 0
        dslots <- Array.zeroCreate dslots.Length
    /// ConcurrentDictionary surface, minus the concurrency: wasm is
    /// single-threaded, so the atomicity these promise is free
    member x.TryAdd (k : 'k, v : 'v) : bool =
        if x.ContainsKey k then false
        else
            x.Add (k, v)
            true
    member x.TryRemove (k : 'k, value : byref<'v>) : bool =
        if x.TryGetValue (k, &value) then
            x.Remove k |> ignore
            true
        else false
    /// `match d.TryGetValue k with | (true, v) -> ...` and
    /// `d.TryGetValue(k, &v)` are both this one declaration.
    member x.TryGetValue (k : 'k, value : byref<'v>) : bool =
        let e = dslots.[x.SlotOf k]
        if e = 0 then
            value <- dvals.[0]
            false
        else
            value <- dvals.[e - 1]
            true
    member x.KeyArray () : 'k[] = Array.init dcount (fun i -> dkeys.[i])
    member x.ValueArray () : 'v[] = Array.init dcount (fun i -> dvals.[i])
    /// .NET hands back a KeyCollection; what every caller does with it is
    /// enumerate, so a seq is the same thing minus the wrapper
    member x.Keys : seq<'k> = x.KeyArray () :> seq<'k>
    member x.Values : seq<'v> = x.ValueArray () :> seq<'v>
    member x.GetEnumerator () : IEnumerator<KeyValuePair<'k, 'v>> =
        (Array.init dcount (fun i -> KeyValuePair<'k, 'v>(dkeys.[i], dvals.[i])) :> seq<KeyValuePair<'k, 'v>>).GetEnumerator ()
    interface IEnumerable<KeyValuePair<'k, 'v>> with
        member x.GetEnumerator () =
            (Array.init dcount (fun i -> KeyValuePair<'k, 'v>(dkeys.[i], dvals.[i])) :> seq<KeyValuePair<'k, 'v>>).GetEnumerator ()

/// System.Collections.Generic.HashSet — the same table without the values,
/// under a DIFFERENT NAME. `HashSet` is taken twice over: by this prelude's
/// own immutable one and by FSharp.Data.Adaptive's, which the acceptance
/// corpus ports. A user type whose name matches a prelude type merges with
/// it rather than shadowing it (see DIVERGENCES.md), so claiming the .NET
/// name would break every program that declares its own. The members are
/// .NET's exactly; only the type's name differs.
/// walks a MutableHashSet's DENSE key array (0 .. count-1)
type MutableHashSetEnumerator<'a>(keys : 'a[], count : int) =
    let mutable i = 0 - 1
    member x.MoveNext () : bool =
        i <- i + 1
        i < count
    member x.Current : 'a = keys.[i]
type MutableHashSet<'a>() =
    let mutable skeys : 'a[] = Array.zeroCreate 8
    let mutable shashes : int[] = Array.zeroCreate 8
    let mutable sslots : int[] = Array.zeroCreate 16
    let mutable scount = 0
    member x.SlotOfHash (k : 'a, h : int) : int =
        let mask = sslots.Length - 1
        let mutable i = h &&& mask
        let mutable found = 0 - 1
        while found < 0 do
            let e = sslots.[i]
            if e = 0 then found <- i
            elif shashes.[e - 1] = h && skeys.[e - 1] = k then found <- i
            else i <- (i + 1) &&& mask
        found
    member x.SlotOf (k : 'a) : int = x.SlotOfHash (k, hash k &&& 1073741823)
    member x.Rehash () : unit =
        let slots : int[] = Array.zeroCreate (sslots.Length * 2)
        let mask = slots.Length - 1
        let mutable e = 0
        while e < scount do
            let mutable i = shashes.[e] &&& mask
            while slots.[i] <> 0 do
                i <- (i + 1) &&& mask
            slots.[i] <- e + 1
            e <- e + 1
        sslots <- slots
    member x.Count = scount
    member x.GetEnumerator () = MutableHashSetEnumerator<'a>(skeys, scount)
    member x.Contains (v : 'a) : bool = sslots.[x.SlotOf v] > 0
    /// .NET answers whether the element was NEW
    member x.Add (v : 'a) : bool =
        let h = hash v &&& 1073741823
        let s = x.SlotOfHash (v, h)
        if sslots.[s] > 0 then false
        else
            if scount >= skeys.Length then
                let keys : 'a[] = Array.zeroCreate (skeys.Length * 2)
                let hs : int[] = Array.zeroCreate (skeys.Length * 2)
                Array.blit skeys 0 keys 0 scount
                Array.blit shashes 0 hs 0 scount
                skeys <- keys
                shashes <- hs
            skeys.[scount] <- v
            shashes.[scount] <- h
            scount <- scount + 1
            if scount * 2 >= sslots.Length then x.Rehash ()
            else sslots.[s] <- scount
            true
    /// The survivors SHIFT DOWN and the index is rebuilt, so elements stay
    /// insertion-ordered — the same trade the Dictionary makes.
    member x.Remove (v : 'a) : bool =
        let e = sslots.[x.SlotOf v]
        if e = 0 then false
        else
            let mutable i = e - 1
            while i < scount - 1 do
                skeys.[i] <- skeys.[i + 1]
                shashes.[i] <- shashes.[i + 1]
                i <- i + 1
            scount <- scount - 1
            let slots : int[] = Array.zeroCreate sslots.Length
            let mask = slots.Length - 1
            let mutable j = 0
            while j < scount do
                let mutable p = shashes.[j] &&& mask
                while slots.[p] <> 0 do
                    p <- (p + 1) &&& mask
                slots.[p] <- j + 1
                j <- j + 1
            sslots <- slots
            true
    member x.Clear () : unit =
        scount <- 0
        sslots <- Array.zeroCreate sslots.Length
    member x.UnionWith (xs : seq<'a>) : unit =
        for v in xs do x.Add v |> ignore
    member x.ExceptWith (xs : seq<'a>) : unit =
        for v in xs do x.Remove v |> ignore
    member x.IsSubsetOf (xs : seq<'a>) : bool =
        let other = MutableHashSet<'a>()
        other.UnionWith xs
        let mutable ok = true
        let mutable i = 0
        while i < scount do
            if not (other.Contains skeys.[i]) then ok <- false
            i <- i + 1
        ok
    member x.Overlaps (xs : seq<'a>) : bool =
        let mutable any = false
        for v in xs do
            if x.Contains v then any <- true
        any
    /// ours, not .NET's — the seam to the Array and Seq modules, which a
    /// class holding a PACKED array cannot offer through IEnumerable
    member x.ToArray () : 'a[] = Array.init scount (fun i -> skeys.[i])
    member x.GetEnumerator () : IEnumerator<'a> =
        (x.ToArray () :> seq<'a>).GetEnumerator ()
    interface IEnumerable<'a> with
        member x.GetEnumerator () = (x.ToArray () :> seq<'a>).GetEnumerator ()

/// System.Threading, on a runtime with ONE thread.
///
/// These are not stubs. A single-threaded runtime genuinely enters and
/// exits every lock, and an increment genuinely is atomic when nothing else
/// can run between the read and the write — so each of these does exactly
/// what .NET's does, under the assumption the platform enforces. What is
/// absent is any way to BLOCK: `Monitor.Enter` on a lock someone else holds
/// cannot happen, so there is nothing to wait for.
type Monitor =
    static member Enter (o : obj) : unit = ()
    static member Exit (o : obj) : unit = ()
    static member IsEntered (o : obj) : bool = true
    static member TryEnter (o : obj) : bool = true

/// F#'s `lock`: run the body, which is the whole of it here.
let lock (o : 'a) (f : unit -> 'b) : 'b = f ()

/// System.Threading.Interlocked. Every one takes the location by REFERENCE,
/// as .NET's does, and returns what .NET returns — `Increment` the NEW
/// value, `Exchange` and `CompareExchange` the OLD one.
type Interlocked =
    static member Increment (location : byref<int>) : int =
        location <- location + 1
        location
    static member Decrement (location : byref<int>) : int =
        location <- location - 1
        location
    /// GENERIC, as .NET's are: a list, a reference, an int — anything a
    /// location can hold. `Interlocked.Exchange(&finalizers, [])` swaps a
    /// list, and declaring these at `int` alone made that a type error.
    static member Exchange (location : byref<'a>, value : 'a) : 'a =
        let old = location
        location <- value
        old
    static member CompareExchange (location : byref<'a>, value : 'a, comparand : 'a) : 'a =
        let old = location
        if old = comparand then location <- value
        old

/// System.Lazy — a memoized thunk.
type Lazy<'a>(f : unit -> 'a) =
    let mutable computed = false
    let mutable stored : 'a = Unchecked.defaultof<'a>
    member x.Value : 'a =
        if not computed then
            stored <- f ()
            computed <- true
        stored
    member x.IsValueCreated = computed
    member x.Force () : 'a = x.Value

/// System.WeakReference — a STRONG reference.
///
/// wasm-GC has no weak references and no finalizers: there is no way to
/// observe that a value became unreachable, and no way to be told. So this
/// holds its target and `TryGetTarget` always succeeds. Every program that
/// only READS through a weak reference behaves identically; what changes is
/// that nothing collected through one is ever released, so a graph that
/// relied on weakness to drop its dead half keeps it.
///
/// This is a divergence with teeth, and it is written down in
/// DIVERGENCES.md rather than hidden here.
type WeakReference<'a>(value : 'a) =
    /// .NET's signature. The tuple view — `match w.TryGetTarget () with |
    /// (true, t) -> ...` — is the compiler's, as it is in F#.
    member x.TryGetTarget (target : byref<'a>) : bool =
        target <- value
        true
    member x.Target = value
    member x.IsAlive = true

/// System.Runtime.CompilerServices.ConditionalWeakTable — an IDENTITY-keyed
/// table, strong for the same reason WeakReference is.
///
/// Identity, not structure: the .NET table compares keys by reference, and
/// the values it holds are keyed on objects whose structural equality would
/// be both wrong and expensive. Linear probing over insertion-ordered
/// entries, like Dictionary, but the probe tests `ReferenceEquals`.
type ConditionalWeakTable<'k, 'v>() =
    let mutable ckeys : 'k[] = Array.zeroCreate 8
    let mutable cvals : 'v[] = Array.zeroCreate 8
    let mutable ccount = 0
    member x.IndexOf (k : 'k) : int =
        let mutable found = 0 - 1
        let mutable i = 0
        while i < ccount do
            if found < 0 && System.Object.ReferenceEquals (ckeys.[i], k) then found <- i
            i <- i + 1
        found
    member x.TryGetValue (k : 'k, value : byref<'v>) : bool =
        let i = x.IndexOf k
        if i < 0 then
            value <- cvals.[0]
            false
        else
            value <- cvals.[i]
            true
    member x.Add (k : 'k, v : 'v) : unit =
        if ccount >= ckeys.Length then
            let nk : 'k[] = Array.zeroCreate (ckeys.Length * 2)
            let nv : 'v[] = Array.zeroCreate (cvals.Length * 2)
            Array.blit ckeys 0 nk 0 ccount
            Array.blit cvals 0 nv 0 ccount
            ckeys <- nk
            cvals <- nv
        ckeys.[ccount] <- k
        cvals.[ccount] <- v
        ccount <- ccount + 1
    member x.Remove (k : 'k) : bool =
        let i = x.IndexOf k
        if i < 0 then false
        else
            let mutable j = i
            while j < ccount - 1 do
                ckeys.[j] <- ckeys.[j + 1]
                cvals.[j] <- cvals.[j + 1]
                j <- j + 1
            ccount <- ccount - 1
            true
    member x.Count = ccount

/// System.Text.StringBuilder. Appending is O(1) — the chunks are joined once,
/// by the pairwise merge in String.concat, when the text is asked for. A left
/// fold over `+` would copy the whole accumulator at every step.
type StringBuilder() =
    let chunks = ResizeArray<string>()
    let mutable total = 0
    member x.Length = total
    /// .NET returns the builder, so appends chain
    member x.Append (s : string) : StringBuilder =
        chunks.Add s
        total <- total + s.Length
        x
    /// .NET overloads Append for every primitive; the char one is what
    /// character-at-a-time code (a framing reader, a lexer) actually calls
    member x.Append (c : char) : StringBuilder = x.Append (string c)
    member x.AppendLine (s : string) : StringBuilder = x.Append (s + "\n")
    member x.Clear () : StringBuilder =
        chunks.Clear ()
        total <- 0
        x
    override x.ToString () : string = String.concat "" (chunks.ToArray () :> seq<string>)
