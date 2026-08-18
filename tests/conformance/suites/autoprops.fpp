// Auto-properties (`member val`, fsc members-suite shapes) and the
// numeric-of-string conversions the same round fixed: `member val P = init
// with get, set` is a backing field plus accessors, init runs ONCE at
// construction, the bare form is get-only.
module Core_autoprops

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

let mutable initCount = 0

type P() =
    member val X = (initCount <- initCount + 1; initCount * 10) with get, set
    member val RO = 5
    member this.Sum = this.X + this.RO

let p1 = P()
test "av1" (initCount = 1)
test "av2" (p1.X = 10)
test "av3" (p1.RO = 5)
test "av4" (p1.Sum = 15)
p1.X <- 99
test "av5" (p1.X = 99)
test "av6" (initCount = 1)
let p2 = P()
test "av7" (initCount = 2)
test "av8" (p2.X = 20)
test "av9" (p1.X = 99)

// an auto-property between ordinary members, reading a ctor argument
type Q(seed : int) =
    member this.Half = this.Level / 2
    member val Level = seed * 3 with get, set
    member this.Bump (n : int) = this.Level <- this.Level + n

let q = Q(4)
test "av10" (q.Level = 12)
test "av11" (q.Half = 6)
q.Bump 8
test "av12" (q.Level = 20)

// static auto-property, get-only
type S() =
    static member val Origin = 7
    member val Tag = "t" with get, set

test "av13" (S.Origin = 7)
let s1 = S()
s1.Tag <- "u"
test "av14" (s1.Tag = "u")

// numeric-of-string conversions
let i64 = int64 "123"
test "cv1" (i64 = 123L)
test "cv2" (int64 "-9876543210" = -9876543210L)
let u64 = uint64 "77"
test "cv3" (u64 = 77UL)
test "cv4" (uint64 "9007199254" = 9007199254UL)
test "cv5" (int64 (uint64 "42") = 42L)
test "cv6" (int "-345" = -345)

printfn "DONE tests=%d failures=%d" ntests failures
