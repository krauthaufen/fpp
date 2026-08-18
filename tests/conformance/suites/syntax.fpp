// The portable core of fsc's syntax test, converted to self-checking
// asserts: bit operators across widths, exception raise/catch shapes,
// loop forms, arrays and char arithmetic, tuples, the List/Option
// samples, generic comparison, records, unions, escape characters and
// negative-sign precedence. Dropped: %A printing, DateTime/Regex/WinForms,
// dynamic `?` operators, SRTP modules, `;;` and `let..in` legacy forms.
module Core_syntax

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// bit operators over int, int64, uint64 and byte
test "bit1" ((0xAB7F3456 &&& 0xFFFF0000) = 0xAB7F0000)
test "bit2" ((0x12343456 ^^^ 0x7FFF0000) = 0x6DCB3456)
test "bit3" ((0x1234ABCD <<< 1) = 0x2469579A)
test "bit4" ((0x1234ABCD >>> 16) = 0x1234)
test "bit5" ((0x0A0A0A0A012343456L &&& 0x00000000FFFF0000L) = 0x12340000L)
test "bit6" ((0x0A0A0A0A012343456UL &&& 0x0000FFFF00000000UL) = 0x0000A0A000000000UL)
test "bit7" ((0x13uy &&& 0x11uy) = 0x11uy)
test "bit8" ((0x1234ABCD ||| 0x40000000) = 0x5234ABCD)

// exceptions: failwith caught as Failure, catch-all, rethrow-free flow
let exc1 =
    try
        failwith "Whoa!"
        "unreached"
    with
    | Failure msg -> "caught " + msg
test "exc1" (exc1 = "caught Whoa!")

let exc2 =
    try raise (Failure "not Monday") with
    | Failure msg -> msg
test "exc2" (exc2 = "not Monday")

// loop forms: for-to, for-downto, nested, while over a ref
let mutable acc1 = 0
for i = 1 to 10 do acc1 <- acc1 + i
test "for1" (acc1 = 55)
let mutable acc2 = 0
for i = 10 downto 1 do acc2 <- acc2 * 2 + (i % 2)
test "for2" (acc2 = 341)
let mutable acc3 = 0
for i = 0 to 9 do
    for _j = i to 9 do
        acc3 <- acc3 + 1
test "for3" (acc3 = 55)
let count = ref 0
while (!count) < 10 do count := (!count) + 2
test "whl1" ((!count) = 10)

// recursion
let rec fib n = if n < 2 then 1 else fib (n - 1) + fib (n - 2)
test "fib1" (fib 10 = 89)

// arrays: prefix sums and letter counting over a string
let size = 1000
let arr = Array.create size 0
for i = 1 to size - 1 do arr.[i] <- i + arr.[i - 1]
test "arr1" (arr.[999] = 499500)
test "arr2" (arr.[1] = 1)

let results = Array.create 26 0
let data = "The quick brown fox jumps over the lazy dog"
for i = 0 to data.Length - 1 do
    let c = System.Char.ToUpper data.[i]
    if c >= 'A' && c <= 'Z' then
        let k = int c - int 'A'
        results.[k] <- results.[k] + 1
test "cnt1" (results.[int 'O' - int 'A'] = 4)
test "cnt2" (results.[int 'E' - int 'A'] = 3)
test "cnt3" (results.[int 'Z' - int 'A'] = 1)

// tuple plumbing through a function composed with itself
let tf (a, b, c) = (a + b, b + c, c + a)
let tres = tf (tf (tf (1, 2, 3)))
test "tup1" (tres = (17, 16, 15))
let r1, r2, r3 = tres
test "tup2" (r1 + r2 + r3 = 48)

// the List samples, asserted
let ldata = [ 1; 2; 3; 4 ]
test "lst1" (List.head ldata = 1)
test "lst2" (List.tail ldata = [ 2; 3; 4 ])
test "lst3" (List.length ldata = 4)
test "lst4" (not (List.isEmpty ldata))
let consume (d : int list) =
    match d with
    | 1 :: rest -> rest
    | 2 :: 3 :: rest -> rest
    | [ 4 ] -> []
    | _ -> []
test "lst5" (consume (consume (consume ldata)) = [])
test "lst6" (List.map (fun x -> x + 1) ldata = [ 2; 3; 4; 5 ])
test "lst7" (List.map (fun x -> (x, x)) ldata = [ (1, 1); (2, 2); (3, 3); (4, 4) ])
let mutable iterAcc = 0
ldata |> List.iter (fun x -> iterAcc <- iterAcc * 10 + x)
test "lst8" (iterAcc = 1234)
let mutable iteriAcc = 0
// a TOP-LEVEL statement starting with `[` (only `[<` opens an attribute)
[ "Cats"; "Dogs"; "Mice" ] |> List.iteri (fun i x -> iteriAcc <- iteriAcc + i * x.Length)
test "lst9" (iteriAcc = 12)
let animals = [ ("Cats", 4); ("Dogs", 5); ("Mice", 3); ("Elephants", 2) ]
test "lst10" (List.fold (fun a (_nm, x) -> a + x) 0 animals = 14)
test "lst11" (List.filter (fun (nm, _x) -> String.length nm <= 4) animals = [ ("Cats", 4); ("Dogs", 5); ("Mice", 3) ])
test "lst12" (List.choose (fun (nm, x) -> if String.length nm <= 4 then Some x else None) animals = [ 4; 5; 3 ])

// Options
let odata = Some (1, 3)
test "opt1" (Option.isSome odata)
test "opt2" (not (Option.isNone odata))
test "opt3" (Option.get odata = (1, 3))
let odata2 : (int * int) option = None
test "opt4" (Option.isNone odata2)

// generic comparison and equality over structured values
test "cmp1" (compare (1, 2) (1, 3) < 0)
test "cmp2" (compare [ 1; 2; 3 ] [ 1; 2; 3 ] = 0)
test "cmp3" (compare "abc" "abd" < 0)
test "cmp5" (( [ 1; 2 ], "a" ) < ( [ 1; 2 ], "b" ))

// records: construction, field access, equality, update
type Pointr = { x : float; y : float }
let p1 = { x = 3.0; y = 4.0 }
let p2 = { p1 with y = 5.0 }
test "rec1" (p1.x = 3.0 && p1.y = 4.0)
test "rec2" (p2 = { x = 3.0; y = 5.0 })
test "rec3" (p1 <> p2)

// unions: the wheel/cycle sample
type Wheel = Wheel of float
type Cycle =
    | Unicycle of Wheel
    | Bicycle of Wheel * Wheel
let wheelRadius (w : Wheel) = match w with Wheel r -> r
let totalRadius (c : Cycle) =
    match c with
    | Unicycle w -> wheelRadius w
    | Bicycle (a, b) -> wheelRadius a + wheelRadius b
test "uni1" (totalRadius (Unicycle (Wheel 2.5)) = 2.5)
test "uni2" (totalRadius (Bicycle (Wheel 1.0, Wheel 1.5)) = 2.5)

// escape characters
test "esc1" (int '\n' = 10)
test "esc2" (int '\t' = 9)
test "esc3" (int '\\' = 92)
test "esc4" ("a\nb".Length = 3)
test "esc5" (int '\'' = 39)
test "esc6" ("\"".Length = 1)

// negative-sign precedence: `R -x` applies R to (-x)
let idf (x : int) = x
let idf2 (x : int) (_y : int) = x
let nx = 1
test "neg1" (idf -nx = -1)
test "neg2" (idf2 -nx -nx = -1)
test "neg3" (idf2 nx -nx = 1)
test "neg4" (-idf 3 = -3)
test "neg5" (3 - -4 = 7)

printfn "DONE tests=%d failures=%d" ntests failures
