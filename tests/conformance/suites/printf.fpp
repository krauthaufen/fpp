// The printf family, from dotnet/fsharp tests/fsharp/core/printf/test.fsx
// in the supported subset: %d %i %u %s %c %b %x %X %o %f %A and %%, width
// with the 0/- flags. Deliberately absent in F++ (Format.fs): %e %g,
// precision (.N), %B, %+ — those REJECT at compile time, not silently.
module Core_printf

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// %o — octal, two's complement for negatives (cewoui2* in the original)
test "o1" (sprintf "%o" 0 = "0")
test "o2" (sprintf "%o" 5 = "5")
test "o3" (sprintf "%o" 8 = "10")
test "o4" (sprintf "%o" 15 = "17")
test "o5" (sprintf "%o" (-2147483647 - 1) = "20000000000")
test "o6" (sprintf "%o" (-2147483647) = "20000000001")
test "o7" (sprintf "%o" 2147483647 = "17777777777")
test "o8" (sprintf "%o" (-1) = "37777777777")
test "o9" (sprintf "%o" (-9223372036854775807L - 1L) = "1000000000000000000000")
test "o10" (sprintf "%o" 18446744073709551615UL = "1777777777777777777777")

// %x / %X — hex both cases
test "x1" (sprintf "%x" 0 = "0")
test "x2" (sprintf "%x" 255 = "ff")
test "x3" (sprintf "%X" 255 = "FF")
test "x4" (sprintf "%x" (-1) = "ffffffff")
test "x5" (sprintf "%X" (-1) = "FFFFFFFF")
test "x6" (sprintf "%x" 305419896 = "12345678")
test "x7" (sprintf "%x" 255L = "ff")
test "x8" (sprintf "%X" 48879UL = "BEEF")
test "x9" (sprintf "%x" (-1L) = "ffffffffffffffff")

// %d / %i / %u across widths and 64 bits
test "d1" (sprintf "%d" 42 = "42")
test "d2" (sprintf "%i" (-42) = "-42")
test "d3" (sprintf "%d" 5000000000L = "5000000000")
test "d4" (sprintf "%d" (-5000000000L) = "-5000000000")
test "d5" (sprintf "%d" (-9223372036854775807L - 1L) = "-9223372036854775808")
test "d6" (sprintf "%d" 9223372036854775807L = "9223372036854775807")
test "d7" (sprintf "%d" 18446744073709551615UL = "18446744073709551615")
test "d8" (sprintf "%u" 42 = "42")
test "d9" (sprintf "%d" 0L = "0")

// widths and flags
test "w1" (sprintf "%5d" 42 = "   42")
test "w2" (sprintf "%-5d" 42 = "42   ")
test "w3" (sprintf "%05d" 42 = "00042")
test "w4" (sprintf "%02x" 5 = "05")
test "w5" (sprintf "%08x" 255 = "000000ff")
test "w6" (sprintf "%10s" "hi" = "        hi")
test "w7" (sprintf "%-10s" "hi" = "hi        ")
test "w8" (sprintf "%3d" 12345 = "12345")
test "w9" (sprintf "%5d" (-42) = "  -42")

// %s %c %b and %%
test "s1" (sprintf "%s" "abc" = "abc")
test "s2" (sprintf "%c" 'q' = "q")
test "s3" (sprintf "%b" true = "true")
test "s4" (sprintf "%b" false = "false")
test "s5" (sprintf "a%%b" = "a%b")
test "s6" (sprintf "%s-%d-%c" "x" 7 'y' = "x-7-y")

// %f — fixed six decimals
test "f1" (sprintf "%f" 3.5 = "3.500000")
test "f2" (sprintf "%f" 0.0 = "0.000000")
test "f3" (sprintf "%f" (-1.25) = "-1.250000")

// a partially applied format is a function
let fo = sprintf "%o"
test "p1" (fo 8 = "10")
test "p2" (fo 15 = "17")
let fd = sprintf "%d-%d"
test "p3" (fd 1 2 = "1-2")

printfn "DONE tests=%d failures=%d" ntests failures
