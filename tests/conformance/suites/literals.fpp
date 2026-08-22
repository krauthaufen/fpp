// CONSTANT EXPRESSIONS, ported from dotnet/fsharp's
// tests/FSharp.Compiler.ComponentTests/Conformance/Expressions/
// ConstantExpressions (one file per type: int, int64, byte, char, string,
// float, uint*, nativeint, bool, unit) and the literal cases of
// LexicalAnalysis.
//
// Every literal here is checked for its VALUE and, where the width matters,
// for the arithmetic that only the right width answers correctly — a byte
// literal read as an int and a char escape read one character wrong both
// show up as a wrong number rather than a build error.
//
// DROPPED: `bigint` (`123I` — no arbitrary-precision type here), decimal
// (`1.0M`), and `float32` printing (its shortest-round-trip spelling is
// single-precision, a separate arc).
module Core_literals

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- integers, and every suffix ------------------------------------------

let i32 = 42
let i8 = 42y
let u8 = 42uy
let i16 = 42s
let u16 = 42us
let u32 = 42u
let i64 = 42L
let u64 = 42UL
let ni = 42n
let un = 42un

test "int32" (i32 = 42)
test "sbyte" (int i8 = 42)
test "byte" (int u8 = 42)
test "int16" (int i16 = 42)
test "uint16" (int u16 = 42)
test "uint32" (int u32 = 42)
test "int64" (i64 = 42L)
test "uint64" (u64 = 42UL)
test "nativeint" (int ni = 42)
test "unativeint" (int un = 42)

// the suffix decides the ARITHMETIC, not just the annotation
test "byte-wraps" (int (200uy + 100uy) = 44)
test "sbyte-wraps" (int (100y + 100y) = 0 - 56)
test "int16-wraps" (int (30000s + 10000s) = 0 - 25536)
test "uint32-large" (4000000000u > 2000000000u)
test "int64-beyond-int32" (i64 * 100000000L = 4200000000L)
test "uint64-large" (18000000000000000000UL > 9000000000000000000UL)

// ---- the bases -----------------------------------------------------------

test "hex" (0xFF = 255)
test "hex-lower" (0xff = 255)
test "octal" (0o17 = 15)
test "binary" (0b1011 = 11)
test "hex-suffixed" (0xFFuy = 255uy)
test "hex-int64" (0xFFFFFFFFFFL = 1099511627775L)
test "binary-int64" (0b1000000000000000000000000000000000L = 8589934592L)

// an underscore is a digit separator
test "separator-decimal" (1_000_000 = 1000000)
test "separator-hex" (0xFF_FF = 65535)

// the extremes of each width
// 2147483648 is not writable as an int32 literal (FS1147) — the minimum is
// spelled by subtracting from the maximum
test "int32-max" (2147483647 + 1 = 0 - 2147483647 - 1)
test "int32-min" (0 - 2147483647 - 1 - 1 = 2147483647)
test "int64-max" (9223372036854775807L + 1L = 0L - 9223372036854775807L - 1L)
test "byte-max" (255uy + 1uy = 0uy)

// ---- floats ---------------------------------------------------------------

test "float-plain" (1.5 = 1.5)
test "float-exponent" (1.5e2 = 150.0)
test "float-negative-exponent" (1.5e-2 = 0.015)
test "float-capital-exponent" (1.5E2 = 150.0)
test "float-trailing-dot" (100. = 100.0)
test "float-leading-dot-sum" (1.0 + 0.5 = 1.5)
test "float32-suffix" (float 1.5f = 1.5)
test "float-separator" (1_000.5 = 1000.5)

// the float literals a program leans on
test "float-zero" (0.0 = 0.0)
test "float-precision" (0.1 + 0.2 <> 0.3)
test "float-big" (1e300 * 10.0 = 1e301)

// ---- characters -----------------------------------------------------------

test "char-plain" ('a' = 'a')
test "char-order" ('a' < 'b')
test "char-of-int" (int 'A' = 65)
test "char-newline" (int '\n' = 10)
test "char-tab" (int '\t' = 9)
test "char-return" (int '\r' = 13)
test "char-backslash" (int '\\' = 92)
test "char-quote" (int '\'' = 39)
test "char-double-quote" (int '\"' = 34)
test "char-null" (int '\000' = 0)
test "char-unicode" (int 'A' = 65)
test "char-trigraph" (int '\065' = 65)

// ---- strings --------------------------------------------------------------

test "string-plain" ("abc".Length = 3)
test "string-escapes" ("a\nb".Length = 3)
test "string-backslash" ("a\\b".Length = 3)
test "string-quote" ("a\"b".Length = 3)
test "string-unicode-escape" ("A" = "A")
test "string-long-unicode" ("\U00000041" = "A")
test "string-empty" ("".Length = 0)
test "string-concat" ("ab" + "cd" = "abcd")

// a VERBATIM string keeps its backslashes
test "verbatim" (@"a\nb".Length = 4)
test "verbatim-quote" (@"a""b".Length = 3)

// a TRIPLE-QUOTED string keeps everything
test "triple-quoted" ("""a\nb""".Length = 4)
test "triple-quoted-quote" ("""a"b""".Length = 3)

// indexing and slicing a literal
test "string-index" ("abc".[1] = 'b')
test "string-substring" ("abcdef".Substring (1, 3) = "bcd")

// ---- bool and unit --------------------------------------------------------

test "bool-true" (true = true)
test "bool-false" (not false)
test "bool-and" (true && not false)
test "unit-value" (() = ())

let returnsUnit () = ()
test "unit-returned" (returnsUnit () = ())

// ---- literals inside containers and patterns ------------------------------

test "list-of-literals" ([ 1; 2; 3 ] = [ 1; 2; 3 ])
test "array-of-literals" (Array.toList [| 1uy; 2uy |] = [ 1uy; 2uy ])
test "tuple-of-literals" ((1, 'a', "s", true) = (1, 'a', "s", true))

let classify (v : int) =
    match v with
    | 0 -> "zero"
    | 0xFF -> "hex"
    | 1_000 -> "separated"
    | _ -> "other"

test "literal-pattern-zero" (classify 0 = "zero")
test "literal-pattern-hex" (classify 255 = "hex")
test "literal-pattern-separated" (classify 1000 = "separated")

let charCase (c : char) =
    match c with
    | '\n' -> "nl"
    | 'a' -> "a"
    | _ -> "?"

test "char-pattern" (charCase '\n' = "nl" && charCase 'a' = "a")

let stringCase (s : string) =
    match s with
    | "" -> "empty"
    | "a\tb" -> "escaped"
    | _ -> "?"

test "string-pattern" (stringCase "" = "empty" && stringCase "a\tb" = "escaped")

// ---- a [<Literal>] binding is a constant ---------------------------------

[<Literal>]
let Threshold = 10

[<Literal>]
let Greeting = "hi"

test "literal-binding" (Threshold * 2 = 20)
test "literal-binding-string" (Greeting + "!" = "hi!")

let usesLiteralPattern (v : int) =
    match v with
    | Threshold -> "at"
    | _ -> "off"

test "literal-in-pattern" (usesLiteralPattern 10 = "at" && usesLiteralPattern 9 = "off")

printfn "DONE tests=%d failures=%d" ntests failures
