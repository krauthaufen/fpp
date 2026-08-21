// String and char semantics in the common F#/F++ subset, in the shape of
// dotnet/fsharp tests/fsharp/core/unicode (which pins source encodings) and
// the string parts of libtest.
//
// DROPPED: `String.sub`, `String.toList`/`ofList` (F++ extras, not F#), and
// `Seq.toList "abc"` — a string is seq<char> in F# but not here, so the
// char-sequence view is spelled as a comprehension, which both accept.
//
// ADAPTED: every non-ASCII character is written as a \u / \U ESCAPE. The
// fpp CLI reads source as BYTES (Latin-1 — the byte domain the self-host
// fixpoint compares in), so a literal UTF-8 character in source is its bytes,
// where fsc reads UTF-8 and gets one char. The escapes mean the same thing to
// both, and they are what this suite is really about.
//
// The point is the UTF-16 view .NET has: `String.length` counts CODE UNITS,
// so an astral character counts TWO, and `\U0001F600` is a surrogate pair.
module Core_strings

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- literals and length ------------------------------------------------

test "ascii-length" (String.length "abc" = 3)
test "empty-length" (String.length "" = 0)
test "latin1-length" (String.length "\u00e9" = 1)
test "kanji-length" (String.length "\u6f22" = 1)
test "kanji-word" (String.length "\u6f22\u5b57" = 2)
test "mixed-length" (String.length "a\u6f22b" = 3)
// astral: one CODE POINT, two UTF-16 code units
test "astral-length" (String.length "\U0001F600" = 2)
test "astral-pair" (String.length "\U0001F600\U0001F600" = 4)

// ---- escapes ------------------------------------------------------------

test "esc-newline" (String.length "a\nb" = 3)
test "esc-tab" (String.length "a\tb" = 3)
test "esc-backslash" (String.length "a\\b" = 3)
test "esc-quote" (String.length "a\"b" = 3)
test "esc-u" ("\u00e9" = "\u00E9")
test "esc-u-kanji" ("\u6f22" = "\u6F22")
test "esc-U-astral" (String.length "\U0001F600" = 2)
test "esc-U-eq" ("\U0001F600" = "\uD83D\uDE00")
test "esc-mixed" ("\u0061\u0062\u0063" = "abc")

// ---- indexing and slicing ----------------------------------------------

test "index-0" ("abc".[0] = 'a')
test "index-2" ("abc".[2] = 'c')
test "index-kanji" ("\u6f22".[0] = '\u6f22')
test "substring" ("hello".Substring (1, 3) = "ell")
test "substring-tail" ("hello".Substring 2 = "llo")
test "length-member" ("hello".Length = 5)

// ---- comparison ---------------------------------------------------------

test "eq" ("abc" = "abc")
test "neq" ("abc" <> "abd")
test "lt" (compare "abc" "abd" < 0)
test "gt" (compare "b" "a" > 0)
test "eq-empty" (compare "" "" = 0)
test "prefix-lt" (compare "ab" "abc" < 0)
test "ordinal" (compare "Z" "a" < 0)
test "kanji-cmp" (compare "\u6f22" "\u6f20" > 0)

// ---- building -----------------------------------------------------------

test "concat-op" ("ab" + "cd" = "abcd")
test "concat-empty" ("" + "x" = "x")
test "String.concat" (String.concat ", " [ "a"; "b"; "c" ] = "a, b, c")
test "String.concat-empty" (String.concat "," ([] : string list) = "")
test "String.replicate" (String.replicate 3 "ab" = "ababab")
test "String.init" (String.init 3 (fun i -> string i) = "012")
test "String.collect" (String.collect (fun c -> string c + "-") "ab" = "a-b-")
test "String.map" (String.map (fun c -> System.Char.ToUpper c) "abc" = "ABC")
test "String.filter" (String.filter (fun c -> System.Char.IsDigit c) "a1b2" = "12")
test "String.exists" (String.exists (fun c -> c = 'b') "abc")
test "String.forall" (String.forall (fun c -> System.Char.IsLetter c) "abc")
test "chars-toList" ([ for c in "abc" -> c ] = [ 'a'; 'b'; 'c' ])
test "chars-ofList" (String.concat "" [ for c in [ 'a'; 'b' ] -> string c ] = "ab")

// ---- chars --------------------------------------------------------------

test "char-lit" ('a' < 'b')
test "char-esc" ('\n' = char 10)
test "char-int" (int 'A' = 65)
test "char-of-int" (char 65 = 'A')
test "char-kanji-int" (int '\u6f22' = 28450)
test "System.Char.IsDigit" (System.Char.IsDigit '7' && not (System.Char.IsDigit 'x'))
test "System.Char.IsLetter" (System.Char.IsLetter 'x' && not (System.Char.IsLetter '7'))
test "System.Char.IsWhiteSpace" (System.Char.IsWhiteSpace ' ' && not (System.Char.IsWhiteSpace 'x'))
test "System.Char.IsUpper" (System.Char.IsUpper 'X' && not (System.Char.IsUpper 'x'))
test "System.Char.ToUpper" (System.Char.ToUpper 'x' = 'X')
test "System.Char.ToLower" (System.Char.ToLower 'X' = 'x')

// ---- string of things ---------------------------------------------------

test "string-int" (string 42 = "42")
test "string-neg" (string (0 - 7) = "-7")
test "string-bool" (string true = "True")
test "string-char" (string 'a' = "a")
test "sprintf-s" (sprintf "%s!" "hi" = "hi!")
test "sprintf-d" (sprintf "%d" 42 = "42")
test "sprintf-unicode" (sprintf "%s" "\u6f22" = "\u6f22")

printfn "DONE tests=%d failures=%d" ntests failures
