// UNICODE AND CHARACTER ESCAPES, ported from dotnet/fsharp's
// tests/fsharp/core/unicode and the LexicalAnalysis/StringsAndCharacters
// cases of the Conformance suite.
//
// A string here is UTF-16, so the questions that matter are where a
// character's ENCODING shows through: `Length` counts code UNITS, so an
// astral character is two of them; `\u` names one unit and `\U` names a code
// point that may need a surrogate pair; and a non-ASCII literal written
// directly in the source must equal the same text written as escapes.
//
// DROPPED: the file-encoding round trips (StreamWriter/out.bsl), codepage
// switches, and `System.Text.Encoding` — none of that surface exists here.
// `System.String (chars)` is dropped too: it is an unresolved name that
// SILENTLY DROPS its statement, recorded in tests/known-issues.
module Core_unicode

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// ---- escapes in a string literal -------------------------------------------

eq "escape-newline" (string "a\nb".Length) "3"
eq "escape-tab" (string "a\tb".Length) "3"
eq "escape-backslash" "a\\b" ("a" + string '\\' + "b")
eq "escape-quote" (string "a\"b".Length) "3"
eq "escape-return" (string "a\rb".Length) "3"
eq "escape-backspace" (string "a\bb".Length) "3"
eq "escape-formfeed" (string "a\fb".Length) "3"
eq "escape-nul-length" (string "a\000b".Length) "3"

// the same character, three spellings
eq "escape-unicode-short" "\u0041" "A"
eq "escape-hex" "\x41" "A"
eq "escape-trigraph" "\065" "A"
test "three-spellings-agree" ("A" = "\x41" && "\x41" = "\065")

// ---- non-ASCII, written directly and as escapes ----------------------------

// the copyright sign and the not-equals sign, from the original suite
eq "copyright-escape" "\u00a9" "©"
eq "not-equals-escape" "\u2260" "≠"
eq "copyright-length" (string "\u00a9".Length) "1"
eq "not-equals-length" (string "\u2260".Length) "1"

// a literal written directly in the source is the same string
let direct = "©≠"
let escaped = "\u00a9\u2260"
test "direct-equals-escaped" (direct = escaped)
eq "direct-length" (string direct.Length) "2"

// text in several scripts, counted in UTF-16 code units
eq "greek" (string "αβγ".Length) "3"
eq "cyrillic" (string "Привет".Length) "6"
eq "kanji" (string "日本語".Length) "3"
eq "hebrew" (string "שלום".Length) "4"

// concatenation and comparison do not care which side of the BMP it is on
eq "concat-non-ascii" ("日本" + "語") "日本語"
test "compare-non-ascii-equal" ("日本語" = "日本" + "語")
test "compare-non-ascii-differ" ("日本語" <> "日本")

// ---- code units versus code points -----------------------------------------

// an ASTRAL character is ONE code point and TWO UTF-16 code units, so
// `Length` reports two — the same answer .NET gives
let astral = "\U0001F600"
eq "astral-length" (string astral.Length) "2"
eq "astral-as-surrogate-pair" astral "\uD83D\uDE00"
test "astral-first-is-high-surrogate" (astral.[0] = '\uD83D')
test "astral-second-is-low-surrogate" (astral.[1] = '\uDE00')

// a string mixing ASCII and an astral character
let mixed = "a\U0001F600b"
eq "mixed-length" (string mixed.Length) "4"
test "mixed-first" (mixed.[0] = 'a')
test "mixed-last" (mixed.[3] = 'b')

// ---- indexing and slicing non-ASCII ----------------------------------------

let jp = "日本語"
test "index-first" (jp.[0] = '日')
test "index-last" (jp.[2] = '語')
eq "slice-non-ascii" jp.[0..1] "日本"
eq "substring-non-ascii" (jp.Substring 1) "本語"
eq "substring-non-ascii-two" (jp.Substring (1, 1)) "本"

// the String module works the same
eq "concat-module" (String.concat "-" [ "α"; "β" ]) "α-β"
eq "replace-non-ascii" (jp.Replace ("本", "X")) "日X語"
test "contains-non-ascii" (jp.Contains "本")
test "startswith-non-ascii" (jp.StartsWith "日")
test "endswith-non-ascii" (jp.EndsWith "語")
eq "indexof-non-ascii" (string (jp.IndexOf "語")) "2"

// reversing counts code units, so it is defined on the BMP text
let reversed = Array.rev (jp.ToCharArray ())
eq "chars-of-non-ascii"
   (String.concat "" (Array.toList (Array.map (fun (c : char) -> string c) reversed)))
   "語本日"

// ---- character literals ----------------------------------------------------

let copy = '\u00a9'
let ne = '\u2260'
let ni = '日'

test "char-escape-equals-direct" (copy = '©')
eq "char-to-string" (string ne) "≠"
eq "char-in-a-string" (string ni + "本") "日本"
eq "char-code" (string (int copy)) "169"
eq "char-code-not-equals" (string (int ne)) "8800"
eq "char-code-kanji" (string (int ni)) "26085"
test "char-of-code" (char 169 = '\u00a9')

// the ordinary escapes as CHARACTERS
eq "char-newline-code" (string (int '\n')) "10"
eq "char-tab-code" (string (int '\t')) "9"
eq "char-quote-code" (string (int '\'')) "39"
eq "char-backslash-code" (string (int '\\')) "92"
eq "char-hex" (string (int '\x41')) "65"

// ---- non-ASCII in every position -------------------------------------------

// as a key, in a list, through a lambda, and printed
let words = [ "日本"; "語"; "©" ]
eq "list-of-non-ascii" (String.concat "" words) "日本語©"
eq "mapped-non-ascii" (String.concat "" (List.map (fun (w : string) -> w + "!") words)) "日本!語!©!"
eq "sorted-by-length" (String.concat "," (List.sortBy (fun (w : string) -> w.Length) words)) "語,©,日本"

// interpolated and formatted
let name = "世界"
eq "interpolated" $"hello {name}" "hello 世界"
eq "printf-string" (sprintf "[%s]" name) "[世界]"
eq "printf-char" (sprintf "%c" ni) "日"

// a non-ASCII identifier, which F# allows
let ``日本語の値`` = 42
eq "non-ascii-identifier" (string ``日本語の値``) "42"

// ---- the empty and the whitespace cases -------------------------------------

eq "empty-string" (string "".Length) "0"
eq "only-escapes" (string "\n\t\r".Length) "3"
eq "trim-around-non-ascii" ("  日本  ".Trim ()) "日本"
eq "pad-non-ascii" ("日".PadLeft 3) "  日"

printfn "DONE tests=%d failures=%d" ntests failures
