// CHARS, ported from dotnet/fsharp's
// tests/FSharp.Core.UnitTests/FSharp.Core/Microsoft.FSharp.Core (CharModule)
// and the char cases of Conformance/BasicGrammarElements.
//
// A char is a UTF-16 unit that ORDERS and CONVERTS like a number: `'a' < 'b'`
// is the code-point order, `int 'A'` is 65, and the classification predicates
// are decided by the code point rather than by the alphabet a reader has in
// mind — `Char.IsLetter '9'` is false, `Char.IsDigit 'â'` is false.
//
// DROPPED: the Unicode-category predicates beyond letter/digit/whitespace
// (IsSurrogate, IsSymbol, IsPunctuation), which need the full table.
module Core_charmod

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

// ---- ordering and equality -------------------------------------------------

test "eq" ('a' = 'a')
test "ne" ('a' <> 'b')
test "lt" ('a' < 'b')
test "digits-order" ('0' < '9')
test "upper-before-lower" ('Z' < 'a')
test "compare" (compare 'a' 'b' < 0 && compare 'b' 'a' > 0 && compare 'a' 'a' = 0)
test "min-max" (min 'a' 'b' = 'a' && max 'a' 'b' = 'b')
test "sort" (List.sort [ 'c'; 'a'; 'b' ] = [ 'a'; 'b'; 'c' ])
test "hash" (hash 'a' = hash 'a')

// ---- conversions -----------------------------------------------------------

test "int-of-char" (int 'A' = 65 && int 'a' = 97 && int '0' = 48)
test "char-of-int" (char 65 = 'A' && char 97 = 'a')
test "roundtrip" (char (int 'x') = 'x')
eq "string-of-char" (string 'x') "x"
test "char-arithmetic-via-int" (char (int 'a' + 1) = 'b')
test "distance" (int 'z' - int 'a' = 25)

// a digit's VALUE is its distance from '0'
test "digit-value" (int '7' - int '0' = 7)

// ---- classification --------------------------------------------------------

test "IsDigit" (System.Char.IsDigit '5' && not (System.Char.IsDigit 'a'))
test "IsDigit-space" (not (System.Char.IsDigit ' '))
test "IsLetter" (System.Char.IsLetter 'a' && System.Char.IsLetter 'Z')
test "IsLetter-digit-is-false" (not (System.Char.IsLetter '9'))
test "IsWhiteSpace" (System.Char.IsWhiteSpace ' ' && System.Char.IsWhiteSpace '\t')
test "IsWhiteSpace-newline" (System.Char.IsWhiteSpace '\n')
test "IsWhiteSpace-letter-is-false" (not (System.Char.IsWhiteSpace 'a'))
test "IsUpper" (System.Char.IsUpper 'A' && not (System.Char.IsUpper 'a'))
test "IsLower" (System.Char.IsLower 'a' && not (System.Char.IsLower 'A'))
test "IsLetterOrDigit" (System.Char.IsLetterOrDigit 'a' && System.Char.IsLetterOrDigit '9')
test "IsLetterOrDigit-space-is-false" (not (System.Char.IsLetterOrDigit ' '))

// ---- case mapping -----------------------------------------------------------

test "ToUpper" (System.Char.ToUpper 'a' = 'A')
test "ToLower" (System.Char.ToLower 'A' = 'a')
test "ToUpper-of-upper" (System.Char.ToUpper 'A' = 'A')
test "ToUpper-of-digit" (System.Char.ToUpper '9' = '9')
test "case-roundtrip" (System.Char.ToLower (System.Char.ToUpper 'q') = 'q')

// ---- chars in patterns, containers and strings ------------------------------

let kind (c : char) : string =
    match c with
    | '0' -> "zero"
    | 'a' | 'e' | 'i' | 'o' | 'u' -> "vowel"
    | c when System.Char.IsDigit c -> "digit"
    | _ -> "other"

test "match-literal" (kind '0' = "zero")
test "match-or-pattern" (kind 'e' = "vowel")
test "match-guard" (kind '7' = "digit")
test "match-fallthrough" (kind 'z' = "other")

test "in-list" (List.contains 'b' [ 'a'; 'b' ])
test "list-of-chars" (List.length [ 'a'; 'b'; 'c' ] = 3)
test "array-of-chars" (([| 'a'; 'b' |]).Length = 2)
test "array-index" (([| 'a'; 'b' |]).[1] = 'b')
test "in-string" ("abc".[1] = 'b')
test "string-contains-char" ("abc".Contains 'b')

// building a string from chars, and taking it apart again
let assembled =
    let mutable acc = ""
    for c in [ 'a'; 'b'; 'c' ] do
        acc <- acc + string c
    acc

eq "assembled" assembled "abc"
test "toCharArray-roundtrip" (Array.toList ("abc".ToCharArray ()) = [ 'a'; 'b'; 'c' ])

// counting with a predicate over a string's units
let vowels =
    let mutable n = 0
    for c in "sequoia".ToCharArray () do
        if c = 'a' || c = 'e' || c = 'i' || c = 'o' || c = 'u' then n <- n + 1
    n

test "counted-vowels" (vowels = 5)

// ---- escapes carry their code points ----------------------------------------

test "newline" (int '\n' = 10)
test "tab" (int '\t' = 9)
test "return" (int '\r' = 13)
test "backslash" (int '\\' = 92)
test "quote" (int '\'' = 39)
test "null" (int '\000' = 0)
test "trigraph" (int '\065' = 65)

printfn "DONE tests=%d failures=%d" ntests failures
