// THE STRING MODULE and the string instance members, ported from dotnet/fsharp's
// tests/FSharp.Core.UnitTests/FSharp.Core/Microsoft.FSharp.Core/StringModule.fs
// and the string cases of Conformance/BasicGrammarElements.
//
// `strings` covers literals and escapes; this covers the OPERATIONS, where the
// interesting cases are the empty string and the edges: `String.concat` over
// nothing, a split that finds no separator, `Substring` taking the whole
// string, an index at the last character.
//
// DROPPED: culture-sensitive comparison and `String.Compare` overloads (there
// is one ordinal ordering here), and `sprintf`-based building, which the
// printf suites cover.
module Core_stringmod

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

// ---- length, indexing, slicing --------------------------------------------

let s = "hello"

test "length" (s.Length = 5)
test "length-empty" ("".Length = 0)
test "index-first" (s.[0] = 'h')
test "index-last" (s.[s.Length - 1] = 'o')
eq "substring-from" (s.Substring 3) "lo"
eq "substring-range" (s.Substring (1, 3)) "ell"
eq "substring-whole" (s.Substring (0, 5)) "hello"
eq "substring-empty" (s.Substring (2, 0)) ""

// ---- searching ------------------------------------------------------------

test "contains" (s.Contains "ell")
test "contains-empty-is-true" (s.Contains "")
test "not-contains" (not (s.Contains "xyz"))
test "startsWith" (s.StartsWith "he" && not (s.StartsWith "lo"))
test "endsWith" (s.EndsWith "lo" && not (s.EndsWith "he"))
test "indexOf" (s.IndexOf "l" = 2)
test "indexOf-missing" (s.IndexOf "z" = 0 - 1)
test "lastIndexOf" (s.LastIndexOf "l" = 3)

// ---- transformation --------------------------------------------------------

eq "toUpper" (s.ToUpper ()) "HELLO"
eq "toLower" ("HELLO".ToLower ()) "hello"
eq "trim" ("  pad  ".Trim ()) "pad"
eq "trim-nothing" ("pad".Trim ()) "pad"
eq "trim-all-space" ("   ".Trim ()) ""
eq "replace" (s.Replace ("l", "L")) "heLLo"
eq "replace-missing" (s.Replace ("z", "Z")) "hello"
eq "replace-longer" ("aa".Replace ("a", "bb")) "bbbb"
eq "concat-operator" ("ab" + "cd") "abcd"
eq "concat-empty" ("" + "ab") "ab"

// ---- the String module ------------------------------------------------------

eq "String.concat" (String.concat ", " [ "a"; "b"; "c" ]) "a, b, c"
eq "String.concat-single" (String.concat ", " [ "a" ]) "a"
eq "String.concat-empty-list" (String.concat ", " []) ""
eq "String.concat-empty-sep" (String.concat "" [ "a"; "b" ]) "ab"
eq "String.replicate" (String.replicate 3 "ab") "ababab"
eq "String.replicate-zero" (String.replicate 0 "ab") ""

test "String.length" (String.length "abc" = 3)
test "String.forall" (String.forall (fun c -> c >= 'a') "abc")
test "String.exists" (String.exists (fun c -> c = 'b') "abc")
test "String.exists-empty-is-false" (not (String.exists (fun c -> true) ""))
test "String.forall-empty-is-true" (String.forall (fun c -> false) "")

eq "String.map" (String.map (fun c -> if c = 'a' then 'A' else c) "abc") "Abc"
eq "String.filter" (String.filter (fun c -> c <> 'b') "abc") "ac"
eq "String.collect" (String.collect (fun c -> string c + "-") "ab") "a-b-"

let mutable seen = ""
String.iter (fun c -> seen <- seen + string c) "abc"
eq "String.iter" seen "abc"

// ---- splitting and joining --------------------------------------------------

let parts = "a,b,c".Split ','

test "split-count" (parts.Length = 3)
eq "split-first" parts.[0] "a"
eq "split-last" parts.[2] "c"
test "split-no-separator" (("abc".Split ',').Length = 1)
eq "split-rejoin" (String.concat "," (Array.toList ("a,b,c".Split ','))) "a,b,c"

// an empty field is kept
let empties = "a,,b".Split ','
test "split-keeps-empty" (empties.Length = 3)
eq "split-empty-field" empties.[1] ""

// ---- conversions -----------------------------------------------------------

eq "string-of-int" (string 42) "42"
eq "string-of-negative" (string (0 - 42)) "-42"
eq "string-of-bool" (string true) "True"
eq "string-of-char" (string 'x') "x"
test "int-of-string" (int "42" = 42)
test "float-of-string" (float "2.5" = 2.5)

// a string is a sequence of chars: `for c in s` walks it, and ToCharArray
// materialises it. The Seq MODULE over a string (`Seq.length "abc"`,
// `List.ofSeq "abc"`) is not supported — see
// tests/known-issues/string-as-seq.fpp
test "toCharArray" (Array.toList ("abc".ToCharArray ()) = [ 'a'; 'b'; 'c' ])

let walked =
    let mutable acc = ""
    for c in "abc" do
        acc <- acc + string c
    acc
eq "for-in-string" walked "abc"

// ---- comparison and equality ------------------------------------------------

test "eq-operator" ("abc" = "abc")
test "ne-operator" ("abc" <> "abd")
test "order" (compare "abc" "abd" < 0)
test "order-prefix-is-less" (compare "ab" "abc" < 0)
test "order-case" (compare "A" "a" < 0)
test "sort" (List.sort [ "b"; "a"; "c" ] = [ "a"; "b"; "c" ])
test "empty-is-least" (compare "" "a" < 0)
test "hash" (hash "abc" = hash "abc")
test "as-map-key" (Map.find "k" (Map.ofList [ ("k", 1) ]) = 1)

// ---- building in a loop -----------------------------------------------------

let built =
    let mutable acc = ""
    for i in 1 .. 4 do
        acc <- acc + string i
    acc

eq "built-in-loop" built "1234"
eq "folded" (List.fold (fun (a : string) (b : string) -> a + b) "" [ "x"; "y"; "z" ]) "xyz"

// ---- the overloads that take a SET or a whole string -----------------------
// `Split` and `Trim` each have more than the one-char form. .NET keeps empty
// entries when it splits, which is what makes the edges worth pinning: a
// separator at either end produces one.

eq "split-char-array" (String.concat "|" (Array.toList ("a b  c".Split [| ' ' |]))) "a|b||c"
eq "split-several-separators" (String.concat "|" (Array.toList ("a;b,c".Split [| ';'; ',' |]))) "a|b|c"
eq "split-string-separator" (String.concat "|" (Array.toList ("a::b::c".Split "::"))) "a|b|c"
eq "split-string-absent" (String.concat "|" (Array.toList ("nosep".Split "::"))) "nosep"
eq "split-keeps-leading-empty" (String.concat "|" (Array.toList (",a,".Split ','))) "|a|"
eq "split-char-still-works" (String.concat "|" (Array.toList ("a,b".Split ','))) "a|b"
eq "split-count-with-empties" (string ("a,,b".Split ',').Length) "3"

eq "trim-char-set" ("xxaxbxx".Trim [| 'x' |]) "axb"
eq "trim-all-trimmed" ("aaa".Trim [| 'a' |]) ""
eq "trim-several-chars" ("xy hi yx".Trim [| 'x'; 'y' |]) " hi "
eq "trim-unit-still-works" ("  pad  ".Trim ()) "pad"

eq "string-join" (System.String.Join (",", [| "a"; "b"; "c" |])) "a,b,c"
eq "string-join-empty-sep" (System.String.Join ("", [| "a"; "b" |])) "ab"
eq "string-join-single" (System.String.Join (",", [| "solo" |])) "solo"
// DROPPED: the bare `String.Join (sep, list)`, which F++ has and F# does not
// — there `String` is FSharp.Core's module, with no Join to find, so the
// oracle cannot compile it. The unit suite covers that spelling.

// a member on an INDEX of an overloaded call's result: the element type is
// only known once the call is resolved, and both have to settle together
let joined = "a b	c".Replace("	", " ").Split [| ' ' |]
eq "member-on-index-of-overloaded-result" (joined.[0].Trim ()) "a"
eq "member-on-index-count" (string joined.Length) "3"

printfn "DONE tests=%d failures=%d" ntests failures
