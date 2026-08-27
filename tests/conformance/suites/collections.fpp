// THE MUTABLE .NET COLLECTIONS, ported from dotnet/fsharp's
// tests/fsharp/core/libtest (the ResizeArray and Dictionary cases) and the
// StringBuilder cases of tests/fsharp/core/printf.
//
// These three are the ones F# code reaches for when the immutable
// collections are the wrong shape, and until now nothing GATED them: the
// stdlib/dotnet.fpp exercise is run by hand. They are mutable, so what
// matters is the state after a sequence of operations — a count that tracks
// adds and removes, an indexer that reads back what was written, a key that
// overwrites rather than duplicates, and the ORDER a list preserves.
//
// DROPPED: `MutableHashSet`, which F# spells `HashSet` — the name diverges
// (the acceptance corpus ports a HashSet of its own, see DIVERGENCES.md) so
// the oracle cannot compile the same source. Also dropped: capacity and
// growth behaviour (an implementation detail), and the non-generic
// collections.
module Core_collections

open System.Collections.Generic
open System.Text

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

let joinInts (xs : int seq) : string =
    String.concat "," (Seq.toList (Seq.map (fun (v : int) -> string v) xs))

// ---- ResizeArray: a growable array that keeps insertion ORDER ---------------

let ra = ResizeArray<int> ()

eq "resizearray-starts-empty" (string ra.Count) "0"

ra.Add 1
ra.Add 2
ra.Add 3
eq "count-tracks-adds" (string ra.Count) "3"
eq "keeps-insertion-order" (joinInts ra) "1,2,3"

// the indexer reads and writes
eq "index-read" (string ra.[0]) "1"
eq "index-read-last" (string ra.[2]) "3"
ra.[1] <- 20
eq "index-write" (joinInts ra) "1,20,3"

// removal by VALUE takes the first match and shifts the rest down
let removed = ra.Remove 20
test "remove-reports-success" removed
eq "count-after-remove" (string ra.Count) "2"
eq "order-after-remove" (joinInts ra) "1,3"

let removedMissing = ra.Remove 99
test "remove-of-an-absent-value-fails" (not removedMissing)
eq "count-unchanged-after-failed-remove" (string ra.Count) "2"

// removal by INDEX
ra.Add 4
ra.Add 5
eq "before-removeat" (joinInts ra) "1,3,4,5"
ra.RemoveAt 1
eq "removeat-drops-that-position" (joinInts ra) "1,4,5"

// insertion at a position
ra.Insert (1, 9)
eq "insert-shifts-right" (joinInts ra) "1,9,4,5"
ra.Insert (0, 0)
eq "insert-at-the-front" (joinInts ra) "0,1,9,4,5"

// membership and search
test "contains-a-present-value" (ra.Contains 9)
test "does-not-contain-an-absent-value" (not (ra.Contains 99))
eq "indexof-finds-the-position" (string (ra.IndexOf 9)) "2"
eq "indexof-answers-minus-one-when-absent" (string (ra.IndexOf 99)) "-1"

// clearing
ra.Clear ()
eq "cleared-is-empty" (string ra.Count) "0"
eq "cleared-renders-empty" (joinInts ra) ""

// built by appending, and converted back.
// DROPPED: `ResizeArray<int> ([ 5; 6; 7 ])`. .NET has the collection-taking
// constructor and F++ does not — a secondary constructor here would need
// `new (xs) as x = ... then ...` to fill the instance after the primary one
// ran, and that form does not parse yet.
let ra2 = ResizeArray<int> ()
ra2.Add 5
ra2.Add 6
ra2.Add 7
eq "built-by-appending" (joinInts ra2) "5,6,7"
eq "to-array" (String.concat "," (List.map string (List.ofArray (ra2.ToArray ())))) "5,6,7"
eq "counted-through-seq" (string (Seq.length ra2)) "3"

// a ResizeArray of strings behaves the same
let rs = ResizeArray<string> ()
rs.Add "a"
rs.Add "b"
eq "strings-in-order" (String.concat "" (Seq.toList rs)) "ab"
test "strings-contains" (rs.Contains "a")

// iterated with `for`
let mutable sum = 0
for v in ra2 do sum <- sum + v
eq "iterated-with-for" (string sum) "18"

// nested: a list of lists
let outer = ResizeArray<ResizeArray<int>> ()
let inner1 = ResizeArray<int> ()
inner1.Add 1
outer.Add inner1
eq "nested-count" (string outer.Count) "1"
eq "nested-read" (string outer.[0].[0]) "1"
outer.[0].Add 2
eq "nested-write-is-shared" (joinInts inner1) "1,2"

// ---- Dictionary: keys map to values, and a key is UNIQUE --------------------

let d = Dictionary<string, int> ()

eq "dictionary-starts-empty" (string d.Count) "0"

d.["a"] <- 1
d.["b"] <- 2
eq "count-tracks-keys" (string d.Count) "2"
eq "indexer-reads-back" (string d.["a"]) "1"
eq "indexer-reads-the-other" (string d.["b"]) "2"

// writing an EXISTING key overwrites: it does not add
d.["a"] <- 10
eq "overwrite-does-not-grow" (string d.Count) "2"
eq "overwrite-changes-the-value" (string d.["a"]) "10"

// Add is the same for a fresh key
d.Add ("c", 3)
eq "add-a-fresh-key" (string d.Count) "3"
eq "added-value" (string d.["c"]) "3"

// membership
test "contains-a-present-key" (d.ContainsKey "a")
test "does-not-contain-an-absent-key" (not (d.ContainsKey "zz"))

// removal
let dRemoved = d.Remove "b"
test "remove-reports-success" dRemoved
eq "count-after-remove" (string d.Count) "2"
test "removed-key-is-gone" (not (d.ContainsKey "b"))
test "removing-an-absent-key-fails" (not (d.Remove "zz"))

// the keys and values, read as sets (ORDER is not promised, so sort)
let sortedKeys = List.sort (Seq.toList d.Keys)
eq "keys" (String.concat "," sortedKeys) "a,c"
let sortedValues = List.sort (Seq.toList d.Values)
eq "values" (String.concat "," (List.map string sortedValues)) "3,10"

// iterating yields pairs
let mutable total = 0
for kv in d do total <- total + kv.Value
eq "iterated-values-sum" (string total) "13"

let keyChars = List.sort (Seq.toList (Seq.map (fun (kv : KeyValuePair<string, int>) -> kv.Key) d))
eq "iterated-keys" (String.concat "," keyChars) "a,c"

// clearing
d.Clear ()
eq "dictionary-cleared" (string d.Count) "0"
test "cleared-contains-nothing" (not (d.ContainsKey "a"))

// INT keys, and a value that is itself a collection
let di = Dictionary<int, string> ()
di.[1] <- "one"
di.[2] <- "two"
eq "int-keyed-read" di.[1] "one"
eq "int-keyed-count" (string di.Count) "2"
di.[1] <- "ONE"
eq "int-keyed-overwrite" di.[1] "ONE"

// a dictionary used as a COUNTER, the shape libtest leans on
let counts = Dictionary<string, int> ()
let bump (k : string) : unit =
    if counts.ContainsKey k then counts.[k] <- counts.[k] + 1
    else counts.[k] <- 1

bump "x"
bump "y"
bump "x"
bump "x"
eq "counter-x" (string counts.["x"]) "3"
eq "counter-y" (string counts.["y"]) "1"
eq "counter-distinct-keys" (string counts.Count) "2"

// ---- StringBuilder: appends build one string --------------------------------

let sb = StringBuilder ()
eq "builder-starts-empty" (sb.ToString ()) ""

sb.Append "a" |> ignore
sb.Append "b" |> ignore
eq "appends-concatenate" (sb.ToString ()) "ab"
eq "length-tracks-appends" (string sb.Length) "2"

// Append takes more than strings
sb.Append 1 |> ignore
eq "append-an-int" (sb.ToString ()) "ab1"
sb.Append 'c' |> ignore
eq "append-a-char" (sb.ToString ()) "ab1c"

// AppendLine adds a newline, so read the length rather than the text
let sb2 = StringBuilder ()
sb2.AppendLine "x" |> ignore
test "appendline-is-longer-than-its-text" (sb2.Length > 1)
test "appendline-starts-with-its-text" ((sb2.ToString ()).StartsWith "x")

// the calls CHAIN, since each returns the builder
let sb3 = StringBuilder ()
sb3.Append("a").Append("b").Append("c") |> ignore
eq "chained-appends" (sb3.ToString ()) "abc"

// built in a loop, which is what a builder is for
let sb4 = StringBuilder ()
for i in 1 .. 5 do sb4.Append (string i) |> ignore
eq "built-in-a-loop" (sb4.ToString ()) "12345"
eq "loop-built-length" (string sb4.Length) "5"

// clearing it
sb4.Clear () |> ignore
eq "builder-cleared" (sb4.ToString ()) ""
eq "cleared-length" (string sb4.Length) "0"

// and it keeps working after the clear
sb4.Append "fresh" |> ignore
eq "usable-after-clear" (sb4.ToString ()) "fresh"

// ---- the three together -----------------------------------------------------

// group words by their first letter: a Dictionary of ResizeArrays, rendered
// through a StringBuilder
let groups = Dictionary<char, ResizeArray<string>> ()
let addWord (w : string) : unit =
    let k = w.[0]
    if not (groups.ContainsKey k) then groups.[k] <- ResizeArray<string> ()
    groups.[k].Add w

for w in [ "apple"; "ant"; "bee"; "cat"; "cow" ] do addWord w

eq "grouped-key-count" (string groups.Count) "3"
eq "group-a" (String.concat "," (Seq.toList groups.['a'])) "apple,ant"
eq "group-b" (String.concat "," (Seq.toList groups.['b'])) "bee"

let out = StringBuilder ()
for k in List.sort (Seq.toList groups.Keys) do
    out.Append(string k).Append(":").Append(string groups.[k].Count).Append(";") |> ignore
eq "rendered-groups" (out.ToString ()) "a:2;b:1;c:2;"

printfn "DONE tests=%d failures=%d" ntests failures
