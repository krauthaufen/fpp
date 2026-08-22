// UNSIGNED ordering, everywhere it can be reached: directly, inside a
// container, through a generic function's constraint, and through a comparer
// passed as a value (which is what `List.sort` does).
//
// The values here all sit ABOVE the signed range of their type, which is the
// only place the two orders disagree — read as a signed word, `4000000000u`
// is negative, and every comparison that forgot the type answered backwards.
//
// Ported in spirit from dotnet/fsharp's Conformance/BasicGrammarElements
// (the unsigned literal cases) rather than one file: upstream's unsigned
// coverage is spread across the numeric-literal tests.
module Core_unsigned

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

let big32 = 4000000000u
let small32 = 2u
let big64 = 18446744073709551615UL
let small64 = 2UL

// ---- the operators -------------------------------------------------------

test "u32-gt" (big32 > small32)
test "u32-lt" (small32 < big32)
test "u32-ge" (big32 >= big32)
test "u64-gt" (big64 > small64)
test "u64-lt" (small64 < big64)

// ---- `compare`, as a call and inside a container -------------------------

test "u32-compare" (compare big32 small32 > 0)
test "u32-compare-rev" (compare small32 big32 < 0)
test "u32-compare-eq" (compare big32 big32 = 0)
test "u64-compare" (compare big64 small64 > 0)
test "u64-compare-rev" (compare small64 big64 < 0)

test "u32-in-tuple" (compare (1, big32) (1, small32) > 0)
test "u32-in-list" (compare [ big32 ] [ small32 ] > 0)
// an unsigned payload of a GENERIC union — the prelude's own option, and a
// user union of the same shape — compares unsigned too: the derived
// comparer types its payload binders, so the stamped copy knows the element
test "u32-in-option" (compare (Some big32) (Some small32) > 0)
test "u32-in-option-rev" (compare (Some small32) (Some big32) < 0)
test "u32-in-result" (compare (Ok big32 : Result<uint32, string>) (Ok small32) > 0)
test "u64-in-option" (compare (Some big64) (Some small64) > 0)
test "u64-in-tuple" (compare (1, big64) (1, small64) > 0)

// ---- through a generic function's constraint -----------------------------

// the comparison constraint is INFERRED, which is how both languages spell it
let maxOf a b = if a > b then a else b
let minOf a b = if a < b then a else b

test "u32-generic-max" (maxOf big32 small32 = big32)
test "u32-generic-min" (minOf big32 small32 = small32)
test "u64-generic-max" (maxOf big64 small64 = big64)
test "int-generic-max" (maxOf 5 2 = 5)
test "float-generic-max" (maxOf 2.5 1.5 = 2.5)

// the library's own max/min take the same route
test "u32-max" (max big32 small32 = big32)
test "u32-min" (min big32 small32 = small32)

// ---- through a comparer passed as a VALUE --------------------------------

test "u32-list-sort" (List.sort [ big32; small32 ] = [ small32; big32 ])
test "u32-array-sort" (Array.toList (Array.sort [| big32; small32 |]) = [ small32; big32 ])
test "u64-list-sort" (List.sort [ big64; small64 ] = [ small64; big64 ])
test "u32-seq-sort" (Seq.toList (Seq.sort (List.toSeq [ big32; small32 ])) = [ small32; big32 ])
test "u32-sort-by" (List.sortBy (fun (x : uint32) -> x) [ big32; small32 ] = [ small32; big32 ])
test "u32-list-max" (List.max [ small32; big32 ] = big32)
test "u32-list-min" (List.min [ small32; big32 ] = small32)

// ---- as keys in the ordered containers -----------------------------------

let s = Set.ofList [ big32; small32; 7u ]

test "u32-set-count" (Set.count s = 3)
test "u32-set-contains" (Set.contains big32 s && Set.contains small32 s)
test "u32-set-order" (Set.toList s = [ small32; 7u; big32 ])

let m = Map.ofList [ (big32, "big"); (small32, "small") ]

test "u32-map-lookup" (Map.find big32 m = "big" && Map.find small32 m = "small")
test "u32-map-order" (List.map fst (Map.toList m) = [ small32; big32 ])

// ---- the arithmetic that goes with them ----------------------------------

test "u32-div" (big32 / 2u = 2000000000u)
test "u32-rem" (big32 % 3u = 4000000000u % 3u)
test "u32-shr" (big32 >>> 1 = 2000000000u)
test "u64-div" (big64 / 2UL = 9223372036854775807UL)

printfn "DONE tests=%d failures=%d" ntests failures
