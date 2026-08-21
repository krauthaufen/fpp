// Ported from dotnet/fsharp tests/fsharp/core/libtest/test.fsx — the
// IntegerLoopsWithMinAndMaxIntAndKnownBounds and ...GoingDown modules — into
// the common F#/F++ subset. Test NAMES are the originals.
//
// The point of these is the loop EDGE: a `for` whose bound is Int32.MaxValue
// must run the last iteration without the counter's increment overflowing
// past it, and the same at MinValue going down.
//
// ADAPTED: `System.Int32.MinValue`/`MaxValue` are spelled as the literals
// (no System.Int32 surface); the empty-range checks compare lists, and an
// empty `[ lower .. upper ]` where upper < lower is the empty list in both.
module Core_intloops

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

let minInt = -2147483648
let maxInt = 2147483647

// ---- going up -----------------------------------------------------------

let x0 () =
    let r = ResizeArray<int>()
    for i = 0 to 10 do
        r.Add i
    test "clkevrw1" (List.ofSeq r = [ 0 .. 10 ])

let x1 () =
    let r = ResizeArray<int>()
    for i = minInt to minInt + 2 do
        r.Add i
    test "clkevrw2" (List.ofSeq r = [ minInt .. minInt + 2 ])

let x2 () =
    let r = ResizeArray<int>()
    for i = maxInt - 3 to maxInt - 1 do
        r.Add i
    test "clkevrw3" (List.ofSeq r = [ maxInt - 3 .. maxInt - 1 ])

let x3 () =
    let r = ResizeArray<int>()
    for i = maxInt - 3 to maxInt do
        r.Add i
    test "clkevrw4" (List.ofSeq r = [ maxInt - 3 .. maxInt ])

let x4 () =
    let r = ResizeArray<int>()
    for i = maxInt to maxInt do
        r.Add i
    test "clkevrw5" (List.ofSeq r = [ maxInt .. maxInt ])

let x5 () =
    let r = ResizeArray<int>()
    for i = minInt to minInt do
        r.Add i
    test "clkevrw6" (List.ofSeq r = [ minInt .. minInt ])

let x6 () =
    for lower in [ -5 .. 5 ] do
        for upper in [ -5 .. 5 ] do
            let r = ResizeArray<int>()
            for i = lower to upper do
                r.Add i
            test "clkevrw7" (List.ofSeq r = [ lower .. upper ])

// ---- going down ---------------------------------------------------------

let d0 () =
    let r = ResizeArray<int>()
    for i = 10 downto 0 do
        r.Add i
    test "clkevrw1-down" ((List.ofSeq r |> List.rev) = [ 0 .. 10 ])

let d1 () =
    let r = ResizeArray<int>()
    for i = minInt + 2 downto minInt do
        r.Add i
    test "clkevrw2-down" ((List.ofSeq r |> List.rev) = [ minInt .. minInt + 2 ])

let d2 () =
    let r = ResizeArray<int>()
    for i = maxInt - 1 downto maxInt - 3 do
        r.Add i
    test "clkevrw3-down" ((List.ofSeq r |> List.rev) = [ maxInt - 3 .. maxInt - 1 ])

let d3 () =
    let r = ResizeArray<int>()
    for i = maxInt downto maxInt - 3 do
        r.Add i
    test "clkevrw4-down" ((List.ofSeq r |> List.rev) = [ maxInt - 3 .. maxInt ])

let d4 () =
    let r = ResizeArray<int>()
    for i = maxInt downto maxInt do
        r.Add i
    test "clkevrw5-down" ((List.ofSeq r |> List.rev) = [ maxInt .. maxInt ])

let d5 () =
    let r = ResizeArray<int>()
    for i = minInt downto minInt do
        r.Add i
    test "clkevrw6-down" ((List.ofSeq r |> List.rev) = [ minInt .. minInt ])

let d6 () =
    for lower in [ -5 .. 5 ] do
        for upper in [ -5 .. 5 ] do
            let r = ResizeArray<int>()
            for i = upper downto lower do
                r.Add i
            test "clkevrw7-down" ((List.ofSeq r |> List.rev) = [ lower .. upper ])

let go =
    x0 ()
    x1 ()
    x2 ()
    x3 ()
    x4 ()
    x5 ()
    x6 ()
    d0 ()
    d1 ()
    d2 ()
    d3 ()
    d4 ()
    d5 ()
    d6 ()
    printfn "DONE tests=%d failures=%d" ntests failures
