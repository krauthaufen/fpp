// Ported from dotnet/fsharp tests/fsharp/core/forexpression/test.fsx into
// the common F#/F++ subset. Dropped: the Dictionary/IList variants (.NET
// interface surface), the `#seq` flexible-type plumbing in getTestData
// (each sum builds its own data directly), and the ColorF val-field struct
// regression (explicit-field constructor syntax); its zero-init point is
// covered by struct records elsewhere. The iteration SHAPES — array of
// arrays, seq of seqs, list of lists, ranges, `for i = a to b`, strings —
// are all kept.
module Core_forexpression

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

let count = 1000
let testString = "19740531"
let testData =
    [| for i in 0 .. count -> [| for inner in 0 .. i -> inner |] |]
let expectedArraySum = 167167000
let expectedRangeSum = ((count + 1) * count) / 2
let expectedStringSum = 30

// the sequence source is an array of arrays
let sumOverArray () =
    let mutable sum = 0
    for outer in testData do
        for inner in outer do
            sum <- sum + inner
    sum

// no optimization applies: the enumerator protocol over seqs
let sumOverSeq () =
    let data : seq<seq<int>> = Seq.ofArray (Array.map Seq.ofArray testData)
    let mutable sum = 0
    for outer in data do
        for inner in outer do
            sum <- sum + inner
    sum

// the source extends IList`1 in .NET terms: a ResizeArray
let sumOverResizeArray () =
    let data = ResizeArray<ResizeArray<int>> ()
    for xs in testData do
        let r = ResizeArray<int> ()
        for x in xs do r.Add x
        data.Add r
    let mutable sum = 0
    for outer in data do
        for inner in outer do
            sum <- sum + inner
    sum

// the source is a 'T list
let sumOverList () =
    let data : int list list = List.ofArray (Array.map List.ofArray testData)
    let mutable sum = 0
    for outer in data do
        for inner in outer do
            sum <- sum + inner
    sum

// the source is a range n..m
let sumOverRange () =
    let mutable sum = 0
    for i in 0 .. count do
        sum <- sum + i
    sum

// the classic counted loop
let sumOverCounted () =
    let mutable sum = 0
    for i = 0 to count do
        sum <- sum + i
    sum

// the source is a string
let sumOverString () =
    let mutable sum = 0
    for i in testString do
        sum <- sum + ((int i) - (int '0'))
    sum

let arraySum = sumOverArray ()
let seqSum = sumOverSeq ()
let resizeArraySum = sumOverResizeArray ()
let listSum = sumOverList ()
let rangeSum = sumOverRange ()
let countedSum = sumOverCounted ()
let stringSum = sumOverString ()

test "arraySum" (expectedArraySum = arraySum)
test "seqSum" (expectedArraySum = seqSum)
test "ResizeArraySum" (expectedArraySum = resizeArraySum)
test "listSum" (expectedArraySum = listSum)
test "rangeSum" (expectedRangeSum = rangeSum)
test "countedSum" (expectedRangeSum = countedSum)
test "stringSum" (expectedStringSum = stringSum)

printfn "DONE tests=%d failures=%d" ntests failures
