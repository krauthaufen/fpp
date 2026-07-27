module Fpp.Prelude

// The other half of the bootstrap seam. `src/Fpp.Compiler/Prelude.fs` routes
// every runtime touchpoint of the compiler through this surface so that .NET
// hosts it while dotnet builds the compiler; THIS file is the same surface in
// F++, for when the compiler compiles itself. The two must agree on
// semantics, not on implementation: .NET uses its own List/Dictionary, we
// use arrays and an open-addressed table.

let strLen (s : string) : int = s.Length
let charAt (s : string) (i : int) : char = s.[i]
let substr (s : string) (start : int) (len : int) : string = String.sub s start len

let isDigit (c : char) : bool = c >= '0' && c <= '9'
let isHexDigit (c : char) : bool = isDigit c || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')
let isAsciiLetter (c : char) : bool = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

/// A string is a byte array, so everything outside ASCII is a UTF-8
/// continuation or lead byte — all of which belong to identifiers, which is
/// the only question the lexer asks of this predicate.
let isLetter (c : char) : bool = isAsciiLetter c || int c >= 128

let stringOfChars (cs : char list) : string =
    let mutable acc = ""
    for c in cs do
        acc <- acc + string c
    acc

// ---- Vec: a growable vector ------------------------------------------

type Vec<'a> = { mutable Items : 'a[]; mutable Count : int }

let vecNew<'a> () : Vec<'a> = { Items = Array.zeroCreate 8; Count = 0 }
let vecLen (v : Vec<'a>) : int = v.Count
let vecGet (v : Vec<'a>) (i : int) : 'a = v.Items.[i]
let vecSet (v : Vec<'a>) (i : int) (x : 'a) : unit = v.Items.[i] <- x

let private vecGrow (v : Vec<'a>) (needed : int) : unit =
    if needed > v.Items.Length then
        let mutable cap = v.Items.Length * 2
        while cap < needed do
            cap <- cap * 2
        let bigger : 'a[] = Array.zeroCreate cap
        let mutable i = 0
        while i < v.Count do
            bigger.[i] <- v.Items.[i]
            i <- i + 1
        v.Items <- bigger

let vecAdd (v : Vec<'a>) (x : 'a) : unit =
    vecGrow v (v.Count + 1)
    v.Items.[v.Count] <- x
    v.Count <- v.Count + 1

let vecInsert (v : Vec<'a>) (i : int) (x : 'a) : unit =
    vecGrow v (v.Count + 1)
    let mutable j = v.Count
    while j > i do
        v.Items.[j] <- v.Items.[j - 1]
        j <- j - 1
    v.Items.[i] <- x
    v.Count <- v.Count + 1

let vecToList (v : Vec<'a>) : 'a list =
    let mutable acc = []
    let mutable i = v.Count - 1
    while i >= 0 do
        acc <- v.Items.[i] :: acc
        i <- i - 1
    acc

let vecOfList (xs : 'a list) : Vec<'a> =
    let v = vecNew<'a> ()
    for x in xs do
        vecAdd v x
    v

// ---- Dict: a mutable hash map ----------------------------------------

// Entries live in insertion order in `Keys`/`Vals`; `Slots` is the open-
// addressed index over them, holding entry index + 1 (0 = empty). Insertion
// order is what makes `dictPairs` deterministic, which the emitter's output
// depends on.
type Dict<'k, 'v> =
    { mutable Keys : 'k[]
      mutable Vals : 'v[]
      mutable Slots : int[]
      mutable Count : int }

let dictNew<'k, 'v> () : Dict<'k, 'v> =
    { Keys = Array.zeroCreate 8; Vals = Array.zeroCreate 8
      Slots = Array.zeroCreate 16; Count = 0 }

let private dictSlot (d : Dict<'k, 'v>) (k : 'k) : int =
    // linear probing; the table is never full, so this terminates
    let mask = d.Slots.Length - 1
    let mutable i = (hash k &&& 1073741823) &&& mask
    let mutable found = -1
    while found < 0 do
        let e = d.Slots.[i]
        if e = 0 then found <- i
        elif d.Keys.[e - 1] = k then found <- i
        else i <- (i + 1) &&& mask
    found

let private dictRehash (d : Dict<'k, 'v>) : unit =
    let slots : int[] = Array.zeroCreate (d.Slots.Length * 2)
    let mask = slots.Length - 1
    let mutable e = 0
    while e < d.Count do
        let mutable i = (hash d.Keys.[e] &&& 1073741823) &&& mask
        while slots.[i] <> 0 do
            i <- (i + 1) &&& mask
        slots.[i] <- e + 1
        e <- e + 1
    d.Slots <- slots

let dictSet (d : Dict<'k, 'v>) (k : 'k) (v : 'v) : unit =
    let s = dictSlot d k
    let e = d.Slots.[s]
    if e > 0 then d.Vals.[e - 1] <- v
    else
        if d.Count >= d.Keys.Length then
            let keys : 'k[] = Array.zeroCreate (d.Keys.Length * 2)
            let vals : 'v[] = Array.zeroCreate (d.Vals.Length * 2)
            let mutable i = 0
            while i < d.Count do
                keys.[i] <- d.Keys.[i]
                vals.[i] <- d.Vals.[i]
                i <- i + 1
            d.Keys <- keys
            d.Vals <- vals
        d.Keys.[d.Count] <- k
        d.Vals.[d.Count] <- v
        d.Count <- d.Count + 1
        // keep the load factor under a half: probes stay short and the
        // "never full" invariant `dictSlot` relies on holds
        if d.Count * 2 >= d.Slots.Length then dictRehash d
        else d.Slots.[s] <- d.Count

let dictTryFind (d : Dict<'k, 'v>) (k : 'k) : 'v option =
    let e = d.Slots.[dictSlot d k]
    if e > 0 then Some d.Vals.[e - 1] else None

let dictPairs (d : Dict<'k, 'v>) : ('k * 'v) list =
    let mutable acc = []
    let mutable i = d.Count - 1
    while i >= 0 do
        acc <- (d.Keys.[i], d.Vals.[i]) :: acc
        i <- i - 1
    acc
