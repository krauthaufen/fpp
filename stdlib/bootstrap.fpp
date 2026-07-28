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

/// Pairwise merge, not a left fold — `acc + string c` copies the whole
/// accumulator per character, which is quadratic in the result.
let stringOfChars (cs : char list) : string =
    let mutable cur : string list = []
    let mutable n = 0
    for c in cs do
        cur <- string c :: cur
        n <- n + 1
    let mutable reversed = true
    while n > 1 do
        let mutable out : string list = []
        let mutable rest = cur
        let mutable more = true
        while more do
            match rest with
            | x :: y :: tail ->
                out <- (if reversed then y + x else x + y) :: out
                rest <- tail
            | [ x ] ->
                out <- x :: out
                rest <- []
                more <- false
            | [] -> more <- false
        cur <- out
        reversed <- not reversed
        n <- (n + 1) / 2
    match cur with
    | [ one ] -> one
    | _ -> ""

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

let vecClear (v : Vec<'a>) : unit = v.Count <- 0

let vecToArray (v : Vec<'a>) : 'a[] =
    let a : 'a[] = Array.zeroCreate v.Count
    let mutable i = 0
    while i < v.Count do
        a.[i] <- v.Items.[i]
        i <- i + 1
    a

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
      /// each entry's hash, kept beside it. A probe that lands on the wrong
      /// entry is rejected on one int compare instead of a STRUCTURAL one:
      /// the compiler's keys are mostly (path, offset) pairs, so the old
      /// probe walked a string char by char to reject a collision. This is
      /// what .NET's Dictionary does, and it was most of the gap between the
      /// two halves on lookups.
      mutable Hashes : int[]
      mutable Slots : int[]
      mutable Count : int }

let dictNew<'k, 'v> () : Dict<'k, 'v> =
    { Keys = Array.zeroCreate 8; Vals = Array.zeroCreate 8
      Hashes = Array.zeroCreate 8
      Slots = Array.zeroCreate 16; Count = 0 }

let private dictSlotH (d : Dict<'k, 'v>) (k : 'k) (h : int) : int =
    // linear probing; the table is never full, so this terminates
    let mask = d.Slots.Length - 1
    let mutable i = h &&& mask
    let mutable found = -1
    while found < 0 do
        let e = d.Slots.[i]
        if e = 0 then found <- i
        elif d.Hashes.[e - 1] = h && d.Keys.[e - 1] = k then found <- i
        else i <- (i + 1) &&& mask
    found

let private dictSlot (d : Dict<'k, 'v>) (k : 'k) : int =
    dictSlotH d k (hash k &&& 1073741823)

let private dictRehash (d : Dict<'k, 'v>) : unit =
    let slots : int[] = Array.zeroCreate (d.Slots.Length * 2)
    let mask = slots.Length - 1
    let mutable e = 0
    while e < d.Count do
        // the stored hash: rehashing must not recompute what it already has
        let mutable i = d.Hashes.[e] &&& mask
        while slots.[i] <> 0 do
            i <- (i + 1) &&& mask
        slots.[i] <- e + 1
        e <- e + 1
    d.Slots <- slots

let dictSet (d : Dict<'k, 'v>) (k : 'k) (v : 'v) : unit =
    let h = hash k &&& 1073741823
    let s = dictSlotH d k h
    let e = d.Slots.[s]
    if e > 0 then d.Vals.[e - 1] <- v
    else
        if d.Count >= d.Keys.Length then
            let keys : 'k[] = Array.zeroCreate (d.Keys.Length * 2)
            let vals : 'v[] = Array.zeroCreate (d.Vals.Length * 2)
            let hs : int[] = Array.zeroCreate (d.Keys.Length * 2)
            let mutable i = 0
            while i < d.Count do
                keys.[i] <- d.Keys.[i]
                vals.[i] <- d.Vals.[i]
                hs.[i] <- d.Hashes.[i]
                i <- i + 1
            d.Keys <- keys
            d.Vals <- vals
            d.Hashes <- hs
        d.Keys.[d.Count] <- k
        d.Vals.[d.Count] <- v
        d.Hashes.[d.Count] <- h
        d.Count <- d.Count + 1
        // keep the load factor under a half: probes stay short and the
        // "never full" invariant `dictSlot` relies on holds
        if d.Count * 2 >= d.Slots.Length then dictRehash d
        else d.Slots.[s] <- d.Count

let dictTryFind (d : Dict<'k, 'v>) (k : 'k) : 'v option =
    let e = d.Slots.[dictSlot d k]
    if e > 0 then Some d.Vals.[e - 1] else None

/// Removing keeps the entries INSERTION-ORDERED — the survivors shift down
/// and the whole index is rebuilt. A tombstone would be cheaper, but
/// `dictSlot` probes until it finds an empty slot, and `dictPairs` order is
/// what makes the emitter's output reproducible.
let dictRemove (d : Dict<'k, 'v>) (k : 'k) : unit =
    let e = d.Slots.[dictSlot d k]
    if e > 0 then
        let mutable i = e - 1
        while i < d.Count - 1 do
            d.Keys.[i] <- d.Keys.[i + 1]
            d.Vals.[i] <- d.Vals.[i + 1]
            d.Hashes.[i] <- d.Hashes.[i + 1]
            i <- i + 1
        d.Count <- d.Count - 1
        let slots : int[] = Array.zeroCreate d.Slots.Length
        let mask = slots.Length - 1
        let mutable j = 0
        while j < d.Count do
            let mutable p = d.Hashes.[j] &&& mask
            while slots.[p] <> 0 do
                p <- (p + 1) &&& mask
            slots.[p] <- j + 1
            j <- j + 1
        d.Slots <- slots

let dictPairs (d : Dict<'k, 'v>) : ('k * 'v) list =
    let mutable acc = []
    let mutable i = d.Count - 1
    while i >= 0 do
        acc <- (d.Keys.[i], d.Vals.[i]) :: acc
        i <- i - 1
    acc

// ---- reference-identity collections ----------------------------------

// The .NET half builds these over `Object.ReferenceEquals`; here the
// identity test is the `refEq` primitive. The hash is the CALLER's, and it
// must read only immutable fields: unification rewrites `Link` while a
// visited set is live, and a hash that moved would strand its entry in the
// wrong bucket. Any hash consistent with identity is legal, so a shallow
// one — a constructor tag, a variable's id — is enough, which is what lets
// this work without an identity-hash primitive at all.

/// Open-addressed over insertion-ordered entries, exactly like `Dict`; only
/// the equality differs.
type RefSet<'a> =
    { mutable RefKeys : 'a[]
      mutable RefSlots : int[]
      mutable RefCount : int
      RefHash : 'a -> int }

let refSetNew (h : 'a -> int) : RefSet<'a> =
    { RefKeys = Array.zeroCreate 8; RefSlots = Array.zeroCreate 16; RefCount = 0; RefHash = h }

let private refSetSlot (s : RefSet<'a>) (x : 'a) : int =
    let mask = s.RefSlots.Length - 1
    let mutable i = (s.RefHash x &&& 1073741823) &&& mask
    let mutable found = -1
    while found < 0 do
        let e = s.RefSlots.[i]
        if e = 0 then found <- i
        elif refEq s.RefKeys.[e - 1] x then found <- i
        else i <- (i + 1) &&& mask
    found

let private refSetRehash (s : RefSet<'a>) : unit =
    let slots : int[] = Array.zeroCreate (s.RefSlots.Length * 2)
    let mask = slots.Length - 1
    let mutable e = 0
    while e < s.RefCount do
        let mutable i = (s.RefHash s.RefKeys.[e] &&& 1073741823) &&& mask
        while slots.[i] <> 0 do
            i <- (i + 1) &&& mask
        slots.[i] <- e + 1
        e <- e + 1
    s.RefSlots <- slots

let refSetContains (s : RefSet<'a>) (x : 'a) : bool = s.RefSlots.[refSetSlot s x] > 0

/// Add, reporting whether the value was NEW.
let refSetAdd (s : RefSet<'a>) (x : 'a) : bool =
    let at = refSetSlot s x
    if s.RefSlots.[at] > 0 then false
    else
        if s.RefCount >= s.RefKeys.Length then
            let keys : 'a[] = Array.zeroCreate (s.RefKeys.Length * 2)
            let mutable i = 0
            while i < s.RefCount do
                keys.[i] <- s.RefKeys.[i]
                i <- i + 1
            s.RefKeys <- keys
        s.RefKeys.[s.RefCount] <- x
        s.RefCount <- s.RefCount + 1
        if s.RefCount * 2 >= s.RefSlots.Length then refSetRehash s
        else s.RefSlots.[at] <- s.RefCount
        true

/// A set of PAIRS compared componentwise by identity.
type RefPair<'a> = { PairFst : 'a; PairSnd : 'a }

type RefPairSet<'a> =
    { mutable PairFsts : 'a[]
      mutable PairSnds : 'a[]
      mutable PairSlots : int[]
      mutable PairCount : int
      PairHash : 'a -> int }

let refPairSetNew (h : 'a -> int) : RefPairSet<'a> =
    { PairFsts = Array.zeroCreate 8; PairSnds = Array.zeroCreate 8
      PairSlots = Array.zeroCreate 16; PairCount = 0; PairHash = h }

let private refPairSlot (s : RefPairSet<'a>) (a : 'a) (b : 'a) : int =
    let mask = s.PairSlots.Length - 1
    let mutable i = ((s.PairHash a * 397 ^^^ s.PairHash b) &&& 1073741823) &&& mask
    let mutable found = -1
    while found < 0 do
        let e = s.PairSlots.[i]
        if e = 0 then found <- i
        elif refEq s.PairFsts.[e - 1] a && refEq s.PairSnds.[e - 1] b then found <- i
        else i <- (i + 1) &&& mask
    found

let private refPairRehash (s : RefPairSet<'a>) : unit =
    let slots : int[] = Array.zeroCreate (s.PairSlots.Length * 2)
    let mask = slots.Length - 1
    let mutable e = 0
    while e < s.PairCount do
        let h = s.PairHash s.PairFsts.[e] * 397 ^^^ s.PairHash s.PairSnds.[e]
        let mutable i = (h &&& 1073741823) &&& mask
        while slots.[i] <> 0 do
            i <- (i + 1) &&& mask
        slots.[i] <- e + 1
        e <- e + 1
    s.PairSlots <- slots

let refPairSetAdd (s : RefPairSet<'a>) (a : 'a) (b : 'a) : bool =
    let at = refPairSlot s a b
    if s.PairSlots.[at] > 0 then false
    else
        if s.PairCount >= s.PairFsts.Length then
            let fs : 'a[] = Array.zeroCreate (s.PairFsts.Length * 2)
            let ss : 'a[] = Array.zeroCreate (s.PairSnds.Length * 2)
            let mutable i = 0
            while i < s.PairCount do
                fs.[i] <- s.PairFsts.[i]
                ss.[i] <- s.PairSnds.[i]
                i <- i + 1
            s.PairFsts <- fs
            s.PairSnds <- ss
        s.PairFsts.[s.PairCount] <- a
        s.PairSnds.[s.PairCount] <- b
        s.PairCount <- s.PairCount + 1
        if s.PairCount * 2 >= s.PairSlots.Length then refPairRehash s
        else s.PairSlots.[at] <- s.PairCount
        true

type RefMap<'k, 'v> =
    { mutable MapKeys : 'k[]
      mutable MapVals : 'v[]
      mutable MapSlots : int[]
      mutable MapCount : int
      MapHash : 'k -> int }

let refMapNew (h : 'k -> int) : RefMap<'k, 'v> =
    { MapKeys = Array.zeroCreate 8; MapVals = Array.zeroCreate 8
      MapSlots = Array.zeroCreate 16; MapCount = 0; MapHash = h }

let private refMapSlot (m : RefMap<'k, 'v>) (k : 'k) : int =
    let mask = m.MapSlots.Length - 1
    let mutable i = (m.MapHash k &&& 1073741823) &&& mask
    let mutable found = -1
    while found < 0 do
        let e = m.MapSlots.[i]
        if e = 0 then found <- i
        elif refEq m.MapKeys.[e - 1] k then found <- i
        else i <- (i + 1) &&& mask
    found

let private refMapRehash (m : RefMap<'k, 'v>) : unit =
    let slots : int[] = Array.zeroCreate (m.MapSlots.Length * 2)
    let mask = slots.Length - 1
    let mutable e = 0
    while e < m.MapCount do
        let mutable i = (m.MapHash m.MapKeys.[e] &&& 1073741823) &&& mask
        while slots.[i] <> 0 do
            i <- (i + 1) &&& mask
        slots.[i] <- e + 1
        e <- e + 1
    m.MapSlots <- slots

/// Drop every entry, keeping the table itself. Same contract as the .NET
/// half's Clear: capacity may stay, the contents do not.
let refMapClear (m : RefMap<'k, 'v>) : unit =
    m.MapSlots <- Array.zeroCreate m.MapSlots.Length
    m.MapCount <- 0

let refMapSet (m : RefMap<'k, 'v>) (k : 'k) (v : 'v) : unit =
    let at = refMapSlot m k
    let e = m.MapSlots.[at]
    if e > 0 then m.MapVals.[e - 1] <- v
    else
        if m.MapCount >= m.MapKeys.Length then
            let keys : 'k[] = Array.zeroCreate (m.MapKeys.Length * 2)
            let vals : 'v[] = Array.zeroCreate (m.MapVals.Length * 2)
            let mutable i = 0
            while i < m.MapCount do
                keys.[i] <- m.MapKeys.[i]
                vals.[i] <- m.MapVals.[i]
                i <- i + 1
            m.MapKeys <- keys
            m.MapVals <- vals
        m.MapKeys.[m.MapCount] <- k
        m.MapVals.[m.MapCount] <- v
        m.MapCount <- m.MapCount + 1
        if m.MapCount * 2 >= m.MapSlots.Length then refMapRehash m
        else m.MapSlots.[at] <- m.MapCount

let refMapTryFind (m : RefMap<'k, 'v>) (k : 'k) : 'v option =
    let e = m.MapSlots.[refMapSlot m k]
    if e > 0 then Some m.MapVals.[e - 1] else None

// ---- host services ---------------------------------------------------

// The RAW imports, over strings only, so that any host can satisfy them:
// a wasm preload module, a browser's preloaded in-memory map. `readTextRaw`
// answers null for a missing file and `listDirRaw` a newline-separated
// list; the wrapping into option and array happens HERE, not in the host.
//
// Synchronous and process-global, deliberately. A host that cannot do
// synchronous IO preloads instead — making the compiler async would infect
// every call path to accommodate it.

extern let readTextRaw : string -> string
extern let existsRaw : string -> int
extern let listDirRaw : string -> string
extern let canonicalizeRaw : string -> string
// the prelude's own text, supplied by the host (the .NET build reads it out
// of its embedded resource; a wasm host hands over what it preloaded)
extern let preludeSourceRaw : string -> string

/// The prelude's own source, as the compiler's front end needs it.
let preludeSource () : string = preludeSourceRaw ""

/// The text of a file, or None when it is not there. NO exception crosses
/// the boundary: the caller reports the miss, with the diagnostics it
/// already owns.
let hostReadText (path : string) : string option =
    let s = readTextRaw path
    if isNull s then None else Some s

let hostExists (path : string) : bool = existsRaw path <> 0

let hostListDir (path : string) : string[] =
    let s = listDirRaw path
    if isNull s || s = "" then Array.zeroCreate 0
    else Array.filter (fun (e : string) -> e <> "") (s.Split '\n')

let hostCanonicalize (path : string) : string =
    let s = canonicalizeRaw path
    if isNull s then path else s

// ---- path arithmetic: PURE, so no host is involved -------------------

let pathIsRooted (p : string) : bool = strLen p > 0 && charAt p 0 = '/'

let pathDirectory (p : string) : string =
    let i = p.LastIndexOf '/'
    if i < 0 then "" elif i = 0 then "/" else substr p 0 i

let pathFileName (p : string) : string =
    let i = p.LastIndexOf '/'
    if i < 0 then p else substr p (i + 1) (strLen p - i - 1)

let pathFileNameWithoutExtension (p : string) : string =
    let f = pathFileName p
    let i = f.LastIndexOf '.'
    if i <= 0 then f else substr f 0 i

let pathCombine (dir : string) (rel : string) : string =
    if dir = "" then rel
    elif pathIsRooted rel then rel
    elif charAt dir (strLen dir - 1) = '/' then dir + rel
    else dir + "/" + rel

// ---- incremental text ----
// The same four operations the .NET half exposes over StringBuilder. Here it
// is a vector of chunks joined once: appending is amortized O(1) and the join
// is linear, where repeated `+` on a growing string would be quadratic.
type Builder = { mutable Chunks : Vec<string> }

let sbNew () : Builder = { Chunks = vecNew () }
let sbAdd (b : Builder) (s : string) : unit = vecAdd b.Chunks s
let sbAddLine (b : Builder) (s : string) : unit =
    vecAdd b.Chunks s
    vecAdd b.Chunks "\n"
let sbLen (b : Builder) : int =
    let mutable n = 0
    for c in vecToList b.Chunks do n <- n + c.Length
    n
let sbClear (b : Builder) : unit = b.Chunks <- vecNew ()
let sbText (b : Builder) : string = String.concat "" (vecToList b.Chunks)

// ---- character classes and ordinal comparison ----
let isLetterOrDigit (c : char) : bool =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')
let isDigitCh (c : char) : bool = c >= '0' && c <= '9'

/// A string hash the compiler can BUILD NAMES from — spelled out so both
/// halves of the seam agree. The host's own `hash` does not: the same
/// mangled name hashed differently in the dotnet-built compiler and in the
/// compiler compiled to wasm, and the two emitted different symbols.
let strHash (s : string) : int =
    let mutable h = 17
    let mutable i = 0
    while i < s.Length do
        h <- h * 31 + int s.[i]
        i <- i + 1
    h

/// Ordinal comparison of a SLICE of `s` (at `i`, `len` long) against the
/// slice of `t` at `j`. Negative, zero or positive, like the .NET half.
let compareOrdinalAt (s : string) (i : int) (t : string) (j : int) (len : int) : int =
    let mutable k = 0
    let mutable r = 0
    while r = 0 && k < len do
        if i + k >= s.Length then r <- -1
        elif j + k >= t.Length then r <- 1
        else
            let a = int s.[i + k]
            let b = int t.[j + k]
            if a < b then r <- -1
            elif a > b then r <- 1
        k <- k + 1
    r

// ---- literal parsing ----
// The same family the .NET half exposes. A compiler reads numbers in these
// forms only, and both halves must answer identically.

let private digitVal (c : char) : int =
    if c >= '0' && c <= '9' then int c - int '0'
    elif c >= 'a' && c <= 'f' then 10 + int c - int 'a'
    elif c >= 'A' && c <= 'F' then 10 + int c - int 'A'
    else -1

let parseInt64In (baseN : int) (digits : string) : int64 =
    let mutable acc = 0L
    let mutable i = 0
    while i < digits.Length do
        let d = digitVal digits.[i]
        if d >= 0 && d < baseN then acc <- acc * int64 baseN + int64 d
        i <- i + 1
    acc

let parseUInt32In (baseN : int) (digits : string) : int =
    int (parseInt64In baseN digits)

let parseUInt32 (digits : string) : int = int (parseInt64In 10 digits)

/// decimal, including an exponent: mantissa digits scaled by the exponent
let parseFloat (s : string) : float =
    let mutable intPart = 0.0
    let mutable frac = 0.0
    let mutable scale = 0.1
    let mutable exp = 0
    let mutable expSign = 1
    let mutable neg = false
    let mutable stage = 0
    let mutable i = 0
    while i < s.Length do
        let c = s.[i]
        if c = '-' && i = 0 then neg <- true
        elif c = '.' then stage <- 1
        elif c = 'e' || c = 'E' then stage <- 2
        elif c = '-' && stage = 2 then expSign <- -1
        elif c = '+' && stage = 2 then expSign <- 1
        elif isDigitCh c then
            let d = digitVal c
            if stage = 0 then intPart <- intPart * 10.0 + float d
            elif stage = 1 then
                frac <- frac + float d * scale
                scale <- scale * 0.1
            else exp <- exp * 10 + d
        i <- i + 1
    let mutable v = intPart + frac
    let mutable k = 0
    while k < exp do
        if expSign > 0 then v <- v * 10.0 else v <- v / 10.0
        k <- k + 1
    if neg then -v else v

/// The IEEE half nearest `v`, as its 16 bits. F++ HAS float16, and the
/// conversion is exact by the 2p+2 double-rounding rule the backend already
/// relies on, so the bits come from the language rather than a host call.
let halfBits (v : float) : int = float16Bits (float16 v)

/// How many BYTES this text occupies. A string IS a byte sequence here —
/// source is read as bytes, so there is nothing left to encode.
let byteLength (s : string) : int = s.Length

/// Bytes as the string they already are: a string IS a byte array here, so
/// this is a copy with a type change (the Builder merges pairwise, so the
/// concat is not quadratic).
let bytesString (bs : byte[]) : string =
    let b = sbNew ()
    let mutable i = 0
    while i < bs.Length do
        sbAdd b (string (char (int bs.[i])))
        i <- i + 1
    sbText b

/// The same text as BYTES.
let stringBytes (s : string) : byte[] =
    let out = Array.zeroCreate s.Length
    let mutable i = 0
    while i < s.Length do
        out.[i] <- byte s.[i]
        i <- i + 1
    out
