module Fpp.Prelude

// The bootstrap seam. The compiler is written in the common subset of F# and
// F++; every runtime touchpoint goes through this module so that the F++
// stdlib only ever has to reimplement this file to close the loop.

let inline strLen (s : string) : int = s.Length
let inline charAt (s : string) (i : int) : char = s.[i]
let inline substr (s : string) (start : int) (len : int) : string = s.Substring(start, len)

let inline isDigit (c : char) : bool = c >= '0' && c <= '9'
let inline isHexDigit (c : char) : bool = isDigit c || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')
let inline isAsciiLetter (c : char) : bool = (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
let isLetter (c : char) : bool = isAsciiLetter c || System.Char.IsLetter c

let stringOfChars (cs : char list) : string = System.String(List.toArray cs)

/// Growable vector — the only mutable collection the compiler uses.
type Vec<'a> = System.Collections.Generic.List<'a>

/// Incremental text. Repeated `+` on a growing string is quadratic, and the
/// emitter builds megabytes; both halves of the seam provide the same four
/// operations so compiler code never names a host type.
type Builder = System.Text.StringBuilder
let sbNew () : Builder = System.Text.StringBuilder ()
let sbAdd (b : Builder) (s : string) : unit = b.Append s |> ignore
let sbAddLine (b : Builder) (s : string) : unit = b.AppendLine s |> ignore
let sbLen (b : Builder) : int = b.Length
let sbClear (b : Builder) : unit = b.Clear () |> ignore
let sbText (b : Builder) : string = b.ToString ()

/// Character classes and ordinal comparison, as host services: the F++ half
/// implements them over code points rather than naming a .NET type.
let isLetterOrDigit (c : char) : bool = System.Char.IsLetterOrDigit c
let isDigitCh (c : char) : bool = c >= '0' && c <= '9'
/// Ordinal comparison of a SLICE of `s` (at `i`, `len` long) against `t`.
let compareOrdinalAt (s : string) (i : int) (t : string) (j : int) (len : int) : int =
    System.String.CompareOrdinal (s, i, t, j, len)

// ---- literal parsing -------------------------------------------------
// One family, because a compiler reads numbers in exactly these forms and
// the F++ half must answer identically — bit patterns, not approximations.

/// digits in the given base (2..16) as a signed 64-bit value
let parseInt64In (baseN : int) (digits : string) : int64 =
    System.Convert.ToInt64 (digits, baseN)
/// digits in the given base as an unsigned 32-bit value, kept in an int
let parseUInt32In (baseN : int) (digits : string) : int =
    int (System.Convert.ToUInt32 (digits, baseN))
let parseUInt32 (digits : string) : int = int (System.UInt32.Parse digits)
/// decimal (never locale-dependent: a compiler's output must not move
/// because of a machine's culture settings)
let parseFloat (s : string) : float =
    System.Double.Parse (s, System.Globalization.CultureInfo.InvariantCulture)
/// the IEEE half nearest `v`, as its 16 bits
let halfBits (v : float) : int =
    int (System.BitConverter.HalfToInt16Bits (System.Half.op_Explicit v)) &&& 0xffff
/// how many BYTES this text occupies as UTF-8
let utf8Length (s : string) : int = System.Text.Encoding.UTF8.GetByteCount s

let inline vecNew<'a> () : Vec<'a> = Vec<'a>()
let inline vecLen (v : Vec<'a>) : int = v.Count
let inline vecGet (v : Vec<'a>) (i : int) : 'a = v.[i]
let inline vecSet (v : Vec<'a>) (i : int) (x : 'a) : unit = v.[i] <- x
let inline vecAdd (v : Vec<'a>) (x : 'a) : unit = v.Add x
let inline vecInsert (v : Vec<'a>) (i : int) (x : 'a) : unit = v.Insert(i, x)
let inline vecClear (v : Vec<'a>) : unit = v.Clear ()
let inline vecToList (v : Vec<'a>) : 'a list = List.ofSeq v
let inline vecToArray (v : Vec<'a>) : 'a[] = v.ToArray()
let vecOfList (xs : 'a list) : Vec<'a> = Vec<'a>(xs)

/// Mutable hash map — used only by the query engine.
type Dict<'k, 'v> = System.Collections.Generic.Dictionary<'k, 'v>

let inline dictNew<'k, 'v when 'k : equality> () : Dict<'k, 'v> = Dict<'k, 'v>()
let inline dictSet (d : Dict<'k, 'v>) (k : 'k) (v : 'v) : unit = d.[k] <- v

let dictTryFind (d : Dict<'k, 'v>) (k : 'k) : 'v option =
    match d.TryGetValue k with
    | true, v -> Some v
    | _ -> None

let inline dictRemove (d : Dict<'k, 'v>) (k : 'k) : unit = d.Remove k |> ignore

let dictPairs (d : Dict<'k, 'v>) : ('k * 'v) list =
    [ for kv in d -> kv.Key, kv.Value ]

// ---- reference-identity collections -----------------------------------
//
// A pruned type is a GRAPH, so every structural walker over one needs a
// visited set, and IDENTITY is what it has to key on: two structurally
// equal types that are different objects are different nodes, and hashing
// a cyclic one structurally would not terminate.
//
// The hash comes from the caller and must read only IMMUTABLE fields.
// Unification rewrites `Link` while a visited set is live; a hash that
// looked at a link would move an entry's bucket out from under it. Any hash
// is otherwise legal, since identity-equal values are the same object and
// hash equally by construction.
//
// The F++ half (stdlib/bootstrap.fpp) builds these over `refEq`, which is
// why the hash is a parameter at all: wasm-GC exposes no address, and the
// emitter's identity numbers live in a hidden field on CLASS instances that
// a DU value does not have.

let private identityComparer<'a when 'a : not struct> (h : 'a -> int) =
    { new System.Collections.Generic.IEqualityComparer<'a> with
        member _.Equals (a, b) = System.Object.ReferenceEquals (a, b)
        member _.GetHashCode a = h a }

type RefSet<'a> = System.Collections.Generic.HashSet<'a>

let refSetNew<'a when 'a : not struct> (h : 'a -> int) : RefSet<'a> =
    RefSet<'a> (identityComparer h)

/// Add, reporting whether the value was NEW — every visited-set walk asks
/// exactly this question.
let inline refSetAdd (s : RefSet<'a>) (x : 'a) : bool = s.Add x
let inline refSetContains (s : RefSet<'a>) (x : 'a) : bool = s.Contains x

/// A set of PAIRS compared componentwise by identity — the shape
/// `unifySeen` needs to cut a shared sub-DAG down to one visit.
type RefPair<'a> =
    { PairFst : 'a; PairSnd : 'a }

type RefPairSet<'a> = System.Collections.Generic.HashSet<RefPair<'a>>

let refPairSetNew<'a when 'a : not struct> (h : 'a -> int) : RefPairSet<'a> =
    RefPairSet<'a> (
        { new System.Collections.Generic.IEqualityComparer<RefPair<'a>> with
            member _.Equals (a, b) =
                System.Object.ReferenceEquals (a.PairFst, b.PairFst)
                && System.Object.ReferenceEquals (a.PairSnd, b.PairSnd)
            member _.GetHashCode p = h p.PairFst * 397 ^^^ h p.PairSnd })

let inline refPairSetAdd (s : RefPairSet<'a>) (a : 'a) (b : 'a) : bool =
    s.Add { PairFst = a; PairSnd = b }

type RefMap<'k, 'v> = System.Collections.Generic.Dictionary<'k, 'v>

let refMapNew<'k, 'v when 'k : not struct> (h : 'k -> int) : RefMap<'k, 'v> =
    RefMap<'k, 'v> (identityComparer h)

let inline refMapSet (m : RefMap<'k, 'v>) (k : 'k) (v : 'v) : unit = m.[k] <- v

let refMapTryFind (m : RefMap<'k, 'v>) (k : 'k) : 'v option =
    match m.TryGetValue k with
    | true, v -> Some v
    | _ -> None

// ---- host services ----------------------------------------------------
//
// The four things the compiler needs from a host: read a file, test a path,
// list a directory, canonicalize a path. Nothing else — no writing, no
// process, no network.
//
// NO EXCEPTION crosses this boundary. A missing file is `None` and the
// CALLER reports it, which keeps the error surface in the compiler where
// diagnostics already live. The F++ half declares the raw imports over
// STRINGS only (null for "no result", newline-separated for a list) so any
// host can satisfy them — a wasm preload module, a browser's in-memory map —
// and wraps them into these signatures.

let hostReadText (path : string) : string option =
    if System.IO.File.Exists path then Some (System.IO.File.ReadAllText path) else None

/// The prelude's own source. A host SUPPLIES it — the .NET build embeds
/// stdlib/prelude.fpp as a resource so the binary stays self-contained; a
/// wasm host hands over the text it already has. Reading it by path would
/// make the compiler depend on finding a stdlib directory.
let preludeSource () : string =
    use s =
        System.Reflection.Assembly.GetExecutingAssembly().GetManifestResourceStream "prelude.fpp"
    use r = new System.IO.StreamReader (s)
    r.ReadToEnd ()

let hostExists (path : string) : bool =
    System.IO.File.Exists path || System.IO.Directory.Exists path

let hostListDir (path : string) : string[] =
    if System.IO.Directory.Exists path then System.IO.Directory.GetFiles path |> Array.sort
    else [||]

let hostCanonicalize (path : string) : string =
    if path = "" then "" else System.IO.Path.GetFullPath path

// Path arithmetic is PURE — no host required, so it does not belong in the
// import surface.

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
