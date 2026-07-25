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
