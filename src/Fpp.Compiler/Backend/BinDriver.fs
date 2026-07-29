module Fpp.Backend.BinDriver

open Fpp.Prelude
open Fpp.Analysis.Types
open Fpp.Core.Ir
open Fpp.Backend.WasmBinary
open Fpp.Backend.EmitBin

// The BINARY driver: Decl list -> executable .wasm bytes, no text anywhere.
// This grows exactly as the runtime did — the expression cases it can emit
// are the ones proven by running programs; anything else raises a named
// error so the next case to port is always explicit.
//
// Numbering is self-consistent within this backend (tags, data, globals):
// the binary module never has to agree with the text module byte-wise, only
// behave identically — the program-output oracle is the gate.

type St =
    { M : Mod
      Errors : Vec<string>
      CaseTag : Dict<string, int>
      CaseArity : Dict<string, int>
      EnumConst : Dict<string, int>
      GlobalOf : Dict<string * int, string>
      FnOf : Dict<string * int, string>
      ArityOf : Dict<string * int, int>
      Warnings : Vec<string>
      /// record name -> field order; (record, field) -> slot
      FieldsOf : Dict<string, string list>
      FieldIdx : Dict<string * string, int>
      /// field name -> owning record (last declaration wins, like the text)
      FieldOwner : Dict<string, string>
      /// each lifted lambda, keyed by its ELam NODE (reference identity):
      /// name + captured keys in slot order
      LamName : RefMap<Expr, string>
      LamFree : Dict<string, (string * int) list>
      LamBody : Vec<string * (VarId * Scheme) * Expr>
      /// let-bound mutables that a lambda mentions: capture copies the env
      /// BY VALUE, so these live in a one-field $cell and the copy that
      /// lands in the closure's env is a copy of the CELL REFERENCE
      CellVars : Dict<string * int, bool>
      /// class machinery: obj records (carry __desc), class ids, dispatch
      /// slots, interface implementors, subclass sets
      ObjRec : Dict<string, bool>
      ClassName : Dict<string, bool>
      DescIdOf : Dict<string, int>
      SlotOf : Dict<string * string, int>
      IfaceName : Dict<string, bool>
      ImplsOf : Dict<string, string list>
      SubsOf : Dict<string, string list>
      BaseOf : Dict<string, string>
      /// EApp nodes in tail position (by node identity): a full-arity call
      /// to a known function there compiles to return_call
      TailApp : RefMap<Expr, bool>
      /// POD struct layout: name -> (leaves as (dotted path, kind, byte
      /// offset), sizeof, stride in i64 words) — the C image a pinned
      /// array exposes
      Pod : Dict<string, (string * string * int) list * int * int>
      /// locals on a RAW scalar rail: binder key -> kind (i/f/s/l). Reads
      /// box, writes unbox — and the peephole cancels both against their
      /// producers/consumers, which is what makes a hot loop alloc-free
      LocalKind : Dict<string * int, string>
      /// known functions with SCALAR signatures: param kinds + return kind.
      /// Calls unbox arguments and box results (both cancel on rails);
      /// bodies receive raw params and return raw
      SigKinds : Dict<string * int, string list * string>
      SigByName : Dict<string, string list * string>
      /// the CURRENT body's return kind — return_call is legal only when
      /// callee and caller agree (the frame that would unbox is gone)
      mutable CurRet : string
      /// mentioned inside some lambda: those can never be rail locals
      InLambda : Dict<string * int, bool>
      /// struct-record fields with their declared TYPE names (uniform
      /// records erase types; POD navigation needs them back)
      StructFields : Dict<string, (string * string) list>
      /// curry wrappers requested for top-level functions used first-class:
      /// name -> arity, plus request order (bodies are emitted LAST, and
      /// their decls land last too, so decl order still equals body order)
      Wrappers : Dict<string, int>
      /// constructors used as first-class functions share the lazy-decl
      /// scheme with wrappers; ONE ordered list keeps decl order = body
      /// order across both kinds ("w:" wrapper chain, "c:" ctorfn)
      CtorFns : Dict<string, bool>
      LateFns : Vec<string>
      /// extern (FFI) functions: (path,offset) -> param kinds * result kind
      /// ("i" crosses as raw i32, anything else as opaque anyref)
      Externs : Dict<string * int, string list * string>
      mutable DataN : int }

let private err (st : St) (msg : string) : unit = vecAdd st.Errors msg

/// dereference a $cell already on the stack
let private cellGet (f : Fn) : unit =
    gcT f "ref.cast" "$cell"
    gcTF f "struct.get" "$cell" 0

let private mangle (v : VarId) : string =
    "$b" + string (abs (strHash v.Path % 1000)) + "_" + string v.Offset + "_"
    + (v.Name |> String.map (fun c -> if isLetterOrDigit c then c else '_'))

/// intern a string literal as a data segment, return its name and length
let private internStr (st : St) (bytes : byte[]) : string * int =
    // named by the MODULE's segment count: the scratch pass and the real
    // pass then agree without shared mutable state of their own
    let name = "$bd" + string st.M.DataCount
    dataSeg st.M name bytes
    name, bytes.Length

// unescape for string literals — the full three-spelling logic, ported from
// the retired text emitter: triple-quoted is literal, verbatim folds `""`,
// ordinary processes named/decimal/hex/unicode escapes into BYTES
let private escapeAt (s : string) (i : int) : int * int =
    let at k = if i + k < strLen s then charAt s (i + k) else '\000'
    let hexVal (c : char) =
        if c >= '0' && c <= '9' then int c - 48
        elif c >= 'a' && c <= 'f' then int c - 87
        elif c >= 'A' && c <= 'F' then int c - 55
        else -1
    let hexRun (start : int) (count : int) =
        let mutable v = 0
        let mutable k = 0
        let mutable ok = true
        while ok && k < count do
            let d = hexVal (at (start + k))
            if d < 0 then ok <- false else v <- v * 16 + d
            k <- k + 1
        if ok then Some v else None
    match at 1 with
    | 'n' -> 10, 2
    | 't' -> 9, 2
    | 'r' -> 13, 2
    | 'a' -> 7, 2
    | 'b' -> 8, 2
    | 'f' -> 12, 2
    | 'v' -> 11, 2
    | '\\' -> 92, 2
    | '"' -> 34, 2
    | '\'' -> 39, 2
    | 'x' -> (match hexRun 2 2 with Some v -> v, 4 | None -> int (at 1), 2)
    | 'u' -> (match hexRun 2 4 with Some v -> v, 6 | None -> int (at 1), 2)
    | 'U' -> (match hexRun 2 8 with Some v -> v, 10 | None -> int (at 1), 2)
    | c when c >= '0' && c <= '9' ->
        if isDigit (at 2) && isDigit (at 3) then
            ((int (at 1) - 48) * 100 + (int (at 2) - 48) * 10 + (int (at 3) - 48)) % 256, 4
        elif c = '0' then 0, 2
        else int c, 2
    | c -> int c, 2

let private unescape (raw : string) : byte[] =
    let raw = if strLen raw > 1 && charAt raw (strLen raw - 1) = 'B' then substr raw 0 (strLen raw - 1) else raw
    let isTriple =
        strLen raw >= 6 && charAt raw 0 = '"' && charAt raw 1 = '"' && charAt raw 2 = '"'
    let isVerbatim = strLen raw >= 3 && charAt raw 0 = '@'
    let out = vecNew<byte> ()
    if isTriple then
        // no escape processing at all: the text IS the value
        let inner = substr raw 3 (strLen raw - 6)
        for k in 0 .. strLen inner - 1 do vecAdd out (byte (charAt inner k))
    elif isVerbatim then
        // `""` is the only escape a verbatim string has
        let inner = substr raw 2 (strLen raw - 3)
        let mutable i = 0
        while i < strLen inner do
            if charAt inner i = '"' && i + 1 < strLen inner && charAt inner (i + 1) = '"' then
                vecAdd out (byte 34)
                i <- i + 2
            else
                vecAdd out (byte (charAt inner i))
                i <- i + 1
    else
        let inner = if strLen raw >= 2 then substr raw 1 (strLen raw - 2) else raw
        let mutable i = 0
        while i < strLen inner do
            let c = charAt inner i
            if c = '\\' && i + 1 < strLen inner then
                let code, width = escapeAt inner i
                // above ASCII a `\u` escape is UTF-8 (a string IS bytes);
                // `\DDD`/`\xHH` name ONE byte, kept under 256 by escapeAt
                if code < 128 then vecAdd out (byte code)
                elif width > 2 && (charAt inner (i + 1) = 'u' || charAt inner (i + 1) = 'U') then
                    if code < 2048 then
                        vecAdd out (byte (192 ||| (code / 64)))
                        vecAdd out (byte (128 ||| (code % 64)))
                    else
                        vecAdd out (byte (224 ||| (code / 4096)))
                        vecAdd out (byte (128 ||| ((code / 64) % 64)))
                        vecAdd out (byte (128 ||| (code % 64)))
                else vecAdd out (byte (code % 256))
                i <- i + width
            else
                vecAdd out (byte c)
                i <- i + 1
    vecToArray out

/// a char literal is ONE code point; reading it out of the unescaped BYTES
/// would take only the first byte of a multi-byte escape
let private charCode (raw : string) : int =
    let inner = if strLen raw >= 2 then substr raw 1 (strLen raw - 2) else raw
    if strLen inner > 1 && charAt inner 0 = '\\' then fst (escapeAt inner 0)
    else
        let bs = unescape raw
        if bs.Length > 0 then int bs.[0] else 0

/// A local becomes a cell when it is let-bound, assigned somewhere, and
/// mentioned inside a lambda. The test is per BINDING, so every read and
/// write agrees on the representation. (Port of the text emitter's cellScan.)
let private cellScan (decls : Decl list) : Dict<string * int, bool> * Dict<string * int, bool> =
    let letBound = dictNew<string * int, bool> ()
    let assigned = dictNew<string * int, bool> ()
    let inLambda = dictNew<string * int, bool> ()
    let rec go (depth : int) (e : Expr) : unit =
        let g = go depth
        match e with
        | EVar (v, _) | EVarI (v, _, _) ->
            if depth > 0 then dictSet inLambda (v.Path, v.Offset) true
        | ELam (_, b) -> go (depth + 1) b
        | EAssign (v, x) ->
            dictSet assigned (v.Path, v.Offset) true
            if depth > 0 then dictSet inLambda (v.Path, v.Offset) true
            g x
        | ELet (_, v, _, r, b) ->
            dictSet letBound (v.Path, v.Offset) true
            g r
            g b
        | EApp (fn, args) -> g fn; List.iter g args
        | EIf (a, b, c) -> g a; g b; g c
        | EMatch (s, cs) ->
            g s
            for _, gd, b in cs do
                (match gd with Some gd -> g gd | None -> ())
                g b
        | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) | ECtor (_, _, xs) | EArray (_, xs) ->
            List.iter g xs
        | ERecord (_, fs) -> for _, v in fs do g v
        | ERecordExt (_, b, fs) -> g b; (for _, v in fs do g v)
        | EField (r, _, _) -> g r
        | EFieldSet (r, _, _, v) -> g r; g v
        | EWhile (c, b) -> g c; g b
        | EIndex (_, a, i) -> g a; g i
        | EIndexSet (_, a, i, v) -> g a; g i; g v
        | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) | ECast (_, a, _) | ETypeTest (_, a) -> g a
        | EArrayCreate (_, n, v) -> g n; g v
        | EIfaceCall (_, _, recv, args) -> g recv; List.iter g args
        | ETry (b, cs) ->
            g b
            for _, gd, x in cs do
                (match gd with Some gd -> g gd | None -> ())
                g x
        | _ -> ()
    // a top-level function's own parameter lambdas ARE the function, not a
    // capture boundary — its body compiles to a wasm function whose locals
    // are locals
    let rec skipParams (e : Expr) : Expr =
        match e with
        | ELam (_, b) -> skipParams b
        | _ -> e
    for d in decls do
        match d with
        | DLet (_, _, _, e) -> go 0 (skipParams e)
        | _ -> ()
    let cells = dictNew<string * int, bool> ()
    for k, _ in dictPairs assigned do
        if (dictTryFind letBound k).IsSome && (dictTryFind inLambda k).IsSome then
            dictSet cells k true
    // the lambda-mentioned set travels too: a local a lambda reads can
    // never live on a raw scalar rail (env slots are anyref)
    cells, inLambda

/// free variables of a body: referenced keys minus those bound inside
let rec private freeWalk (bound : Dict<string * int, bool>) (acc : Vec<string * int>) (seen : Dict<string * int, bool>) (e : Expr) : unit =
    let note (v : VarId) =
        let k = (v.Path, v.Offset)
        if not (dictTryFind bound k).IsSome && not (dictTryFind seen k).IsSome then
            dictSet seen k true
            vecAdd acc k
    let rec bindPat (p : Pat) =
        match p with
        | PVar (v, _) -> dictSet bound (v.Path, v.Offset) true
        | PAs (inner, v, _) -> dictSet bound (v.Path, v.Offset) true; bindPat inner
        | PCtor (_, _, ps) | PTuple ps | PListLit ps | POr ps -> List.iter bindPat ps
        | PCons (h, t) -> bindPat h; bindPat t
        | _ -> ()
    match e with
    | EVar (v, _) | EVarI (v, _, _) -> note v
    | EAssign (v, x) -> note v; freeWalk bound acc seen x
    | ELam (ps, b) ->
        for pv, _ in ps do dictSet bound (pv.Path, pv.Offset) true
        freeWalk bound acc seen b
    | ELet (true, _, _, _, _) ->
        // a REC GROUP's binders are all in scope inside every member's rhs:
        // bind the whole spine run FIRST, or a member's reference to a later
        // sibling leaks into the enclosing lambda as a phantom capture no
        // frame can provide. Merging adjacent independent rec-lets this way
        // is harmless — their binders simply shadow nothing.
        let members = vecNew<Expr> ()
        let mutable cur = e
        let mutable go = true
        while go do
            match cur with
            | ELet (true, v, _, rhs, b) ->
                dictSet bound (v.Path, v.Offset) true
                vecAdd members rhs
                cur <- b
            | _ -> go <- false
        for rhs in vecToList members do freeWalk bound acc seen rhs
        freeWalk bound acc seen cur
    | ELet (_, v, _, rhs, b) ->
        freeWalk bound acc seen rhs
        dictSet bound (v.Path, v.Offset) true
        freeWalk bound acc seen b
    | EMatch (sc, cs) ->
        freeWalk bound acc seen sc
        for pt, g, b in cs do
            bindPat pt
            (match g with Some x -> freeWalk bound acc seen x | None -> ())
            freeWalk bound acc seen b
    | EApp (g, args) -> freeWalk bound acc seen g; for a in args do freeWalk bound acc seen a
    | EIf (a, b, c) -> freeWalk bound acc seen a; freeWalk bound acc seen b; freeWalk bound acc seen c
    | ESeq xs | ETuple xs | EListLit xs | EPrim (_, xs) | ECtor (_, _, xs) | EArray (_, xs) ->
        for x in xs do freeWalk bound acc seen x
    | ERecord (_, fs) -> for _, v in fs do freeWalk bound acc seen v
    | ERecordExt (_, b, fs) -> freeWalk bound acc seen b; (for _, v in fs do freeWalk bound acc seen v)
    | EField (r, _, _) -> freeWalk bound acc seen r
    | EFieldSet (r, _, _, v) -> freeWalk bound acc seen r; freeWalk bound acc seen v
    | EWhile (c, b) -> freeWalk bound acc seen c; freeWalk bound acc seen b
    | EIfaceCall (_, _, r, args) -> freeWalk bound acc seen r; for a in args do freeWalk bound acc seen a
    | ECast (_, x, _) | ETypeTest (_, x) | EArrayLen (_, x) -> freeWalk bound acc seen x
    | EIndex (_, a, i) -> freeWalk bound acc seen a; freeWalk bound acc seen i
    | EIndexSet (_, a, i, v) -> freeWalk bound acc seen a; freeWalk bound acc seen i; freeWalk bound acc seen v
    | EArrayCreate (_, a, b) -> freeWalk bound acc seen a; freeWalk bound acc seen b
    | ETry (b, cs) ->
        freeWalk bound acc seen b
        for pt, g, x in cs do
            bindPat pt
            (match g with Some gg -> freeWalk bound acc seen gg | None -> ())
            freeWalk bound acc seen x
    | _ -> ()

/// discover every lambda in DFS order: curry multi-param, name it, record
/// its free list (order = discovery order of the walk), queue its body
let rec private discoverLams (st : St) (outer : Dict<string * int, bool>) (e : Expr) : unit =
    match e with
    | ELam (ps, body) ->
        // curry to unary
        (match ps with
         | [ (pv, psch) ] ->
             let name = "$blam" + string (vecLen st.LamBody)
             refMapSet st.LamName e name
             let bound = dictNew<string * int, bool> ()
             dictSet bound (pv.Path, pv.Offset) true
             let acc = vecNew<string * int> ()
             freeWalk bound acc (dictNew ()) body
             // captures exclude globals and known functions: those resolve
             // directly wherever they are read. BOTH the build site and the
             // body index this same filtered list, so slots cannot drift.
             let captured =
                 vecToList acc
                 |> List.filter (fun k ->
                     not (dictTryFind st.GlobalOf k).IsSome
                     && not (dictTryFind st.FnOf k).IsSome)
             dictSet st.LamFree name captured
             vecAdd st.LamBody (name, (pv, psch), body)
             let inner = dictNew<string * int, bool> ()
             dictSet inner (pv.Path, pv.Offset) true
             discoverLams st inner body
         | (pv, psch) :: rest ->
             let curried = ELam ([ (pv, psch) ], ELam (rest, body))
             refMapSet st.LamName e (
                 // name the SOURCE node by its curried head so emitNode
                 // finds it: discover the curried form and alias
                 let nm = "$blam" + string (vecLen st.LamBody)
                 discoverLams st outer curried
                 (match refMapTryFind st.LamName curried with Some n -> n | None -> nm))
         | [] -> ())
    | ELet (_, _, _, rhs, b) -> discoverLams st outer rhs; discoverLams st outer b
    | EMatch (sc, cs) ->
        discoverLams st outer sc
        for _, g, b in cs do
            (match g with Some x -> discoverLams st outer x | None -> ())
            discoverLams st outer b
    | EApp (g, args) -> discoverLams st outer g; for a in args do discoverLams st outer a
    | EIf (a, b, c) -> discoverLams st outer a; discoverLams st outer b; discoverLams st outer c
    | ESeq xs | ETuple xs | EListLit xs | EPrim (_, xs) | ECtor (_, _, xs) | EArray (_, xs) ->
        for x in xs do discoverLams st outer x
    | ERecord (_, fs) -> for _, v in fs do discoverLams st outer v
    | EField (r, _, _) -> discoverLams st outer r
    | EFieldSet (r, _, _, v) -> discoverLams st outer r; discoverLams st outer v
    | EWhile (c, b) -> discoverLams st outer c; discoverLams st outer b
    | EAssign (_, x) -> discoverLams st outer x
    | EIfaceCall (_, _, r, args) -> discoverLams st outer r; for a in args do discoverLams st outer a
    | ECast (_, x, _) | ETypeTest (_, x) | EArrayLen (_, x) | EArrayPin (_, x) | EArrayUnpin (_, x) ->
        discoverLams st outer x
    | ERecordExt (_, b, fs) ->
        discoverLams st outer b
        for _, v in fs do discoverLams st outer v
    | EIndex (_, a, i) -> discoverLams st outer a; discoverLams st outer i
    | EIndexSet (_, a, i, v) ->
        discoverLams st outer a
        discoverLams st outer i
        discoverLams st outer v
    | EArrayCreate (_, n, v) -> discoverLams st outer n; discoverLams st outer v
    | ETry (b, cs) ->
        discoverLams st outer b
        for _, g, x in cs do
            (match g with Some gg -> discoverLams st outer gg | None -> ())
            discoverLams st outer x
    | _ -> ()

/// a known top-level function used as a VALUE: declare its curried wrapper
/// chain once; the closure built at the use site enters at .w0
let private requestWrapper (st : St) (f : Fn) (fname : string) (arity : int) : unit =
    if not (dictTryFind st.Wrappers fname).IsSome then
        dictSet st.Wrappers fname arity
        vecAdd st.LateFns ("w:" + fname)
        for k in 0 .. arity - 1 do declFn f.M (fname + ".w" + string k) "$u1"

/// cast to (ref null eq) — ref.eq's operand type
let private castEq (f : Fn) : unit =
    gci f "ref.cast_null"
    emitS32 f.B (heapByte "eq" - 0x80)

/// the STATIC kind of an expression, where one is knowable without type
/// state: enough to pick the rail a kindless conversion reads from. Uniform
/// storage makes "u" safe everywhere else — the value carries its box.
/// packed-array element classification: which $parr_* a primitive element
/// type stores in. byte/sbyte are NOT here — they share $str (packed i8).
let private parrK (nm : string) : string =
    match nm with
    | "int" | "bool" | "char" -> "i"
    | "float16" -> "h"
    | "float" -> "f"
    | "float32" -> "s"
    | "int64" -> "l"
    | _ -> ""
let private parrTy (k : string) = "$parr_" + k
let private boxOfK (k : string) = match k with "f" -> "$off" | "s" -> "$oss" | "l" -> "$ofl" | _ -> "$ofi"
let private unboxOfK (k : string) = match k with "f" -> "$tof" | "s" -> "$tos" | "l" -> "$tol" | _ -> "$toi"
/// packed reads need an explicit sign; a half reads unsigned
let private getOpOfK (k : string) = if k = "h" then "array.get_u" else "array.get"

let rec private kindOfLite (st : St) (e : Expr) : string =
    let kindOfLite = kindOfLite st
    match e with
    | EVar (v, _) | EVarI (v, _, _) ->
        (match dictTryFind st.LocalKind (v.Path, v.Offset) with Some k -> k | None -> "u")
    | EIndex (nm, _, _) ->
        (match parrK nm with
         | "" -> (if nm = "byte" || nm = "sbyte" then "i" elif nm = "$str" then "i" else "u")
         | "h" -> "u"
         | k -> k)
    | EField (EIndex (nm, _, _), fname, _) when (dictTryFind st.Pod nm).IsSome ->
        (match (dictTryFind st.Pod nm).Value |> fun (placed, _, _) -> placed |> List.tryFind (fun (p, _, _) -> p = fname) with
         | Some (_, k, _) -> k
         | None -> "u")
    | ELit (LFloat t) ->
        if t.EndsWith "h" || t.EndsWith "H" then "u"
        elif t.EndsWith "f" || t.EndsWith "F" then "s"
        else "f"
    | ELit (LInt t) -> if t.EndsWith "L" then "l" else "i"
    | EPrim (op, _) when
        op.Length > 1 && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "-"; "*"; "/"; "%" ] ->
        let k = op.Substring (op.Length - 1)
        if k = "f" || k = "s" || k = "l" then k else "u"
    | EPrim (("-" | "*" | "/" | "%" | "&&&" | "|||" | "^^^" | "<<<" | ">>>" | "u~~~"), _) -> "i"
    | EPrim ("u-f", _) -> "f"
    | EPrim ("u-s", _) -> "s"
    | EPrim ("u-l", _) -> "l"
    | ELet (_, _, _, _, body) -> kindOfLite body
    | ESeq xs -> (match List.tryLast xs with Some x -> kindOfLite x | None -> "u")
    | EIf (_, t, e2) ->
        let a, b = kindOfLite t, kindOfLite e2
        if a = b then a else "u"
    | EApp (EUnknown n, [ _ ]) when n.Contains "#" ->
        (match n.Substring (0, n.IndexOf "#") with
         | "float" -> "f" | "float32" -> "s" | "int64" -> "l" | _ -> "u")
    | EApp (EUnknown "int64", [ _ ]) -> "l"
    | EApp (EUnknown "float", [ _ ]) -> "f"
    | EApp (EUnknown "float32", [ _ ]) -> "s"
    | EApp ((EVar (v, _) | EVarI (v, _, _)), args) when
          (dictTryFind st.ArityOf (v.Path, v.Offset)) = Some (List.length args) ->
        (match dictTryFind st.SigKinds (v.Path, v.Offset) with
         | Some (_, rk) -> rk
         | None -> "u")
    | _ -> "u"

/// every tuple arity the program mentions, in expressions or patterns —
/// the frame declares one $tupN per arity and the structural runtime
/// (equal/hashv/cmpv) generates one branch per arity
let private scanTupleArities (decls : Decl list) : int list =
    let found = dictNew<int, bool> ()
    let note (n : int) = if n >= 2 then dictSet found n true
    let rec scanP (p : Pat) : unit =
        match p with
        | PTuple ps -> note (List.length ps); List.iter scanP ps
        | PCtor (_, _, ps) | PListLit ps | POr ps -> List.iter scanP ps
        | PCons (a, b) -> scanP a; scanP b
        | PAs (inner, _, _) -> scanP inner
        | _ -> ()
    let rec scan (e : Expr) : unit =
        match e with
        | ETuple xs -> note (List.length xs); List.iter scan xs
        | ELam (_, b) -> scan b
        | ELet (_, _, _, r, b) -> scan r; scan b
        | EMatch (sc, cs) ->
            scan sc
            for p, g, b in cs do
                scanP p
                (match g with Some g -> scan g | None -> ())
                scan b
        | ETry (b, cs) ->
            scan b
            for p, g, x in cs do
                scanP p
                (match g with Some g -> scan g | None -> ())
                scan x
        | EApp (g, args) -> scan g; List.iter scan args
        | EIf (a, b, c) -> scan a; scan b; scan c
        | ESeq xs | EListLit xs | EPrim (_, xs) | ECtor (_, _, xs) | EArray (_, xs) -> List.iter scan xs
        | ERecord (_, fs) -> for _, v in fs do scan v
        | ERecordExt (_, b, fs) -> scan b; (for _, v in fs do scan v)
        | EField (r, _, _) -> scan r
        | EFieldSet (r, _, _, v) -> scan r; scan v
        | EWhile (c, b) -> scan c; scan b
        | EAssign (_, x) -> scan x
        | EIfaceCall (_, _, r, args) -> scan r; List.iter scan args
        | ECast (_, x, _) | ETypeTest (_, x) -> scan x
        | EIndex (_, a, i) -> scan a; scan i
        | EIndexSet (_, a, i, v) -> scan a; scan i; scan v
        | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) -> scan a
        | EArrayCreate (_, n, v) -> scan n; scan v
        | _ -> ()
    for d in decls do
        match d with
        | DLet (_, _, _, body) -> scan body
        | _ -> ()
    dictPairs found |> List.map fst |> List.sort

/// mark every EApp in TAIL position of a function body. All emitted
/// functions return anyref, so a tail call is always type-legal; the emitter
/// turns marked full-arity known calls into return_call.
let rec private markTails (st : St) (e : Expr) : unit =
    match e with
    | EApp (_, _) -> refMapSet st.TailApp e true
    | ELet (_, _, _, _, b) -> markTails st b
    | ESeq xs -> (match List.tryLast xs with Some x -> markTails st x | None -> ())
    | EIf (_, t, el) -> markTails st t; markTails st el
    | EMatch (_, cs) -> for _, _, b in cs do markTails st b
    | _ -> ()

/// collect the run of `let rec ... = fun` bindings heading a let spine.
/// Grouping bindings that are NOT mutually recursive is harmless: their
/// markers are simply never captured, so patching finds nothing to do.
let rec private recGroupOf (e : Expr) : (VarId * Expr) list * Expr =
    match e with
    | ELet (true, v, _, (ELam (_, _) as lam), rest) ->
        let ms, body = recGroupOf rest
        (v, lam) :: ms, body
    | _ -> [], e

/// unbox instruction name for a POD leaf kind
let private podUnbox (k : string) = match k with "f" -> "$tof" | "s" -> "$tos" | "l" -> "$tol" | _ -> "$toi"

/// read one leaf (dotted path) out of a UNIFORM struct value held in local
/// `vl`, leaving the UNBOXED scalar on the stack
let rec private emitPodLeaf (st : St) (f : Fn) (rn : string) (vl : string) (path : string) (k : string) : unit =
    lg f vl
    let mutable cur = rn
    let mutable rest = path
    let mutable go = true
    while go do
        let i = rest.IndexOf '.'
        let head = if i < 0 then rest else rest.Substring (0, i)
        let idx = (dictTryFind st.FieldIdx (cur, head)).Value
        gcT f "ref.cast" ("$r_" + cur)
        gcTF f "struct.get" ("$r_" + cur) idx
        if i < 0 then go <- false
        else
            let fs = (dictTryFind st.StructFields cur).Value
            let _, ty = fs |> List.find (fun (fn, _) -> fn = head)
            cur <- ty
            rest <- rest.Substring (i + 1)
    callf f (podUnbox k)

/// push i64 word `w` of the POD value in local `vl` (C image, little-endian
/// packing of 4-byte scalars into 8-byte words)
and private emitPodWord (st : St) (f : Fn) (rn : string) (vl : string) (w : int) : unit =
    let placed, _, _ = (dictTryFind st.Pod rn).Value
    let parts = placed |> List.filter (fun (_, _, off) -> off / 8 = w)
    let one (fn : string, k : string, off : int) =
        emitPodLeaf st f rn vl fn k
        let sh = (off % 8) * 8
        match k with
        | "f" -> ins f "i64.reinterpret_f64"
        | "l" -> ()
        | "s" ->
            ins f "i32.reinterpret_f32"
            ins f "i64.extend_i32_u"
            if sh <> 0 then
                lc f (int64 sh)
                ins f "i64.shl"
        | _ ->
            ins f "i64.extend_i32_u"
            if sh <> 0 then
                lc f (int64 sh)
                ins f "i64.shl"
    match parts with
    | [] -> lc f 0L
    | first :: restP ->
        one first
        for p in restP do
            one p
            ins f "i64.or"

/// materialize a UNIFORM $r_ struct of (possibly nested) `rn` from the POD
/// words: handle in `hl`, word base in `bl`; `top`/`prefix` index the
/// top-level layout, whose offsets carry the dotted paths
and private emitPodBuild (st : St) (f : Fn) (top : string) (hl : string) (bl : string) (rn : string) (prefix : string) : unit =
    let placed, _, _ = (dictTryFind st.Pod top).Value
    for fn, ty in (dictTryFind st.StructFields rn).Value do
        let full = if prefix = "" then fn else prefix + "." + fn
        if (dictTryFind st.StructFields ty).IsSome then
            emitPodBuild st f top hl bl ty full
        else
            let _, k, off = placed |> List.find (fun (p, _, _) -> p = full)
            lg f hl
            lg f bl
            ic f (off / 8)
            ins f "i32.add"
            callf f "$hwget"
            let sh = (off % 8) * 8
            (match k with
             | "f" ->
                 ins f "f64.reinterpret_i64"
                 callf f "$off"
             | "l" -> callf f "$ofl"
             | "s" ->
                 (if sh <> 0 then
                     lc f (int64 sh)
                     ins f "i64.shr_u")
                 ins f "i32.wrap_i64"
                 ins f "f32.reinterpret_i32"
                 callf f "$oss"
             | _ ->
                 (if sh <> 0 then
                     lc f (int64 sh)
                     ins f "i64.shr_u")
                 ins f "i32.wrap_i64"
                 callf f "$ofi")
    gcT f "struct.new" ("$r_" + rn)

and private emitNode (st : St) (f : Fn) (lv : Dict<string * int, string>) (e : Expr) : unit =
    match e with
    | ELit (LInt s) when not (s.EndsWith "L") ->
        // an unsigned literal keeps its bit pattern: 4000000000u is the i32
        // whose unsigned reading is that value
        let isHex = s.StartsWith "0x" || s.StartsWith "0X"
        let isUnsigned = s.EndsWith "u" || s.EndsWith "U"
        let v =
            if isHex then parseUInt32In 16 (s.Substring(2).TrimEnd ([| 'u'; 'U' |]))
            else
                let digits = s |> String.filter (fun c -> isDigit c || c = '-')
                if digits = "" then 0
                elif isUnsigned then parseUInt32 digits
                else int digits
        ic f v
        callf f "$ofi"
    | ELit (LInt s) ->
        let isHex = s.StartsWith "0x" || s.StartsWith "0X"
        let v =
            if isHex then parseInt64In 16 (s.Substring(2).TrimEnd ([| 'L' |]))
            else
                let digits = s |> String.filter (fun c -> isDigit c || c = '-')
                if digits = "" then 0L else int64 digits
        lc f v
        callf f "$ofl"
    | ELit (LFloat s) ->
        // keep everything a float constant may contain, drop only the F++
        // width suffix; the writer speaks BITS, so the conversion is here
        let num = s |> String.filter (fun c -> isDigit c || c = '.' || c = '-' || c = '+' || c = 'e' || c = 'E')
        if s.EndsWith "h" || s.EndsWith "H" then
            // a half literal is rounded ONCE, here, into its i31 bit pattern
            ic f (halfBits (parseFloat num))
            refI31 f
        elif s.EndsWith "f" || s.EndsWith "F" then
            sc f (singleBits (float32 (parseFloat num)))
            gcT f "struct.new" "$boxs"
        else
            fc f (doubleBits (parseFloat num))
            gcT f "struct.new" "$boxf"
    | ELit (LChar raw) ->
        ic f (charCode raw)
        refI31 f
    | ELit (LBool b) ->
        ic f (if b then 1 else 0)
        refI31 f
    | ELit LUnit ->
        ic f 0
        refI31 f
    | ELit LNull -> refNull f "any"
    | ELit (LString raw) ->
        let bytes = unescape raw
        let dn, len = internStr st bytes
        ic f 0
        ic f len
        arrNewData f "$str" dn
    | ESeq xs ->
        (match List.rev xs with
         | [] ->
             ic f 0
             refI31 f
         | last :: initRev ->
             for x in List.rev initRev do
                 emitNode st f lv x
                 ins f "drop"
             emitNode st f lv last)
    | EVarI (v, sch, _) -> emitNode st f lv (EVar (v, sch))
    | EVar (v, _) ->
        let vk = (v.Path, v.Offset)
        (match dictTryFind lv vk with
         | Some l when l.StartsWith "@env:" ->
             lg f "$env"
             gcT f "ref.cast" "$arr"
             ic f (int (l.Substring 5))
             gcT f "array.get" "$arr"
             // the env slot holds the CELL, shared with the frame that owns
             // it — that sharing is the whole point; reading dereferences
             if (dictTryFind st.CellVars vk).IsSome then cellGet f
         | Some l ->
             lg f l
             (match dictTryFind st.LocalKind vk with
              | Some k -> callf f (boxOfK k)
              | None -> if (dictTryFind st.CellVars vk).IsSome then cellGet f)
         | None ->
         match dictTryFind st.GlobalOf vk with
         | Some g -> gg f g
         | None ->
         match dictTryFind st.FnOf vk, dictTryFind st.ArityOf vk with
         | Some fn, Some ar ->
             // function as a value: curried wrapper closure chain
             requestWrapper st f fn ar
             rf f (fn + ".w0")
             refNull f "any"
             gcT f "struct.new" "$clo"
         | _ ->
             err st ("binary: unbound variable " + v.Name)
             refNull f "any")
    | ELet (_, _, _, _, _) ->
        // the let spine, iteratively, exactly like the text emitter
        let mutable cur = e
        let mutable walking = true
        while walking do
            match cur with
            | ELet (true, _, _, ELam _, _) ->
                // recursive local functions: every member captures the
                // others, so no closure can be built until every name has a
                // slot. Bind each name to a fresh MARKER (distinct identity),
                // build every closure over the markers, install, then patch
                // each closure's env slots marker → closure. A single rec
                // binding is just a one-element group.
                let members, groupBody = recGroupOf cur
                let slots =
                    members
                    |> List.map (fun (v, lam) ->
                        v, lam,
                        freshLocal f "$bl" "anyref",
                        freshLocal f "$bmk" "anyref",
                        freshLocal f "$bcl" "anyref")
                for v, _, l, _, _ in slots do dictSet lv (v.Path, v.Offset) l
                for _, _, l, mk, _ in slots do
                    ic f -999
                    gcT f "struct.new" "$du0"
                    ls f mk
                    lg f mk
                    ls f l
                for _, lam, _, _, cl in slots do
                    emitNode st f lv lam
                    ls f cl
                for _, _, l, _, cl in slots do
                    lg f cl
                    ls f l
                for _, _, _, _, cl in slots do
                    for _, _, _, mk2, cl2 in slots do
                        lg f cl
                        lg f mk2
                        lg f cl2
                        callf f "$patchmark"
                cur <- groupBody
            | ELet (_, v, _, rhs, body) ->
                let key = (v.Path, v.Offset)
                let k = kindOfLite st rhs
                if (dictTryFind st.CellVars key).IsNone
                   && (dictTryFind st.InLambda key).IsNone
                   && (k = "i" || k = "f" || k = "s" || k = "l") then
                    // RAW RAIL: the local carries the scalar itself; the
                    // unbox here cancels against the rhs's box, and every
                    // read boxes (cancelled by scalar consumers in turn)
                    emitNode st f lv rhs
                    callf f (unboxOfK k)
                    let ty = match k with "f" -> "f64" | "s" -> "f32" | "l" -> "i64" | _ -> "i32"
                    let l = freshLocal f "$tl" ty
                    dictSet st.LocalKind key k
                    dictSet lv key l
                    ls f l
                else
                    emitNode st f lv rhs
                    // a captured mutable: the frame holds the CELL, not the value
                    if (dictTryFind st.CellVars key).IsSome then
                        gcT f "struct.new" "$cell"
                    let l = freshLocal f "$bl" "anyref"
                    dictSet lv key l
                    ls f l
                cur <- body
            | _ -> walking <- false
        emitNode st f lv cur
    | EIf (c, t, el) ->
        emitNode st f lv c
        callf f "$toi"
        ifA f
        emitNode st f lv t
        elseB f
        emitNode st f lv el
        endB f
    | EMatch (scrut, cases) ->
        let sl = freshLocal f "$bm" "anyref"
        let res = freshLocal f "$br" "anyref"
        emitNode st f lv scrut
        ls f sl
        blockE f "$mdone"
        let mutable ci = 0
        for pat, guard, body in cases do
            let lbl = "$mc" + string ci
            ci <- ci + 1
            blockE f lbl
            emitPat st f lv lbl sl pat
            (match guard with
             | Some g ->
                 emitNode st f lv g
                 callf f "$toi"
                 ins f "i32.eqz"
                 brIf f lbl
             | None -> ())
            emitNode st f lv body
            ls f res
            br f "$mdone"
            endB f
        ins f "unreachable"
        endB f
        lg f res
    | ETry (body, cases) ->
        let res = freshLocal f "$tr" "anyref"
        let exn = freshLocal f "$tx" "anyref"
        blockE f "$tdone"
        blockA f "$tcatch"
        tryTableA f "$tcatch"
        emitNode st f lv body
        endB f
        ls f res
        br f "$tdone"
        endB f
        ls f exn
        let mutable ci = 0
        for pat, guard, cbody in cases do
            let lbl = "$tc" + string ci
            ci <- ci + 1
            blockE f lbl
            emitPat st f lv lbl exn pat
            (match guard with
             | Some g ->
                 emitNode st f lv g
                 callf f "$toi"
                 ins f "i32.eqz"
                 brIf f lbl
             | None -> ())
            emitNode st f lv cbody
            ls f res
            br f "$tdone"
            endB f
        // no case matched: the exception continues outward
        lg f exn
        throwExn f
        endB f
        lg f res
    | ERecordExt (rn, baseExpr, fields) ->
        // a derived instance IS its base's layout plus its own fields;
        // unchanged slots copy straight out of the base (prefix layout makes
        // the index valid in the plain `{ r with ... }` case too)
        (match dictTryFind st.FieldsOf rn with
         | Some order ->
             let bl = freshLocal f "$bx" "anyref"
             emitNode st f lv baseExpr
             ls f bl
             let baseRn = dictTryFind st.BaseOf rn
             let baseLen =
                 match baseRn with
                 | Some bn -> (match dictTryFind st.FieldsOf bn with Some o -> o.Length | None -> 0)
                 | None -> 0
             order |> List.iteri (fun i fname ->
                 if fname = "__idhash" then
                     ic f 0
                     refI31 f
                 elif fname = "__desc" && (dictTryFind st.ObjRec rn).IsSome then
                     gg f ("$desc_" + rn)
                 else
                     match fields |> List.tryFind (fun (fn, _) -> fn = fname) with
                     | Some (_, v) -> emitNode st f lv v
                     | None ->
                         match baseRn with
                         | Some bn when i < baseLen ->
                             lg f bl
                             gcT f "ref.cast" ("$r_" + bn)
                             gcTF f "struct.get" ("$r_" + bn) i
                         | Some _ ->
                             err st ("binary: missing field " + fname + " in " + rn)
                             refNull f "any"
                         | None ->
                             lg f bl
                             gcT f "ref.cast" ("$r_" + rn)
                             gcTF f "struct.get" ("$r_" + rn) i)
             gcT f "struct.new" ("$r_" + rn)
         | None ->
             err st ("binary: record ext with unknown type " + rn)
             refNull f "any")
    | ECtor (name, _, _) when (dictTryFind st.EnumConst name).IsSome ->
        ic f (dictTryFind st.EnumConst name).Value
        callf f "$ofi"
    | ECtor (name, _, args) ->
        (match dictTryFind st.CaseArity name with
         | Some 0 -> gg f ("$c_" + name)
         | Some _ when not (List.isEmpty args) ->
             ic f (dictTryFind st.CaseTag name).Value
             (match args with
              | [ one ] -> emitNode st f lv one
              | many ->
                  err st "binary: multi-payload ctor not ported"
                  refNull f "any")
             gcT f "struct.new" "$du1"
         | Some 1 ->
             // the constructor as a VALUE (`|> Some`): a closure whose
             // function builds the case; body emitted with the wrapper tail
             if not (dictTryFind st.CtorFns name).IsSome then
                 dictSet st.CtorFns name true
                 vecAdd st.LateFns ("c:" + name)
                 declFn f.M ("$ctorfn_" + name) "$u1"
             rf f ("$ctorfn_" + name)
             refNull f "any"
             gcT f "struct.new" "$clo"
         | Some _ ->
             err st ("binary: unapplied multi-payload constructor " + name)
             refNull f "any"
         | _ ->
             err st ("binary: ctor shape not ported: " + name)
             refNull f "any")
    | EApp (EUnknown "print", [ a ]) ->
        emitNode st f lv a
        callf f "$printval"
        ic f 10
        callf f "$putc"
        ic f 0
        refI31 f
    | EApp (EUnknown "$str.Substring", [ s; start ]) ->
        let sl = freshLocal f "$sbs" "i32"
        let sv = freshLocal f "$sbv" "anyref"
        emitNode st f lv s
        ls f sv
        emitNode st f lv start
        callf f "$toi"
        ls f sl
        lg f sv
        gcT f "ref.cast" "$str"
        lg f sl
        lg f sv
        gcT f "ref.cast" "$str"
        gci f "array.len"
        lg f sl
        ins f "i32.sub"
        callf f "$strsub"
    | EApp (EUnknown "$str.Substring#2", [ s; start; len ])
    | EApp (EUnknown "strsub", [ s; start; len ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv start
        callf f "$toi"
        emitNode st f lv len
        callf f "$toi"
        callf f "$strsub"
    | EApp (EUnknown "$str.StartsWith", [ s; p ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv p
        gcT f "ref.cast" "$str"
        callf f "$strStarts"
        refI31 f
    | EApp (EUnknown "$str.EndsWith", [ s; p ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv p
        gcT f "ref.cast" "$str"
        callf f "$strEnds"
        refI31 f
    | EApp (EUnknown "$str.Contains", [ s; p ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv p
        gcT f "ref.cast" "$str"
        ic f 0
        callf f "$strFind"
        ic f 0
        ins f "i32.ge_s"
        refI31 f
    | EApp (EUnknown "$str.IndexOf", [ s; p ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv p
        gcT f "ref.cast" "$str"
        ic f 0
        callf f "$strFind"
        callf f "$ofi"
    | EApp (EUnknown "$str.IndexOf#2", [ s; c ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv c
        callf f "$toi"
        callf f "$strFindChar"
        callf f "$ofi"
    | EApp (EUnknown "$str.IndexOf#3", [ s; p; from ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv p
        gcT f "ref.cast" "$str"
        emitNode st f lv from
        callf f "$toi"
        callf f "$strFind"
        callf f "$ofi"
    | EApp (EUnknown "$str.LastIndexOf", [ s; c ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv c
        callf f "$toi"
        callf f "$strLastFindChar"
        callf f "$ofi"
    | EApp (EUnknown "$str.Split", [ s; c ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv c
        callf f "$toi"
        callf f "$strSplitChar"
    | EApp (EUnknown "$str.Replace", [ s; a; b ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv a
        gcT f "ref.cast" "$str"
        emitNode st f lv b
        gcT f "ref.cast" "$str"
        callf f "$strReplace"
    | EApp (EUnknown "$str.Trim", [ s ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        callf f "$strTrim"
    | EApp (EUnknown "$str.TrimEnd", [ s; cs ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv cs
        callf f "$strTrimEndChars"
    | EIfaceCall (iface, mname, recv, args) ->
        (match dictTryFind st.SlotOf (iface, mname) with
         | Some slot ->
             let t = freshLocal f "$dv" "anyref"
             let ft = "$v" + string (1 + List.length args)
             let dispatch () =
                 lg f t
                 for a in args do emitNode st f lv a
                 lg f t
                 gcT f "ref.cast" "$obj"
                 gcTF f "struct.get" "$obj" 0
                 gcT f "ref.cast" "$desc"
                 gcTF f "struct.get" "$desc" 1
                 ic f slot
                 gcT f "array.get" "$vt"
                 gcT f "ref.cast" ft
                 callRef f ft
             emitNode st f lv recv
             ls f t
             // lists and arrays ARE seqs but carry no vtable: pre-test the
             // representation and route to the built-in iterators
             if iface = "IEnumerable" && mname = "GetEnumerator" then
                 lg f t
                 callf f "$isBuiltinSeq"
                 ifA f
                 lg f t
                 callf f "$iterNew"
                 elseB f
                 dispatch ()
                 endB f
             elif iface = "IEnumerator" && (mname = "MoveNext" || mname = "Current") then
                 lg f t
                 gcT f "ref.test" "$iter"
                 ifA f
                 lg f t
                 callf f (if mname = "MoveNext" then "$iterNext" else "$iterCur")
                 elseB f
                 dispatch ()
                 endB f
             else dispatch ()
         | None ->
             err st ("binary: no dispatch slot for " + iface + "." + mname)
             refNull f "any")
    | ETypeTest (tn, e2) ->
        // list/array/string test their representation; a class tests its
        // descriptor id against itself and its subclasses; an interface
        // against its implementors. GUARDED: a non-object answers false.
        let t = freshLocal f "$bq" "anyref"
        emitNode st f lv e2
        ls f t
        let idOf () =
            lg f t
            gcT f "ref.cast" "$obj"
            gcTF f "struct.get" "$obj" 0
            gcT f "ref.cast" "$desc"
            gcTF f "struct.get" "$desc" 0
        let classIdTest (classes : string list) =
            let hits = classes |> List.filter (fun c -> (dictTryFind st.ObjRec c).IsSome)
            lg f t
            gcT f "ref.test" "$obj"
            ifV f "i32"
            (match hits with
             | [] -> ic f 0
             | first :: rest ->
                 idOf ()
                 ic f (dictTryFind st.DescIdOf first).Value
                 ins f "i32.eq"
                 for c in rest do
                     idOf ()
                     ic f (dictTryFind st.DescIdOf c).Value
                     ins f "i32.eq"
                     ins f "i32.or")
            elseB f
            ic f 0
            endB f
            refI31 f
        if tn = "list" then
            lg f t
            ins f "ref.is_null"
            lg f t
            gcT f "ref.test" "$cons"
            ins f "i32.or"
            refI31 f
        elif tn = "array" then
            lg f t
            callf f "$isArrayRep"
            refI31 f
        elif tn = "string" then
            lg f t
            gcT f "ref.test" "$str"
            refI31 f
        elif (dictTryFind st.ObjRec tn).IsSome then
            classIdTest (match dictTryFind st.SubsOf tn with Some s -> s | None -> [ tn ])
        elif (dictTryFind st.IfaceName tn).IsSome then
            classIdTest (match dictTryFind st.ImplsOf tn with Some s -> s | None -> [])
        else
            err st ("binary: cannot type-test against " + tn + ": not a class")
            refNull f "any"
    | ECast (_, e2, false) ->
        // widening: representation unchanged, nothing to do at runtime
        emitNode st f lv e2
    | ECast (tn, e2, true) ->
        // a downcast CHECKS (representation is uniform); null casts to null
        let t = freshLocal f "$bq" "anyref"
        emitNode st f lv e2
        ls f t
        let idOf () =
            lg f t
            gcT f "ref.cast" "$obj"
            gcTF f "struct.get" "$obj" 0
            gcT f "ref.cast" "$desc"
            gcTF f "struct.get" "$desc" 0
        let classIdTest (classes : string list) =
            let hits = classes |> List.filter (fun c -> (dictTryFind st.ObjRec c).IsSome)
            lg f t
            gcT f "ref.test" "$obj"
            ifV f "i32"
            (match hits with
             | [] -> ic f 0
             | first :: rest ->
                 idOf ()
                 ic f (dictTryFind st.DescIdOf first).Value
                 ins f "i32.eq"
                 for c in rest do
                     idOf ()
                     ic f (dictTryFind st.DescIdOf c).Value
                     ins f "i32.eq"
                     ins f "i32.or")
            elseB f
            ic f 0
            endB f
        let emitOk () =
            if tn = "list" then
                lg f t
                ins f "ref.is_null"
                lg f t
                gcT f "ref.test" "$cons"
                ins f "i32.or"
            elif tn = "array" then
                lg f t
                callf f "$isArrayRep"
            elif tn = "string" then
                lg f t
                gcT f "ref.test" "$str"
            elif tn = "seq" || tn = "IEnumerable" then
                lg f t
                callf f "$isBuiltinSeq"
                lg f t
                gcT f "ref.test" "$obj"
                ins f "i32.or"
            elif (dictTryFind st.IfaceName tn).IsSome then
                classIdTest (match dictTryFind st.ImplsOf tn with Some s -> s | None -> [])
            else
                classIdTest (match dictTryFind st.SubsOf tn with Some s -> s | None -> [ tn ])
        if not ((dictTryFind st.ObjRec tn).IsSome || (dictTryFind st.IfaceName tn).IsSome
                || tn = "list" || tn = "array" || tn = "string" || tn = "seq" || tn = "IEnumerable") then
            err st ("binary: cannot downcast to " + tn + ": not a class")
            refNull f "any"
        else
            lg f t
            ins f "ref.is_null"
            emitOk ()
            ins f "i32.or"
            ifA f
            lg f t
            elseB f
            (match dictTryFind st.CaseTag "InvalidCast" with
             | Some tg ->
                 ic f tg
                 emitNode st f lv (ELit (LString ("\"invalid cast to " + tn + "\"")))
                 gcT f "struct.new" "$du1"
                 throwExn f
             | None -> ins f "unreachable")
            endB f
    | EUnknown "hash" ->
        requestWrapper st f "$hashvBoxed" 1
        rf f "$hashvBoxed.w0"
        refNull f "any"
        gcT f "struct.new" "$clo"
    | EApp (EUnknown pd, [ a ]) when
        pd.StartsWith "pad0#" || pd.StartsWith "padl#" || pd.StartsWith "padr#" ->
        let width = pd.Substring 5
        emitNode st f lv a
        gcT f "ref.cast" "$str"
        ic f (int width)
        ic f (if pd.StartsWith "pad0#" then 48 else 32)
        ic f (if pd.StartsWith "padl#" then 1 else 0)
        callf f "$strPad"
    | EApp (EUnknown "compare", [ a; b ]) ->
        emitNode st f lv a
        emitNode st f lv b
        callf f "$cmpv"
        callf f "$ofi"
    | EApp (EUnknown "hash", [ a ]) ->
        emitNode st f lv a
        callf f "$hashv"
        callf f "$ofi"
    | EApp (EUnknown "refEq", [ a; b ]) ->
        emitNode st f lv a
        castEq f
        emitNode st f lv b
        castEq f
        ins f "ref.eq"
        refI31 f
    | EUnknown "$class:Ordered:compare:$ref" ->
        // `compare` at a UNIFORM reference: the runtime compares structurally
        requestWrapper st f "$cmpvBoxed" 2
        rf f "$cmpvBoxed.w0"
        refNull f "any"
        gcT f "struct.new" "$clo"
    | EApp (EUnknown n, [ a ]) when n.Contains "#" && not (n.StartsWith "pad") ->
        // conversions whose source kind inference resolved: target#srckind
        let target = n.Substring (0, n.IndexOf "#")
        let src = n.Substring (n.IndexOf "#" + 1)
        let emitA () = emitNode st f lv a
        let strA () = emitA (); gcT f "ref.cast" "$str"
        let mask8 () = ic f 255; ins f "i32.and"
        let sext8 () = ic f 24; ins f "i32.shl"; ic f 24; ins f "i32.shr_s"
        (match target, src with
         | "string", "t" -> emitA ()
         | "int", "t" | "uint32", "t" -> strA (); callf f "$atoi"; callf f "$ofi"
         | "int64", "t" -> strA (); callf f "$atol"; callf f "$ofl"
         | "byte", "t" -> strA (); callf f "$atoi"; mask8 (); callf f "$ofi"
         | "sbyte", "t" -> strA (); callf f "$atoi"; sext8 (); callf f "$ofi"
         | "float", "t" -> strA (); callf f "$atof"; callf f "$off"
         | "float32", "t" -> strA (); callf f "$atof"; ins f "f32.demote_f64"; callf f "$oss"
         | "char", "t" ->
             // Char.Parse: the single (first) character of the string
             strA (); ic f 0; gcT f "array.get_u" "$str"; callf f "$ofi"
         | "float16", "t" -> strA (); callf f "$atof"; ins f "f32.demote_f64"; callf f "$f2h"; callf f "$ofi"
         | "float16", "h" -> emitA ()
         | "float16", "f" -> emitA (); callf f "$tof"; callf f "$f2h64"; callf f "$ofi"
         | "float16", "s" -> emitA (); callf f "$tos"; callf f "$f2h"; callf f "$ofi"
         | "float16", "l" -> emitA (); callf f "$tol"; ins f "f32.convert_i64_s"; callf f "$f2h"; callf f "$ofi"
         | "float16", _ -> emitA (); callf f "$toi"; ins f "f32.convert_i32_s"; callf f "$f2h"; callf f "$ofi"
         | "string", "h" -> emitA (); callf f "$toi"; callf f "$h2f"; ins f "f64.promote_f32"; callf f "$ftoa"
         | "float", "h" -> emitA (); callf f "$toi"; callf f "$h2f"; ins f "f64.promote_f32"; callf f "$off"
         | "float32", "h" -> emitA (); callf f "$toi"; callf f "$h2f"; callf f "$oss"
         | "int64", "h" -> emitA (); callf f "$toi"; callf f "$h2f"; ins f "i64.trunc_f32_s"; callf f "$ofl"
         | _, "h" -> emitA (); callf f "$toi"; callf f "$h2f"; ins f "i32.trunc_f32_s"; callf f "$ofi"
         | "string", "f" -> emitA (); callf f "$tof"; callf f "$ftoa"
         | "string", "s" -> emitA (); callf f "$tos"; ins f "f64.promote_f32"; callf f "$ftoa"
         | "string", "l" -> emitA (); callf f "$tol"; callf f "$ltoa"
         | "string", "w" -> emitA (); callf f "$toi"; ins f "i64.extend_i32_u"; callf f "$ultoa"
         | "string", "b" ->
             // Boolean.ToString: "True"/"False", capital first
             emitA (); callf f "$toi"; ins f "i32.eqz"
             ifA f
             for c in [ 70; 97; 108; 115; 101 ] do ic f c
             arrNewFixed f "$str" 5
             elseB f
             for c in [ 84; 114; 117; 101 ] do ic f c
             arrNewFixed f "$str" 4
             endB f
         | "byte", "f" -> emitA (); callf f "$tof"; ins f "i32.trunc_f64_s"; mask8 (); callf f "$ofi"
         | "byte", "s" -> emitA (); callf f "$tos"; ins f "i32.trunc_f32_s"; mask8 (); callf f "$ofi"
         | "byte", "l" -> emitA (); callf f "$tol"; ins f "i32.wrap_i64"; mask8 (); callf f "$ofi"
         | "byte", _ -> emitA (); callf f "$toi"; mask8 (); callf f "$ofi"
         | "sbyte", "l" -> emitA (); callf f "$tol"; ins f "i32.wrap_i64"; sext8 (); callf f "$ofi"
         | "sbyte", _ -> emitA (); callf f "$toi"; sext8 (); callf f "$ofi"
         | "string", "c" -> emitA (); callf f "$toi"; ic f 1; gcT f "array.new" "$str"
         | "string", _ -> emitA (); callf f "$toi"; callf f "$itoa"
         | "float", "f" -> emitA ()
         | "float", "s" -> emitA (); callf f "$tos"; ins f "f64.promote_f32"; callf f "$off"
         | "float", "l" -> emitA (); callf f "$tol"; ins f "f64.convert_i64_s"; callf f "$off"
         | "float", _ -> emitA (); callf f "$toi"; ins f "f64.convert_i32_s"; callf f "$off"
         | "float32", "s" -> emitA ()
         | "float32", "f" -> emitA (); callf f "$tof"; ins f "f32.demote_f64"; callf f "$oss"
         | "float32", "l" -> emitA (); callf f "$tol"; ins f "f32.convert_i64_s"; callf f "$oss"
         | "float32", _ -> emitA (); callf f "$toi"; ins f "f32.convert_i32_s"; callf f "$oss"
         | "int64", "l" -> emitA ()
         | "int64", "f" -> emitA (); callf f "$tof"; ins f "i64.trunc_f64_s"; callf f "$ofl"
         | "int64", "s" -> emitA (); callf f "$tos"; ins f "i64.trunc_f32_s"; callf f "$ofl"
         | "int64", _ -> emitA (); callf f "$toi"; ins f "i64.extend_i32_s"; callf f "$ofl"
         | _, "l" -> emitA (); callf f "$tol"; ins f "i32.wrap_i64"; callf f "$ofi"
         | _, "f" -> emitA (); callf f "$tof"; ins f "i32.trunc_f64_s"; callf f "$ofi"
         | _, "s" -> emitA (); callf f "$tos"; ins f "i32.trunc_f32_s"; callf f "$ofi"
         | _, "t" ->
             err st ("binary: cannot convert a string to " + target)
             emitA ()
         | _, _ -> emitA ())
    | EApp (EUnknown "int64", [ a ]) ->
        (match kindOfLite st a with
         | "l" -> emitNode st f lv a
         | "f" -> emitNode st f lv a; callf f "$tof"; ins f "i64.trunc_f64_s"; callf f "$ofl"
         | "s" -> emitNode st f lv a; callf f "$tos"; ins f "i64.trunc_f32_s"; callf f "$ofl"
         | _ -> emitNode st f lv a; callf f "$toi"; ins f "i64.extend_i32_s"; callf f "$ofl")
    | EApp (EUnknown ("uint32" | "int"), [ a ]) ->
        (match kindOfLite st a with
         | "f" -> emitNode st f lv a; callf f "$tof"; ins f "i32.trunc_f64_s"; callf f "$ofi"
         | "s" -> emitNode st f lv a; callf f "$tos"; ins f "i32.trunc_f32_s"; callf f "$ofi"
         | "l" -> emitNode st f lv a; callf f "$tol"; ins f "i32.wrap_i64"; callf f "$ofi"
         | _ -> emitNode st f lv a)
    | EApp (EUnknown "string", [ a ]) ->
        (match kindOfLite st a with
         | "f" -> emitNode st f lv a; callf f "$tof"; callf f "$ftoa"
         | "s" -> emitNode st f lv a; callf f "$tos"; ins f "f64.promote_f32"; callf f "$ftoa"
         | "l" -> emitNode st f lv a; callf f "$tol"; callf f "$ltoa"
         | _ -> emitNode st f lv a; callf f "$toi"; callf f "$itoa")
    | EApp (EUnknown "float16#f", [ a ]) ->
        // a half is its bit pattern: round the double once, here
        emitNode st f lv a
        callf f "$tof"
        callf f "$f2h64"
        callf f "$ofi"
    | EApp (EUnknown "doubleBits", [ a ]) ->
        emitNode st f lv a
        callf f "$tof"
        ins f "i64.reinterpret_f64"
        callf f "$ofl"
    | EApp (EUnknown "singleBits", [ a ]) ->
        emitNode st f lv a
        callf f "$tos"
        ins f "i32.reinterpret_f32"
        callf f "$ofi"
    | EApp (EUnknown "hexlower", [ a ]) ->
        emitNode st f lv a
        callf f "$toi"
        ic f 16
        ic f 0
        callf f "$itobase"
    | EApp (EUnknown "hexupper", [ a ]) ->
        emitNode st f lv a
        callf f "$toi"
        ic f 16
        ic f 1
        callf f "$itobase"
    | EApp (EUnknown "octal", [ a ]) ->
        emitNode st f lv a
        callf f "$toi"
        ic f 8
        ic f 0
        callf f "$itobase"
    | EApp (EUnknown (("hexlower64" | "hexupper64" | "octal64") as fn), [ a ]) ->
        emitNode st f lv a
        callf f "$tol"
        lc f (if fn = "octal64" then 8L else 16L)
        ic f (if fn = "hexupper64" then 1 else 0)
        callf f "$ltobase"
    | EApp (EUnknown "fixed6", [ a ]) ->
        emitNode st f lv a
        callf f "$tof"
        callf f "$ftoa6"
    | EApp (EUnknown "showv", [ a ]) ->
        emitNode st f lv a
        callf f "$showv"
    | EApp (EUnknown "printu", [ a ]) ->
        // an unsigned value prints unsigned: widen the bit pattern
        emitNode st f lv a
        callf f "$toi"
        ins f "i64.extend_i32_u"
        callf f "$ultoa"
        gcT f "ref.cast" "$str"
        callf f "$prints"
        ic f 10
        callf f "$putc"
        ic f 0
        refI31 f
    | EApp (EUnknown "printb", [ a ]) ->
        // Boolean.ToString spells it with a capital
        emitNode st f lv a
        callf f "$toi"
        ins f "i32.eqz"
        ifE f
        for c in [ 70; 97; 108; 115; 101 ] do ic f c
        arrNewFixed f "$str" 5
        callf f "$prints"
        elseB f
        for c in [ 84; 114; 117; 101 ] do ic f c
        arrNewFixed f "$str" 4
        callf f "$prints"
        endB f
        ic f 10
        callf f "$putc"
        ic f 0
        refI31 f
    | EApp (EUnknown "printc", [ a ]) ->
        // a char prints as the character, not its code
        emitNode st f lv a
        callf f "$toi"
        callf f "$putc"
        ic f 10
        callf f "$putc"
        ic f 0
        refI31 f
    | EApp (EUnknown "prints", [ a ]) ->
        emitNode st f lv a
        gcT f "ref.cast" "$str"
        callf f "$prints"
        ic f 0
        refI31 f
    | EPrim ("+", [ a; b ]) when kindOfLite st a = "i" && kindOfLite st b = "i" ->
        // both sides statically int: skip $addv's runtime dispatch — and on
        // rail operands the un/box pairs cancel to a bare i32.add
        emitNode st f lv a
        callf f "$toi"
        emitNode st f lv b
        callf f "$toi"
        ins f "i32.add"
        callf f "$ofi"
    | EPrim ("+", [ a; b ]) ->
        emitNode st f lv a
        emitNode st f lv b
        callf f "$addv"
    | EPrim ("=", [ a; b ]) ->
        emitNode st f lv a
        emitNode st f lv b
        callf f "$equal"
    | EPrim (op, [ a; b ]) when List.contains op [ "-"; "*"; "/"; "%" ] ->
        let insn =
            match op with
            | "-" -> "i32.sub" | "*" -> "i32.mul" | "%" -> "i32.rem_s" | _ -> "i32.div_s"
        emitNode st f lv a
        callf f "$toi"
        emitNode st f lv b
        callf f "$toi"
        ins f insn
        callf f "$ofi"
    | EPrim (op, [ a; b ]) when List.contains op [ "<"; ">"; "<="; ">=" ] ->
        let insn = match op with "<" -> "i32.lt_s" | ">" -> "i32.gt_s" | "<=" -> "i32.le_s" | _ -> "i32.ge_s"
        emitNode st f lv a
        callf f "$toi"
        emitNode st f lv b
        callf f "$toi"
        ins f insn
        refI31 f
    | EPrim ("<>", [ a; b ]) ->
        emitNode st f lv a
        emitNode st f lv b
        callf f "$equal"
        gcAbs f "ref.cast" "i31"
        i31get f
        ins f "i32.eqz"
        refI31 f
    | EPrim ("::", [ a; b ]) ->
        emitNode st f lv a
        emitNode st f lv b
        gcT f "struct.new" "$cons"
    | EPrim ("@", [ a; b ]) ->
        emitNode st f lv a
        emitNode st f lv b
        callf f "$append"
    | EPrim ("&&", [ a; b ]) -> emitNode st f lv (EIf (a, b, ELit (LBool false)))
    | EPrim ("||", [ a; b ]) -> emitNode st f lv (EIf (a, ELit (LBool true), b))
    | EPrim ("u-", [ a ]) ->
        ic f 0
        emitNode st f lv a
        callf f "$toi"
        ins f "i32.sub"
        callf f "$ofi"
    | EPrim ("unot", [ a ]) ->
        emitNode st f lv a
        callf f "$toi"
        ins f "i32.eqz"
        refI31 f
    | EPrim (op, [ a; b ]) when
        op.Length > 1 && op.EndsWith "t"
        && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "<"; ">"; "<="; ">=" ] ->
        // `+` concatenates; ordering is byte-wise ordinal, like F#'s `<`
        emitNode st f lv a
        gcT f "ref.cast" "$str"
        emitNode st f lv b
        gcT f "ref.cast" "$str"
        (match op.Substring (0, op.Length - 1) with
         | "+" -> callf f "$strcat"
         | baseOp ->
             callf f "$strcmp"
             ic f 0
             ins f (match baseOp with
                    | "<" -> "i32.lt_s" | ">" -> "i32.gt_s"
                    | "<=" -> "i32.le_s" | _ -> "i32.ge_s")
             refI31 f)
    | EPrim (op, [ a; b ]) when
        op.Length > 1
        && (op.EndsWith "f" || op.EndsWith "s" || op.EndsWith "l" || op.EndsWith "i")
        && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "-"; "*"; "/"; "%"; "<"; ">"; "<="; ">=" ] ->
        let baseOp = op.Substring (0, op.Length - 1)
        let kind = op.Substring (op.Length - 1)
        let un, box_, ty, flt =
            match kind with
            | "f" -> "$tof", "$off", "f64", true
            | "s" -> "$tos", "$oss", "f32", true
            | "l" -> "$tol", "$ofl", "i64", false
            | _ -> "$toi", "$ofi", "i32", false
        if baseOp = "%" && flt then
            err st "binary: float remainder unsupported"
            refNull f "any"
        else
            emitNode st f lv a
            callf f un
            emitNode st f lv b
            callf f un
            let cmp = List.contains baseOp [ "<"; ">"; "<="; ">=" ]
            let insn =
                match baseOp with
                | "+" -> ty + ".add" | "-" -> ty + ".sub" | "*" -> ty + ".mul"
                | "/" -> if flt then ty + ".div" else ty + ".div_s"
                | "%" -> ty + ".rem_s"
                | "<" -> if flt then ty + ".lt" else ty + ".lt_s"
                | ">" -> if flt then ty + ".gt" else ty + ".gt_s"
                | "<=" -> if flt then ty + ".le" else ty + ".le_s"
                | _ -> if flt then ty + ".ge" else ty + ".ge_s"
            ins f insn
            if cmp then refI31 f else callf f box_
    | EPrim (op, [ a; b ]) when
        op.Length > 1 && op.EndsWith "w"
        && List.contains (op.Substring (0, op.Length - 1))
            [ "+"; "-"; "*"; "/"; "%"; "<"; ">"; "<="; ">="; "&&&"; "|||"; "^^^"; "<<<"; ">>>" ] ->
        // the UNSIGNED int family: uint32 semantics on the i32 rail
        let baseOp = op.Substring (0, op.Length - 1)
        emitNode st f lv a
        callf f "$toi"
        emitNode st f lv b
        callf f "$toi"
        let cmp = List.contains baseOp [ "<"; ">"; "<="; ">=" ]
        let insn =
            match baseOp with
            | "+" -> "i32.add" | "-" -> "i32.sub" | "*" -> "i32.mul"
            | "/" -> "i32.div_u" | "%" -> "i32.rem_u"
            | "<" -> "i32.lt_u" | ">" -> "i32.gt_u" | "<=" -> "i32.le_u" | ">=" -> "i32.ge_u"
            | "&&&" -> "i32.and" | "|||" -> "i32.or" | "^^^" -> "i32.xor"
            | "<<<" -> "i32.shl" | _ -> "i32.shr_u"
        ins f insn
        if cmp then refI31 f else callf f "$ofi"
    | EPrim (op, [ a; b ]) when
        op.Length > 1 && op.EndsWith "l"
        && List.contains (op.Substring (0, op.Length - 1)) [ "&&&"; "|||"; "^^^"; "<<<"; ">>>" ] ->
        let baseOp = op.Substring (0, op.Length - 1)
        emitNode st f lv a
        callf f "$tol"
        emitNode st f lv b
        (match baseOp with
         | "<<<" | ">>>" ->
             // the shift count is an int
             callf f "$toi"
             ins f "i64.extend_i32_s"
         | _ -> callf f "$tol")
        ins f (match baseOp with
               | "&&&" -> "i64.and" | "|||" -> "i64.or" | "^^^" -> "i64.xor"
               | "<<<" -> "i64.shl" | _ -> "i64.shr_s")
        callf f "$ofl"
    | EPrim (op, [ a; b ]) when List.contains op [ "&&&"; "|||"; "^^^"; "<<<"; ">>>" ] ->
        emitNode st f lv a
        callf f "$toi"
        emitNode st f lv b
        callf f "$toi"
        ins f (match op with
               | "&&&" -> "i32.and" | "|||" -> "i32.or" | "^^^" -> "i32.xor"
               // bare >>> on int is ARITHMETIC, as F#'s — the unsigned
               // family carries the `w` suffix
               | "<<<" -> "i32.shl" | _ -> "i32.shr_s")
        callf f "$ofi"
    | EPrim (op, [ a; b ]) when
        op.Length > 1 && op.EndsWith "h"
        && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "-"; "*"; "/"; "<"; ">"; "<="; ">="; "="; "<>" ] ->
        // float16: widen, operate in f32, round back — ONE rounding, and
        // therefore the correctly-rounded f16 answer. IEEE equality: -0.0h
        // equals 0.0h, a NaN half equals nothing
        let baseOp = op.Substring (0, op.Length - 1)
        emitNode st f lv a
        callf f "$toi"
        callf f "$h2f"
        emitNode st f lv b
        callf f "$toi"
        callf f "$h2f"
        (match baseOp with
         | "+" | "-" | "*" | "/" ->
             ins f ("f32." + (match baseOp with "+" -> "add" | "-" -> "sub" | "*" -> "mul" | _ -> "div"))
             callf f "$f2h"
             callf f "$ofi"
         | _ ->
             ins f ("f32." + (match baseOp with
                              | "<" -> "lt" | ">" -> "gt" | "<=" -> "le"
                              | "=" -> "eq" | "<>" -> "ne" | _ -> "ge"))
             refI31 f)
    | EPrim (("sqrth" | "absh" | "truncateh" | "u-h") as op, [ a ]) ->
        emitNode st f lv a
        callf f "$toi"
        callf f "$h2f"
        ins f (match op with
               | "sqrth" -> "f32.sqrt" | "absh" -> "f32.abs"
               | "truncateh" -> "f32.trunc" | _ -> "f32.neg")
        callf f "$f2h"
        callf f "$ofi"
    | EApp (EUnknown "printh", [ a ]) ->
        // a half is an i31 at runtime, so printing needs the STATIC type
        emitNode st f lv a
        callf f "$toi"
        callf f "$h2f"
        callf f "$oss"
        callf f "$printval"
        ic f 10
        callf f "$putc"
        ic f 0
        refI31 f
    | EPrim ("u-f", [ a ]) ->
        emitNode st f lv a
        callf f "$tof"
        ins f "f64.neg"
        callf f "$off"
    | EPrim ("u-s", [ a ]) ->
        emitNode st f lv a
        callf f "$tos"
        ins f "f32.neg"
        callf f "$oss"
    | EPrim ("u-l", [ a ]) ->
        lc f 0L
        emitNode st f lv a
        callf f "$tol"
        ins f "i64.sub"
        callf f "$ofl"
    | EPrim ("u~~~", [ a ]) ->
        emitNode st f lv a
        callf f "$toi"
        ic f -1
        ins f "i32.xor"
        callf f "$ofi"
    | EPrim (("sqrtf" | "sqrts" | "absf" | "abss" | "truncatef" | "truncates") as op, [ a ]) ->
        // the INSTRUCTION rather than `if x < 0 then -x`: that form gets
        // -0.0 and NaN wrong
        let f32 = op.EndsWith "s"
        let ty = if f32 then "f32" else "f64"
        emitNode st f lv a
        callf f (if f32 then "$tos" else "$tof")
        ins f (if op.StartsWith "sqrt" then ty + ".sqrt"
               elif op.StartsWith "abs" then ty + ".abs"
               else ty + ".trunc")
        callf f (if f32 then "$oss" else "$off")
    | EPrim ("abs", [ a ]) ->
        let l = freshLocal f "$bn" "i32"
        emitNode st f lv a
        callf f "$toi"
        ls f l
        ic f 0
        lg f l
        ins f "i32.sub"
        lg f l
        lg f l
        ic f 0
        ins f "i32.lt_s"
        ins f "select"
        callf f "$ofi"
    | EPrim ("absl", [ a ]) ->
        let l = freshLocal f "$bnl" "i64"
        emitNode st f lv a
        callf f "$tol"
        ls f l
        lc f 0L
        lg f l
        ins f "i64.sub"
        lg f l
        lg f l
        lc f 0L
        ins f "i64.lt_s"
        ins f "select"
        callf f "$ofl"
    | ERecord (tyName, fields) ->
        let rn =
            if tyName <> "" && tyName <> "?" && (dictTryFind st.FieldsOf tyName).IsSome then tyName
            else
                match fields |> List.tryPick (fun (fn, _) -> dictTryFind st.FieldOwner fn) with
                | Some r -> r
                | None -> ""
        (match dictTryFind st.FieldsOf rn with
         | Some order ->
             for fname in order do
                 (match fields |> List.tryFind (fun (fn, _) -> fn = fname) with
                  | Some (_, v) -> emitNode st f lv v
                  | None when fname = "__desc" && (dictTryFind st.ObjRec rn).IsSome ->
                      gg f ("$desc_" + rn)
                  | None when fname = "__idhash" ->
                      ic f 0
                      refI31 f
                  | None ->
                      err st ("binary: missing field " + fname + " in " + rn)
                      refNull f "any")
             gcT f "struct.new" ("$r_" + rn)
         | None ->
             err st ("binary: record with unknown type " + tyName)
             refNull f "any")
    | EField (EIndex (nm, a, i), fname, _) when
          (dictTryFind st.Pod nm).IsSome
          && ((dictTryFind st.Pod nm).Value |> fun (placed, _, _) -> placed |> List.exists (fun (p, _, _) -> p = fname)) ->
        // fusion: pts.[i].X reads ONE word out of the C image — no struct
        // materialization, one box instead of the whole element
        let placed, _, wd = (dictTryFind st.Pod nm).Value
        let _, k, off = placed |> List.find (fun (p, _, _) -> p = fname)
        emitNode st f lv a
        emitNode st f lv i
        callf f "$toi"
        ic f wd
        ins f "i32.mul"
        ic f (off / 8)
        ins f "i32.add"
        callf f "$hwget"
        let sh = (off % 8) * 8
        (match k with
         | "f" ->
             ins f "f64.reinterpret_i64"
             callf f "$off"
         | "l" -> callf f "$ofl"
         | "s" ->
             (if sh <> 0 then
                 lc f (int64 sh)
                 ins f "i64.shr_u")
             ins f "i32.wrap_i64"
             ins f "f32.reinterpret_i32"
             callf f "$oss"
         | _ ->
             (if sh <> 0 then
                 lc f (int64 sh)
                 ins f "i64.shr_u")
             ins f "i32.wrap_i64"
             callf f "$ofi")
    | EField (r, "Length", _) when not (dictTryFind st.FieldOwner "Length").IsSome ->
        // no record claims a Length field: this is the built-in one, across
        // strings and every array representation
        emitNode st f lv r
        callf f "$lenv"
    | EField (r, fname, owner) ->
        let rn =
            if owner <> "" && (dictTryFind st.FieldIdx (owner, fname)).IsSome then owner
            else (match dictTryFind st.FieldOwner fname with Some x -> x | None -> "")
        (match dictTryFind st.FieldIdx (rn, fname) with
         | Some idx ->
             emitNode st f lv r
             gcT f "ref.cast" ("$r_" + rn)
             gcTF f "struct.get" ("$r_" + rn) idx
         | None ->
             err st ("binary: unknown field " + fname)
             refNull f "any")
    | EFieldSet (r, fname, owner, v) ->
        let rn =
            if owner <> "" && (dictTryFind st.FieldIdx (owner, fname)).IsSome then owner
            else (match dictTryFind st.FieldOwner fname with Some x -> x | None -> "")
        (match dictTryFind st.FieldIdx (rn, fname) with
         | Some idx ->
             emitNode st f lv r
             gcT f "ref.cast" ("$r_" + rn)
             emitNode st f lv v
             gcTF f "struct.set" ("$r_" + rn) idx
             ic f 0
             refI31 f
         | None ->
             err st ("binary: unknown field " + fname)
             refNull f "any")
    | ETuple xs ->
        for x in xs do emitNode st f lv x
        gcT f "struct.new" ("$tup" + string (List.length xs))
    | EListLit xs ->
        for x in xs do emitNode st f lv x
        refNull f "any"
        for _ in xs do gcT f "struct.new" "$cons"
    | EApp ((EVar (v, _) | EVarI (v, _, _)), args) when
          (dictTryFind st.ArityOf (v.Path, v.Offset)) = Some (List.length args) ->
        let fn = (dictTryFind st.FnOf (v.Path, v.Offset)).Value
        (match dictTryFind st.Externs (v.Path, v.Offset) with
         | Some (pks, rk) ->
             // FFI boundary: ints cross as raw i32, references pass opaque
             for k, a in List.zip pks args do
                 emitNode st f lv a
                 if k = "i" then callf f "$toi"
             callf f fn
             if rk = "i" then callf f "$ofi"
         | None ->
             let pks, rk =
                 match dictTryFind st.SigKinds (v.Path, v.Offset) with
                 | Some (p, r) -> p, r
                 | None -> (args |> List.map (fun _ -> "u")), "u"
             for k, a in List.zip pks args do
                 emitNode st f lv a
                 if k <> "u" then callf f (unboxOfK k)
             // a marked tail call returns the callee's result as ours — no
             // frame grows; legal only when the return kinds AGREE, because
             // the frame that would re-box is gone
             if (refMapTryFind st.TailApp e).IsSome && rk = st.CurRet then
                 retCall f fn
             else
                 callf f fn
                 if rk <> "u" then callf f (boxOfK rk))
    | EAssign (v, rhs) when (dictTryFind st.CellVars (v.Path, v.Offset)).IsSome ->
        // the cell may live in this frame or in the closure's env; both reads
        // yield the SAME cell, and the write goes through it
        (match dictTryFind lv (v.Path, v.Offset) with
         | Some l when l.StartsWith "@env:" ->
             lg f "$env"
             gcT f "ref.cast" "$arr"
             ic f (int (l.Substring 5))
             gcT f "array.get" "$arr"
         | Some l -> lg f l
         | None ->
             err st ("binary: cell not in scope: " + v.Name)
             refNull f "any")
        gcT f "ref.cast" "$cell"
        emitNode st f lv rhs
        gcTF f "struct.set" "$cell" 0
        ic f 0
        refI31 f
    | EAssign (v, rhs) ->
        (match dictTryFind lv (v.Path, v.Offset) with
         | Some l when not (l.StartsWith "@env:") ->
             emitNode st f lv rhs
             (match dictTryFind st.LocalKind (v.Path, v.Offset) with
              | Some k -> callf f (unboxOfK k)
              | None -> ())
             ls f l
         | Some _ ->
             err st "binary: captured mutable (cells) not ported"
         | None ->
             match dictTryFind st.GlobalOf (v.Path, v.Offset) with
             | Some g ->
                 emitNode st f lv rhs
                 gs f g
             | None -> err st ("binary: assignment to unknown " + v.Name))
        ic f 0
        refI31 f
    | EWhile (c, b) ->
        blockE f "$wbrk"
        loopE f "$wgo"
        emitNode st f lv c
        callf f "$toi"
        ins f "i32.eqz"
        brIf f "$wbrk"
        emitNode st f lv b
        ins f "drop"
        br f "$wgo"
        endB f
        endB f
        ic f 0
        refI31 f
    | EApp (EUnknown "failwith", [ a ]) ->
        // the payload is Failure(msg), so `with Failure msg` matches it
        (match dictTryFind st.CaseTag "Failure" with
         | Some tg ->
             ic f tg
             emitNode st f lv a
             gcT f "struct.new" "$du1"
         | None -> emitNode st f lv a)
        throwExn f
        ic f 0
        refI31 f
    | EApp (EUnknown "raise", [ a ]) ->
        emitNode st f lv a
        throwExn f
        ic f 0
        refI31 f
    | EApp (EUnknown "ignore", [ a ]) ->
        emitNode st f lv a
        ins f "drop"
        ic f 0
        refI31 f
    | EApp (EUnknown "isNull", [ a ]) ->
        emitNode st f lv a
        ins f "ref.is_null"
        refI31 f
    | EApp (EUnknown "$listLength", [ a ]) ->
        // inline: walk the cons chain counting (the runtime's $listLength
        // moves here once more programs demand it)
        let cl = freshLocal f "$ll" "anyref"
        let cn = freshLocal f "$lc" "anyref"
        emitNode st f lv a
        ls f cl
        ic f 0
        refI31 f
        ls f cn
        blockE f "$ldone"
        loopE f "$lgo"
        lg f cl
        ins f "ref.is_null"
        brIf f "$ldone"
        lg f cn
        callf f "$toi"
        ic f 1
        ins f "i32.add"
        callf f "$ofi"
        ls f cn
        lg f cl
        gcT f "ref.cast" "$cons"
        gcTF f "struct.get" "$cons" 1
        ls f cl
        br f "$lgo"
        endB f
        endB f
        lg f cn
    // ---- arrays: UNIFORM $arr (anyref elements) ---------------------------
    // The element-kind name is carried but ignored: the binary path stays
    // uniform until the oracle is green, and packed/POD parity is its own
    // pass afterwards. Every element is therefore a boxed anyref, exactly
    // like a closure env slot.
    | EArray (nm, xs) when (dictTryFind st.Pod nm).IsSome ->
        // C-image packed: N elements x strideWords i64 words, in a handle
        let _, _, wd = (dictTryFind st.Pod nm).Value
        for x in xs do
            let el = freshLocal f "$pke" "anyref"
            emitNode st f lv x
            ls f el
            for w in 0 .. wd - 1 do emitPodWord st f nm el w
        arrNewFixed f "$pk" (List.length xs * wd)
        ic f 0
        ic f 0
        gcT f "struct.new" "$hnd"
    | EIndex (nm, a, i) when (dictTryFind st.Pod nm).IsSome ->
        let _, _, wd = (dictTryFind st.Pod nm).Value
        let hl = freshLocal f "$pha" "anyref"
        let bl = freshLocal f "$phb" "i32"
        emitNode st f lv a
        ls f hl
        emitNode st f lv i
        callf f "$toi"
        ic f wd
        ins f "i32.mul"
        ls f bl
        emitPodBuild st f nm hl bl nm ""
    | EIndexSet (nm, a, i, v) when (dictTryFind st.Pod nm).IsSome ->
        let _, _, wd = (dictTryFind st.Pod nm).Value
        let hl = freshLocal f "$pha" "anyref"
        let bl = freshLocal f "$phb" "i32"
        let vl = freshLocal f "$phv" "anyref"
        emitNode st f lv a
        ls f hl
        emitNode st f lv i
        callf f "$toi"
        ic f wd
        ins f "i32.mul"
        ls f bl
        emitNode st f lv v
        ls f vl
        for w in 0 .. wd - 1 do
            lg f hl
            lg f bl
            ic f w
            ins f "i32.add"
            emitPodWord st f nm vl w
            callf f "$hwset"
        ic f 0
        refI31 f
    | EArrayCreate (nm, n, EUnknown "$zero") when (dictTryFind st.Pod nm).IsSome ->
        let _, _, wd = (dictTryFind st.Pod nm).Value
        emitNode st f lv n
        callf f "$toi"
        ic f wd
        ins f "i32.mul"
        gcT f "array.new_default" "$pk"
        ic f 0
        ic f 0
        gcT f "struct.new" "$hnd"
    | EArrayCreate (nm, n, v) when (dictTryFind st.Pod nm).IsSome ->
        let _, _, wd = (dictTryFind st.Pod nm).Value
        let nl = freshLocal f "$pkn" "i32"
        let vl = freshLocal f "$pkv" "anyref"
        let al = freshLocal f "$pka" "anyref"
        let jl = freshLocal f "$pkj" "i32"
        emitNode st f lv n
        callf f "$toi"
        ls f nl
        emitNode st f lv v
        ls f vl
        lg f nl
        ic f wd
        ins f "i32.mul"
        gcT f "array.new_default" "$pk"
        ic f 0
        ic f 0
        gcT f "struct.new" "$hnd"
        ls f al
        ic f 0
        ls f jl
        blockE f "$pkd"
        loopE f "$pkl"
        lg f jl
        lg f nl
        ins f "i32.ge_u"
        brIf f "$pkd"
        for w in 0 .. wd - 1 do
            lg f al
            lg f jl
            ic f wd
            ins f "i32.mul"
            ic f w
            ins f "i32.add"
            emitPodWord st f nm vl w
            callf f "$hwset"
        lg f jl
        ic f 1
        ins f "i32.add"
        ls f jl
        br f "$pkl"
        endB f
        endB f
        lg f al
    | EArrayLen (nm, a) when (dictTryFind st.Pod nm).IsSome ->
        let _, _, wd = (dictTryFind st.Pod nm).Value
        emitNode st f lv a
        callf f "$hlen"
        ic f wd
        ins f "i32.div_u"
        callf f "$ofi"
    | EArrayPin (nm, a) ->
        (if (dictTryFind st.Pod nm).IsSome then
            emitNode st f lv a
            callf f "$pinh"
            callf f "$ofi"
         else
            err st "binary: Array.pin requires a POD struct array"
            refNull f "any")
    | EArrayUnpin (nm, a) ->
        (if (dictTryFind st.Pod nm).IsSome then
            emitNode st f lv a
            callf f "$unpinh"
            callf f "$ofi"
         else
            err st "binary: Array.unpin requires a POD struct array"
            refNull f "any")
    | EArray (nm, xs) when parrK nm <> "" ->
        // packed primitive array: unboxed elements, no per-element GC object
        let k = parrK nm
        for x in xs do
            emitNode st f lv x
            callf f (unboxOfK k)
        arrNewFixed f (parrTy k) (List.length xs)
    | EIndex (nm, a, i) when parrK nm <> "" ->
        let k = parrK nm
        emitNode st f lv a
        gcT f "ref.cast" (parrTy k)
        emitNode st f lv i
        callf f "$toi"
        gcT f (getOpOfK k) (parrTy k)
        callf f (boxOfK k)
    | EIndexSet (nm, a, i, v) when parrK nm <> "" ->
        let k = parrK nm
        emitNode st f lv a
        gcT f "ref.cast" (parrTy k)
        emitNode st f lv i
        callf f "$toi"
        emitNode st f lv v
        callf f (unboxOfK k)
        gcT f "array.set" (parrTy k)
        ic f 0
        refI31 f
    | EArrayCreate (nm, n, EUnknown "$zero") when parrK nm <> "" ->
        emitNode st f lv n
        callf f "$toi"
        gcT f "array.new_default" (parrTy (parrK nm))
    | EArrayCreate (nm, n, v) when parrK nm <> "" ->
        let k = parrK nm
        emitNode st f lv v
        callf f (unboxOfK k)
        emitNode st f lv n
        callf f "$toi"
        gcT f "array.new" (parrTy k)
    | EArray (("byte" | "sbyte"), xs) ->
        for x in xs do
            emitNode st f lv x
            callf f "$toi"
        arrNewFixed f "$str" (List.length xs)
    | EArray (_, xs) ->
        for x in xs do emitNode st f lv x
        arrNewFixed f "$arr" (List.length xs)
    | EArrayCreate (("byte" | "sbyte"), n, EUnknown "$zero") ->
        // packed i8 array, zeroed — same representation as a string
        emitNode st f lv n
        callf f "$toi"
        gcT f "array.new_default" "$str"
    | EArrayCreate (("byte" | "sbyte"), n, v) ->
        emitNode st f lv v
        callf f "$toi"
        emitNode st f lv n
        callf f "$toi"
        gcT f "array.new" "$str"
    | EArrayCreate (nm, n, EUnknown "$zero") ->
        // Array.zeroCreate. `array.new_default` would give NULL in every
        // slot, which is right for a reference element and wrong for a
        // numeric one — uniform boxing means a zero int is `ref.i31 0`, not
        // null. So the zero is spelled per element kind and filled by
        // array.new.
        (match nm with
         | "float" | "float32" | "double" | "single" ->
             fc f 0L
             gcT f "struct.new" "$boxf"
         | "string" | "obj" | "" -> refNull f "any"
         | _ when strLen nm > 0 && charAt nm 0 = '\'' -> refNull f "any"
         | _ ->
             ic f 0
             refI31 f)
        emitNode st f lv n
        callf f "$toi"
        gcT f "array.new" "$arr"
    | EArrayCreate (_, n, v) ->
        // array.new takes the INIT VALUE first, then the length
        emitNode st f lv v
        emitNode st f lv n
        callf f "$toi"
        gcT f "array.new" "$arr"
    | EIndex ("$str", a, i) ->
        // char access on a STRING receiver (the "$str" sentinel)
        emitNode st f lv a
        gcT f "ref.cast" "$str"
        emitNode st f lv i
        callf f "$toi"
        gcT f "array.get_u" "$str"
        refI31 f
    | EIndex (("byte" | "sbyte") as nm, a, i) ->
        // byte[]/sbyte[] share the packed i8 representation with strings —
        // that identity is what stringBytes/bytesString rely on
        emitNode st f lv a
        gcT f "ref.cast" "$str"
        emitNode st f lv i
        callf f "$toi"
        gcT f (if nm = "byte" then "array.get_u" else "array.get_s") "$str"
        callf f "$ofi"
    | EIndexSet (("byte" | "sbyte"), a, i, v) ->
        emitNode st f lv a
        gcT f "ref.cast" "$str"
        emitNode st f lv i
        callf f "$toi"
        emitNode st f lv v
        callf f "$toi"
        gcT f "array.set" "$str"
        ic f 0
        refI31 f
    | EIndex (_, a, i) ->
        emitNode st f lv a
        gcT f "ref.cast" "$arr"
        emitNode st f lv i
        callf f "$toi"
        gcT f "array.get" "$arr"
    | EIndexSet (_, a, i, v) ->
        emitNode st f lv a
        gcT f "ref.cast" "$arr"
        emitNode st f lv i
        callf f "$toi"
        emitNode st f lv v
        gcT f "array.set" "$arr"
        ic f 0
        refI31 f
    | EArrayLen (_, a) ->
        // representation-dispatched: the receiver may be $arr OR $str (byte
        // strings and arrays share the length surface)
        emitNode st f lv a
        callf f "$lenv"
    | ELam (_, _) ->
        (match refMapTryFind st.LamName e with
         | Some name ->
             // (struct.new $clo (ref.func $lam) env) — env slots hold the
             // CURRENT values of the captured locals, read here at build
             let free = (dictTryFind st.LamFree name).Value
             rf f name
             if List.isEmpty free then refNull f "any"
             else
                 for k in free do
                     (match dictTryFind lv k with
                      | Some l when l.StartsWith "@env:" ->
                          lg f "$env"
                          gcT f "ref.cast" "$arr"
                          ic f (int (l.Substring 5))
                          gcT f "array.get" "$arr"
                      | Some l -> lg f l
                      | None ->
                          err st ("binary: capture not in scope at build site: " + fst k + "@" + string (snd k))
                          refNull f "any")
                 arrNewFixed f "$arr" (List.length free)
             gcT f "struct.new" "$clo"
         | None ->
             err st "binary: undiscovered lambda"
             refNull f "any")
    | EApp (g, args) ->
        // generic application: the applyc chain
        emitNode st f lv g
        for a in args do
            emitNode st f lv a
            callf f "$applyc"
    | other ->
        let tag =
            match other with
            | ELam _ -> "ELam" | EApp (EUnknown n, _) -> "EApp $" + n
            | EApp _ -> "EApp" | EPrim (op, _) -> "EPrim " + op
            | EField _ -> "EField" | EFieldSet _ -> "EFieldSet"
            | ERecord _ -> "ERecord" | ERecordExt _ -> "ERecordExt"
            | EIndex _ -> "EIndex" | EIndexSet _ -> "EIndexSet"
            | EArray _ -> "EArray" | EArrayLen _ -> "EArrayLen"
            | EArrayCreate _ -> "EArrayCreate" | EWhile _ -> "EWhile"
            | EAssign _ -> "EAssign" | ETry _ -> "ETry"
            | EIfaceCall _ -> "EIfaceCall" | ECast _ -> "ECast"
            | ETypeTest _ -> "ETypeTest" | ETuple _ -> "ETuple"
            | EListLit _ -> "EListLit" | EUnknown n -> "EUnknown " + n
            | _ -> "?"
        err st ("binary: not ported: " + tag)
        refNull f "any"

and private emitPat (st : St) (f : Fn) (lv : Dict<string * int, string>)
                    (failLbl : string) (slot : string) (p : Pat) : unit =
    match p with
    | PWild -> ()
    | PVar (v, _) ->
        // or-alternatives bind the SAME identity: whichever alternative
        // matches must write the one slot the shared body reads, so a
        // binder already in scope reuses its slot instead of shadowing it
        let l =
            match dictTryFind lv (v.Path, v.Offset) with
            | Some ex when not (ex.StartsWith "@env:") -> ex
            | _ ->
                let l = freshLocal f "$bp" "anyref"
                dictSet lv (v.Path, v.Offset) l
                l
        lg f slot
        ls f l
    | PLit (LInt sIn) ->
        let digits = sIn |> String.filter (fun c -> isDigit c || c = '-')
        lg f slot
        callf f "$toi"
        ic f (if digits = "" then 0 else int digits)
        ins f "i32.ne"
        brIf f failLbl
    | PLit (LBool b) ->
        lg f slot
        callf f "$toi"
        ic f (if b then 1 else 0)
        ins f "i32.ne"
        brIf f failLbl
    | PCtor (name, _, args) ->
        (match dictTryFind st.CaseArity name, dictTryFind st.CaseTag name with
         | Some 0, Some t ->
             lg f slot
             gcT f "ref.test" "$du0"
             ins f "i32.eqz"
             brIf f failLbl
             lg f slot
             gcT f "ref.cast" "$du0"
             gcTF f "struct.get" "$du0" 0
             ic f t
             ins f "i32.ne"
             brIf f failLbl
         | Some _, Some t ->
             lg f slot
             gcT f "ref.test" "$du1"
             ins f "i32.eqz"
             brIf f failLbl
             lg f slot
             gcT f "ref.cast" "$du1"
             gcTF f "struct.get" "$du1" 0
             ic f t
             ins f "i32.ne"
             brIf f failLbl
             // every sub-pattern matches against the ONE payload slot,
             // exactly as the text emitter does (Lower tuples multi-payload)
             for sub in args do
                 let pl = freshLocal f "$bq" "anyref"
                 lg f slot
                 gcT f "ref.cast" "$du1"
                 gcTF f "struct.get" "$du1" 1
                 ls f pl
                 emitPat st f lv failLbl pl sub
         | _ -> err st ("binary: unknown ctor in pattern " + name))
    | PTuple ps ->
        let t = "$tup" + string (List.length ps)
        let mutable i = 0
        for sub in ps do
            let pl = freshLocal f "$bq" "anyref"
            lg f slot
            gcT f "ref.cast" t
            gcTF f "struct.get" t i
            ls f pl
            emitPat st f lv failLbl pl sub
            i <- i + 1
    | PCons (h, tl) ->
        lg f slot
        gcT f "ref.test" "$cons"
        ins f "i32.eqz"
        brIf f failLbl
        let hl = freshLocal f "$bq" "anyref"
        lg f slot
        gcT f "ref.cast" "$cons"
        gcTF f "struct.get" "$cons" 0
        ls f hl
        emitPat st f lv failLbl hl h
        let tll = freshLocal f "$bq" "anyref"
        lg f slot
        gcT f "ref.cast" "$cons"
        gcTF f "struct.get" "$cons" 1
        ls f tll
        emitPat st f lv failLbl tll tl
    | PListLit [] ->
        lg f slot
        ins f "ref.is_null"
        ins f "i32.eqz"
        brIf f failLbl
    | PListLit (p0 :: rest) ->
        emitPat st f lv failLbl slot (PCons (p0, PListLit rest))
    | PAs (inner, v, _) ->
        let l =
            match dictTryFind lv (v.Path, v.Offset) with
            | Some ex when not (ex.StartsWith "@env:") -> ex
            | _ ->
                let l = freshLocal f "$bp" "anyref"
                dictSet lv (v.Path, v.Offset) l
                l
        lg f slot
        ls f l
        emitPat st f lv failLbl slot inner
    | POr alts ->
        // try each alternative; any match jumps past the rest. All bind the
        // same identities, and PVar's slot reuse makes them agree.
        blockE f "$por"
        let n = List.length alts
        alts |> List.iteri (fun j alt ->
            if j < n - 1 then
                blockE f "$palt"
                emitPat st f lv "$palt" slot alt
                br f "$por"
                endB f
            else
                emitPat st f lv failLbl slot alt)
        endB f
    | PLit (LString raw) ->
        lg f slot
        let bytes = unescape raw
        let dn, len = internStr st bytes
        ic f 0
        ic f len
        arrNewData f "$str" dn
        callf f "$equal"
        gcAbs f "ref.cast" "i31"
        i31get f
        ins f "i32.eqz"
        brIf f failLbl
    | PLit (LChar raw) ->
        lg f slot
        callf f "$toi"
        ic f (charCode raw)
        ins f "i32.ne"
        brIf f failLbl
    | PLit (LFloat s) ->
        let num = s |> String.filter (fun c -> isDigit c || c = '.' || c = '-' || c = '+' || c = 'e' || c = 'E')
        lg f slot
        callf f "$tof"
        fc f (doubleBits (parseFloat num))
        ins f "f64.ne"
        brIf f failLbl
    | PLit LNull ->
        lg f slot
        ins f "ref.is_null"
        ins f "i32.eqz"
        brIf f failLbl
    | PLit LUnit -> ()
    | PTypeTest tn ->
        // `:? T` in a pattern: same tests as ETypeTest, branch to fail
        let idOf () =
            lg f slot
            gcT f "ref.cast" "$obj"
            gcTF f "struct.get" "$obj" 0
            gcT f "ref.cast" "$desc"
            gcTF f "struct.get" "$desc" 0
        let classIdTest (classes : string list) =
            let hits = classes |> List.filter (fun c -> (dictTryFind st.ObjRec c).IsSome)
            lg f slot
            gcT f "ref.test" "$obj"
            ifV f "i32"
            (match hits with
             | [] -> ic f 0
             | first :: rest ->
                 idOf ()
                 ic f (dictTryFind st.DescIdOf first).Value
                 ins f "i32.eq"
                 for c in rest do
                     idOf ()
                     ic f (dictTryFind st.DescIdOf c).Value
                     ins f "i32.eq"
                     ins f "i32.or")
            elseB f
            ic f 0
            endB f
        if tn = "list" then
            lg f slot
            ins f "ref.is_null"
            lg f slot
            gcT f "ref.test" "$cons"
            ins f "i32.or"
        elif tn = "array" then
            lg f slot
            callf f "$isArrayRep"
        elif tn = "string" then
            lg f slot
            gcT f "ref.test" "$str"
        elif (dictTryFind st.ObjRec tn).IsSome then
            classIdTest (match dictTryFind st.SubsOf tn with Some s -> s | None -> [ tn ])
        elif (dictTryFind st.IfaceName tn).IsSome then
            classIdTest (match dictTryFind st.ImplsOf tn with Some s -> s | None -> [])
        else
            err st ("binary: cannot type-test pattern against " + tn)
            ic f 0
        ins f "i32.eqz"
        brIf f failLbl
    | _ -> err st "binary: pattern case not ported yet"

/// Emit a body whose locals are only discovered DURING emission: run the
/// emission once into a scratch buffer (locals allocate in a deterministic
/// order), then declare exactly those locals and splice the bytes. Local
/// indices agree because both passes allocate in the same order.
and private emitWithLocals (st : St) (f : Fn) (lv : Dict<string * int, string>)
                           (owner : string) (body : Expr) (needsResult : bool) : bool =
    emitWithLocalsK st f lv owner body []

and private emitWithLocalsK (st : St) (f : Fn) (lv : Dict<string * int, string>)
                            (owner : string) (body : Expr)
                            (paramKinds : ((string * int) * string) list) : bool =
    // rail-kind decisions are PER PASS: monomorphized clones share binder
    // keys across functions, and within one body a kindOfLite peeking into a
    // nested let-block must see the SAME (empty-so-far) state in the replay
    // as the scratch saw — entries accumulate during a pass, never before it
    let clearKinds () =
        for k, _ in dictPairs st.LocalKind do dictRemove st.LocalKind k
        // RAW params are rail entries from the first instruction on
        for key, k in paramKinds do dictSet st.LocalKind key k
    clearKinds ()
    let scratchB = bytesNew ()
    let scratch =
        { M = f.M; B = scratchB; LocalIdx = dictNew (); LocalTys = vecNew ()
          NParams = f.NParams; Labels = labelsNew (); PatchAt = 0; Replay = -1
          PeepLast = None; PeepPrev = None }
    for k, v in dictPairs f.LocalIdx do
        if (dictTryFind scratch.LocalIdx k).IsNone then dictSet scratch.LocalIdx k v
    let lv0 = dictNew<string * int, string> ()
    for k, v in dictPairs lv do dictSet lv0 k v
    // the DRY RUN uses a throwaway error sink: a body that hits unported
    // cases becomes an UNREACHABLE STUB (bring-up mode: vtable-rooted
    // prelude members survive DCE but are never called by small programs).
    // Reaching a stub at runtime traps loudly rather than misbehaving.
    let probe = { st with Errors = vecNew () }
    emitNode probe scratch lv0 body
    if vecLen probe.Errors > 0 then
        vecAdd st.Warnings ("stubbed " + owner + " (" + vecGet probe.Errors 0 + ")")
        localsDone f
        ins f "unreachable"
        false
    else
        for t in vecToList scratch.LocalTys do
            let l = "$x" + string (vecLen f.LocalTys)
            local f l t
        localsDone f
        clearKinds ()
        f.Replay <- 0
        let lv1 = dictNew<string * int, string> ()
        for k, v in dictPairs lv do dictSet lv1 k v
        emitNode st f lv1 body
        true

/// the whole program: globals + per-decl init functions + _start
let emitBinary (decls : Decl list) : byte[] * string list * string list =
    let m = modNew ()
    let st =
        { M = m; Errors = vecNew (); CaseTag = dictNew (); CaseArity = dictNew ()
          EnumConst = dictNew (); GlobalOf = dictNew (); FnOf = dictNew ()
          ArityOf = dictNew (); Warnings = vecNew ()
          Wrappers = dictNew ()
          CtorFns = dictNew (); LateFns = vecNew (); Externs = dictNew ()
          FieldsOf = dictNew (); FieldIdx = dictNew (); FieldOwner = dictNew (); DataN = 0
          LamName = refMapNew (fun (_ : Expr) -> 7)
          LamFree = dictNew (); LamBody = vecNew (); CellVars = fst (cellScan decls)
          ObjRec = dictNew (); ClassName = dictNew (); DescIdOf = dictNew ()
          SlotOf = dictNew (); IfaceName = dictNew (); ImplsOf = dictNew ()
          SubsOf = dictNew (); BaseOf = dictNew ()
          TailApp = refMapNew (fun (_ : Expr) -> 7)
          Pod = dictNew (); StructFields = dictNew ()
          LocalKind = dictNew (); InLambda = snd (cellScan decls)
          SigKinds = dictNew (); SigByName = dictNew (); CurRet = "u" }
    // ---- class machinery tables (pure, over the decls) ---------------------
    let classDecls = decls |> List.choose (fun d -> match d with DClass (n, b, own, impls) -> Some (n, b, own, impls) | _ -> None)
    let classImpls = classDecls |> List.map (fun (n, _, _, impls) -> n, impls)
    let isClassName (n : string) = classDecls |> List.exists (fun (cn, _, _, _) -> cn = n)
    let baseOf (n : string) = classDecls |> List.tryPick (fun (cn, b, _, _) -> if cn = n then b else None)
    let ownMembersOf (n : string) = classDecls |> List.tryPick (fun (cn, _, own, _) -> if cn = n then Some own else None)
    let rec chainOf (n : string) : string list =
        match baseOf n with
        | Some b when b <> n -> n :: chainOf b
        | _ -> [ n ]
    let subclassesOf (n : string) =
        let derived =
            classDecls |> List.filter (fun (cn, _, _, _) -> List.contains n (chainOf cn)) |> List.map (fun (cn, _, _, _) -> cn)
        if List.isEmpty derived then [ n ] else derived
    let interfaceDecls = decls |> List.choose (fun d -> match d with DInterface (n, ms) -> Some (n, ms) | _ -> None)
    let vtableSlots =
        ((interfaceDecls |> List.collect (fun (i, ms) -> ms |> List.map (fun (mn, _) -> i, mn)))
         @ (classImpls |> List.collect (fun (_, impls) -> impls |> List.collect (fun (i, ms) -> ms |> List.map (fun (mn, _) -> i, mn)))))
        |> List.distinct
        |> List.sort
    let slotImpl (cn : string) (owner : string) (mn : string) : VarId option =
        let fromIface =
            chainOf cn
            |> List.tryPick (fun c ->
                classDecls
                |> List.tryPick (fun (n2, _, _, impls) ->
                    if n2 <> c then None
                    else impls |> List.tryPick (fun (i, ms) -> if i = owner then ms |> List.tryPick (fun (mm, v) -> if mm = mn then Some v else None) else None)))
        match fromIface with
        | Some v -> Some v
        | None ->
            if List.contains owner (chainOf cn) then
                chainOf cn
                |> List.tryPick (fun c ->
                    ownMembersOf c |> Option.bind (fun own -> own |> List.tryPick (fun (mm, v) -> if mm = mn then Some v else None)))
            else None
    // slots 0 and 1 of every vtable are Equals and GetHashCode
    let identitySlots = 2
    let declaredMembers =
        decls |> List.choose (fun d -> match d with DMembers (n, own) -> Some (n, own) | _ -> None)
    let identityImpl (cn : string) (name : string) : VarId option =
        chainOf cn
        |> List.tryPick (fun c ->
            let fromClass =
                ownMembersOf c |> Option.bind (fun own -> own |> List.tryPick (fun (mm, v) -> if mm = name then Some v else None))
            match fromClass with
            | Some v -> Some v
            | None ->
                declaredMembers
                |> List.tryPick (fun (n, own) ->
                    if n <> c then None
                    else own |> List.tryPick (fun (mm, v) -> if mm = name then Some v else None)))
    let rawRecords = decls |> List.choose (fun d -> match d with DRecord (n, _, fs, stf) -> Some (n, fs, stf) | _ -> None)
    let rec expandedFields (n : string) : (string * string) list =
        match rawRecords |> List.tryPick (fun (rn, fs, _) -> if rn = n then Some fs else None) with
        | None -> []
        | Some fs ->
            match baseOf n with
            | Some b when b <> n -> expandedFields b @ fs
            | _ -> fs
    let isObjRecord (n : string) = rawRecords |> List.exists (fun (rn, _, stf) -> rn = n && not stf)
    // ---- POD layout (clang natural alignment), like the text backend ------
    let structNames = rawRecords |> List.filter (fun (_, _, stf) -> stf) |> List.map (fun (n, _, _) -> n)
    let fieldKind (ty : string) : string =
        match ty with
        | "float" -> "f"
        | "float32" -> "s"
        | "int64" -> "l"
        | "int" | "bool" | "char" | "float16" -> "i"
        | t when List.contains t structNames -> "S:" + t
        | _ -> "r"
    let scalarSize (k : string) = if k = "i" || k = "s" then 4 else 8
    for rn, fs, stf in rawRecords do
        if stf then dictSet st.StructFields rn fs
    let rec computeLayout (rn : string) : bool =
        if (dictTryFind st.Pod rn).IsSome then true
        else
            match dictTryFind st.StructFields rn with
            | None -> false
            | Some fs ->
                let ok =
                    fs |> List.forall (fun (_, ty) ->
                        let k = fieldKind ty
                        if k = "i" || k = "f" || k = "s" || k = "l" then true
                        elif k.StartsWith "S:" then
                            let sn = k.Substring 2
                            sn <> rn && computeLayout sn
                        else false)
                if not ok then false
                else
                    let mutable off = 0
                    let mutable maxA = 1
                    let leaves = vecNew<string * string * int> ()
                    for fn, ty in fs do
                        let k = fieldKind ty
                        if k = "i" || k = "f" || k = "s" || k = "l" then
                            let sz = scalarSize k
                            off <- ((off + sz - 1) / sz) * sz
                            vecAdd leaves (fn, k, off)
                            off <- off + sz
                            if sz > maxA then maxA <- sz
                        else
                            let sn = k.Substring 2
                            let nl, nsz, _ = (dictTryFind st.Pod sn).Value
                            let na = nl |> List.map (fun (_, k2, _) -> scalarSize k2) |> List.max
                            off <- ((off + na - 1) / na) * na
                            for np, nk, noff in nl do
                                vecAdd leaves (fn + "." + np, nk, off + noff)
                            off <- off + nsz
                            if na > maxA then maxA <- na
                    let sizeof_ = ((off + maxA - 1) / maxA) * maxA
                    dictSet st.Pod rn (vecToList leaves, sizeof_, (sizeof_ + 7) / 8)
                    true
    for rn in structNames do computeLayout rn |> ignore
    let objRecordNames = rawRecords |> List.filter (fun (_, _, stf) -> not stf) |> List.map (fun (n, _, _) -> n)
    let descId (n : string) = objRecordNames |> List.findIndex (fun rn -> rn = n)
    // populate the St-side lookup tables emitNode dispatches through
    for n in objRecordNames do
        dictSet st.ObjRec n true
        dictSet st.DescIdOf n (descId n)
    for cn, _, _, _ in classDecls do
        dictSet st.ClassName cn true
        dictSet st.SubsOf cn (subclassesOf cn)
        (match baseOf cn with
         | Some b when b <> cn -> dictSet st.BaseOf cn b
         | _ -> ())
    vtableSlots |> List.iteri (fun i (ifn, mn) -> dictSet st.SlotOf (ifn, mn) (i + identitySlots))
    for ifn, _ in interfaceDecls do dictSet st.IfaceName ifn true
    let ifaceNames =
        (interfaceDecls |> List.map fst)
        @ (classImpls |> List.collect (fun (_, impls) -> impls |> List.map fst))
        |> List.distinct
    for ifn in ifaceNames do
        dictSet st.IfaceName ifn true
        let impls =
            classImpls
            |> List.filter (fun (_, impls) -> impls |> List.exists (fun (i, _) -> i = ifn))
            |> List.collect (fun (cn, _) -> subclassesOf cn)
            |> List.distinct
            |> List.filter isObjRecord
        dictSet st.ImplsOf ifn impls
    // functions reachable through a vtable keep the canonical all-anyref
    // signature — that IS the dispatch contract, so no specialization
    let ifaceImplKeys =
        (classImpls |> List.collect (fun (_, impls) -> impls |> List.collect (fun (_, ms) -> ms |> List.map (fun (_, v) -> v.Path, v.Offset))))
        @ (classDecls
           |> List.collect (fun (cn, _, _, _) ->
                vtableSlots |> List.choose (fun (i, mn) -> slotImpl cn i mn |> Option.map (fun v -> v.Path, v.Offset))))
        @ (declaredMembers
           |> List.collect (fun (_, own) ->
                own |> List.choose (fun (mn, v) -> if mn = "Equals" || mn = "GetHashCode" then Some (v.Path, v.Offset) else None)))
        @ (classDecls
           |> List.collect (fun (_, _, own, _) ->
                own |> List.choose (fun (mn, v) -> if mn = "Equals" || mn = "GetHashCode" then Some (v.Path, v.Offset) else None)))
    let isIfaceImpl (key : string * int) = List.contains key ifaceImplKeys
    let scalarKindOfTy (t : Fpp.Analysis.Types.Type) : string =
        match Fpp.Analysis.Types.prune t with
        | Fpp.Analysis.Types.TCon ("float", []) -> "f"
        | Fpp.Analysis.Types.TCon ("float32", []) -> "s"
        | Fpp.Analysis.Types.TCon ("int64", []) -> "l"
        | Fpp.Analysis.Types.TCon ("int", []) -> "i"
        | _ -> "u"
    let rec splitArrow (n : int) (t : Fpp.Analysis.Types.Type) : string list * string =
        if n = 0 then [], scalarKindOfTy t
        else
            match Fpp.Analysis.Types.prune t with
            | Fpp.Analysis.Types.TFun (a, b) ->
                let ps, r = splitArrow (n - 1) b
                scalarKindOfTy a :: ps, r
            | other -> [], scalarKindOfTy other
    // arity of every top-level function, for iface dispatch types
    let dletArity = dictNew<string * int, int> ()
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, _)) -> dictSet dletArity (v.Path, v.Offset) (List.length ps)
        | _ -> ()
    let ifaceArities =
        classDecls
        |> List.collect (fun (cn, _, _, _) ->
            vtableSlots
            |> List.choose (fun (i, mn) ->
                slotImpl cn i mn |> Option.bind (fun v -> dictTryFind dletArity (v.Path, v.Offset))))
        |> List.distinct
    // EVERY program function is declared at type $v<arity>, so the frame
    // needs a $vN for each arity the program uses — not only the iface ones
    let vArities =
        ([ 1; 2; 3 ] @ ifaceArities @ (dictPairs dletArity |> List.map snd))
        |> List.distinct |> List.sort
    // tags in declaration order, like the text prepass
    let mutable tag = 0
    let caseOwner = dictNew<string, string> ()
    for d in decls do
        match d with
        | DUnion (un, _, cases) ->
            for cn, ar in cases do
                dictSet st.CaseTag cn tag
                dictSet st.CaseArity cn ar
                dictSet caseOwner cn un
                tag <- tag + 1
        | DEnum (_, cs) -> for c, v in cs do dictSet st.EnumConst c v
        | _ -> ()
    let tupArities = ([ 2; 3 ] @ scanTupleArities decls) |> List.distinct |> List.sort
    frame m vArities tupArities
    // FFI imports — these occupy function indices BEFORE every declared
    // function, so they must all be registered here, right after the frame
    let abiKind (t : Fpp.Analysis.Types.Type) : string =
        match Fpp.Analysis.Types.prune t with
        | Fpp.Analysis.Types.TCon ("int", []) | Fpp.Analysis.Types.TCon ("bool", [])
        | Fpp.Analysis.Types.TCon ("char", []) -> "i"
        | _ -> "r"
    let rec abiSig (t : Fpp.Analysis.Types.Type) : string list * string =
        match Fpp.Analysis.Types.prune t with
        | Fpp.Analysis.Types.TFun (a, b) ->
            let ps, r = abiSig b
            abiKind a :: ps, r
        | r -> [], abiKind r
    for d in decls do
        match d with
        | DExtern (v, sch) ->
            let pks, rk = abiSig sch.Body
            let fn = mangle v
            importFn m "env" v.Name fn
                (pks |> List.map (fun k -> if k = "i" then "i32" else "anyref"))
                [ (if rk = "i" then "i32" else "anyref") ]
            dictSet st.FnOf (v.Path, v.Offset) fn
            dictSet st.ArityOf (v.Path, v.Offset) (List.length pks)
            dictSet st.Externs (v.Path, v.Offset) (pks, rk)
        | _ -> ()
    // record types: UNIFORM anyref fields (scalarization is a parity task,
    // not a bring-up task). Every OBJ record carries __desc; classes add
    // __idhash and inherit their base's fields as a prefix — that layout is
    // what makes an upcast free. Bases are declared before derived types
    // (their type index must exist), so order by chain depth.
    let orderedRecords =
        rawRecords
        |> List.sortBy (fun (rn, _, stf) ->
            if stf || not (isClassName rn) then 0 else List.length (chainOf rn))
    for rn, fs0, stf in orderedRecords do
        let fields =
            if stf then fs0
            elif isClassName rn then ("__desc", "r") :: ("__idhash", "int") :: expandedFields rn
            else ("__desc", "r") :: fs0
        let names = fields |> List.map fst
        dictSet st.FieldsOf rn names
        names |> List.iteri (fun i fn ->
            dictSet st.FieldIdx (rn, fn) i
            if fn <> "__desc" && fn <> "__idhash" then dictSet st.FieldOwner fn rn)
        if not stf && isObjRecord rn then
            let super = match baseOf rn with Some b when b <> rn -> "$r_" + b | _ -> "$obj"
            tyStructSub m ("$r_" + rn) super false (names |> List.map (fun _ -> fld true "anyref"))
        else
            tyStruct m ("$r_" + rn) (names |> List.map (fun _ -> fld true "anyref"))
    rtTypes2 m
    rtTypes3 m
    rtTypes4 m
    rtTypes5 m
    rtTypes6 m
    rtTypes7 m
    rtTypes8 m
    rtTypes9 m
    rtTypes10 m
    rtTypes11 m
    rtTypes12 m
    rtTypes13 m
    tyFunc m "$init_t" [] []
    rtDecls m
    rtCoreDecls2 m
    rtDecls3 m
    rtDecls4 m
    rtDecls5 m
    rtDecls6 m
    rtDecls7 m
    rtDecls8 m
    rtDecls9 m
    rtDecls10 m
    rtDecls11 m
    rtDecls12 m
    rtDecls13 m
    // const globals for arity-0 DU cases
    for cn, _ in dictPairs st.CaseTag do
        if (dictTryFind st.CaseArity cn) = Some 0 then
            dictSet m.GlobalIdx ("$c_" + cn) m.GlobalCount
            m.GlobalCount <- m.GlobalCount + 1
            emitRefType m.GlobalBody false (tyIdx m "$du0")
            emitByte m.GlobalBody 0
            emitByte m.GlobalBody opI32Const
            emitS32 m.GlobalBody (dictTryFind st.CaseTag cn).Value
            emitByte m.GlobalBody opGcPrefix
            emitU32 m.GlobalBody (gcByte "struct.new")
            emitU32 m.GlobalBody (tyIdx m "$du0")
            emitByte m.GlobalBody opEnd
    // $duEq/$duHash are built AFTER program fns are declared (below): an
    // Equals/GetHashCode override on a union fills its tags' slots
    // program globals + init function declarations
    let inits = vecNew<string> ()
    for d in decls do
        match d with
        | DLet (_, v, sch, ELam (ps, _)) ->
            let fn = mangle v
            dictSet st.FnOf (v.Path, v.Offset) fn
            dictSet st.ArityOf (v.Path, v.Offset) (List.length ps)
            let pk, rk = splitArrow ps.Length sch.Body
            // a lambda-captured param must stay uniform: the closure env is
            // anyref, and the capture build site reads the slot RAW
            let capturedScalar =
                pk.Length = ps.Length
                && (List.zip ps pk
                    |> List.exists (fun ((pv : VarId, _), k) ->
                        k <> "u" && (dictTryFind st.InLambda (pv.Path, pv.Offset)).IsSome))
            if not (isIfaceImpl (v.Path, v.Offset)) && not capturedScalar
               && pk.Length = ps.Length && (rk <> "u" || List.exists (fun k -> k <> "u") pk) then
                dictSet st.SigKinds (v.Path, v.Offset) (pk, rk)
                dictSet st.SigByName fn (pk, rk)
                let wasmOf k = match k with "f" -> "f64" | "s" -> "f32" | "l" -> "i64" | "i" -> "i32" | _ -> "anyref"
                let tn = "$sig_" + String.concat "" pk + "_" + rk
                if tyIdx m tn < 0 then
                    tyFunc m tn (pk |> List.map wasmOf) [ wasmOf rk ]
                declFn m fn tn
            else
                declFn m fn ("$v" + string (List.length ps))
        | DLet (_, v, _, _) ->
            let g = mangle v
            dictSet st.GlobalOf (v.Path, v.Offset) g
            globalAnyref m g
        | _ -> ()
    // generated identity per obj record, then the descriptor globals — the
    // member fns those vtables reference are all declared by now
    globalI32Mut m "$nextid" 0
    globalI32Mut m "$heap" 65536
    let identityAdapters = vecNew<string * int * string> ()
    for rn in objRecordNames do
        declFn m ("$eq_" + rn) "$u1"
        declFn m ("$hash_" + rn) "$v1"
    let slotFnName (v : VarId) : string option =
        match dictTryFind dletArity (v.Path, v.Offset) with
        | Some _ -> Some (mangle v)
        | None -> None
    let descSlots =
        objRecordNames
        |> List.map (fun cn ->
            let identity =
                [ "Equals", "$eq_" + cn, 2; "GetHashCode", "$hash_" + cn, 1 ]
                |> List.map (fun (mname, generated, wantArity) ->
                    match identityImpl cn mname with
                    | Some v ->
                        (match slotFnName v, dictTryFind dletArity (v.Path, v.Offset) with
                         | Some fn, Some actual when actual = wantArity -> fn
                         | Some fn, Some actual when actual = wantArity + 1 ->
                             // GetHashCode() carries a unit argument: adapt
                             let ad = "$adapt" + string wantArity + "_" + cn + "_" + mname
                             vecAdd identityAdapters (ad, wantArity, fn)
                             ad
                         | _ -> generated)
                    | None -> generated)
            let slots =
                vtableSlots
                |> List.map (fun (i, mn) ->
                    match slotImpl cn i mn with
                    | Some v -> (match slotFnName v with Some fn -> fn | None -> "")
                    | None -> "")
            cn, identity @ slots)
    // union identity: structural by default, the union's own override where
    // one is declared — indexed by case tag, which is globally unique
    let duSlot (which : string) (dflt : string) (wantArity : int) : string list =
        if tag = 0 then [ dflt ]
        else
            List.init tag (fun t ->
                let owner =
                    dictPairs st.CaseTag
                    |> List.tryPick (fun (c, tg) -> if tg = t then dictTryFind caseOwner c else None)
                match owner |> Option.bind (fun o -> identityImpl o which) with
                | Some v ->
                    (match dictTryFind dletArity (v.Path, v.Offset) with
                     | Some a when a = wantArity -> mangle v
                     | Some a when a = wantArity + 1 ->
                         let ad = "$adaptdu" + string wantArity + "_" + string t
                         vecAdd identityAdapters (ad, wantArity, mangle v)
                         ad
                     | _ -> dflt)
                | None -> dflt)
    let duEqSlots = duSlot "Equals" "$eq_du_default" 2
    let duHashSlots = duSlot "GetHashCode" "$hash_du_default" 1
    for ad, arity, _ in vecToList identityAdapters do
        declFn m ad ("$v" + string arity)
    globalVt m "$duEq" duEqSlots
    globalVt m "$duHash" duHashSlots
    for cn, slots in descSlots do
        globalDesc m ("$desc_" + cn) (descId cn) slots
    // lambdas discovered only AFTER globals/functions are registered, so
    // the capture filter (below) can exclude them — a global or a known
    // function resolves directly and is never an env slot
    for d in decls do
        match d with
        | DLet (_, _, _, body) -> discoverLams st (dictNew ()) body
        | _ -> ()
    for name, _, _ in vecToList st.LamBody do
        declFn m name "$u1"
    let mutable initN = 0
    for d in decls do
        match d with
        | DLet (_, _, _, ELam _) -> ()
        | DLet (_, v, _, _) ->
            let fname = "$init" + string initN
            initN <- initN + 1
            vecAdd inits fname
            declFn m fname "$init_t"
        | _ -> ()
    declFn m "$_start" "$init_t"
    exportFn m "_start" "$_start"
    // bodies, in declaration order
    rtCore m
    rtCore2 m
    rtCore3 m tupArities
    rtCore4 m
    rtCore5 m
    rtCore6 m
    rtCore7 m tupArities
    rtCore8 m
    rtCore9 m
    rtCore10 m
    rtCore11 m
    rtCore12 m
    rtCore13 m
    // bodies in DECLARATION order: all functions first, then all inits —
    // interleaving them put code into the wrong slots
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, body)) ->
            let names = ps |> List.mapi (fun i _ -> "$a" + string i)
            let f = beginFn m names
            let lv = dictNew<string * int, string> ()
            List.iteri (fun i (pv : VarId, _) -> dictSet lv (pv.Path, pv.Offset) ("$a" + string i)) ps
            let pks, rk =
                match dictTryFind st.SigKinds (v.Path, v.Offset) with
                | Some (p, r) -> p, r
                | None -> (ps |> List.map (fun _ -> "u")), "u"
            let paramKinds =
                List.zip ps pks
                |> List.choose (fun ((pv : VarId, _), k) ->
                    if k = "u" then None else Some ((pv.Path, pv.Offset), k))
            st.CurRet <- rk
            markTails st body
            // locals must all exist before instructions: pre-scan the body
            // is avoided by DECLARING lazily... which binary cannot do — so
            // Fn allows locals before localsDone only. Pre-pass: count let/
            // match binders by walking? Simpler: emit into a scratch, then
            // splice. The scratch approach: emit body into a temp Bytes via
            // a temp Fn, then copy. Implemented as: body Fn writes into the
            // REAL code stream, and `local` is legal before localsDone —
            // so we must know locals first. We pre-walk the body and create
            // one anyref local per binder, keyed by the SAME naming scheme
            // emitNode/emitPat use (vecLen LocalTys order).
            emitWithLocalsK st f lv (mangle v) body paramKinds |> ignore
            if rk <> "u" then callf f (unboxOfK rk)
            st.CurRet <- "u"
            endFn f
        | _ -> ()
    // generated identity bodies — a record compares and hashes over its
    // fields; a class is reference-equal with a lazily assigned id number
    // (wasm-GC exposes no identity of its own: ref.eq compares, it does
    // not number)
    for rn in objRecordNames do
        let fieldCount = (dictTryFind st.FieldsOf rn).Value.Length
        let rt = "$r_" + rn
        // $eq_rn
        let f = beginFn m [ "$a"; "$b" ]
        localsDone f
        if isClassName rn then
            lg f "$a"
            castEq f
            lg f "$b"
            castEq f
            ins f "ref.eq"
            refI31 f
        else
            for i in 1 .. fieldCount - 1 do
                lg f "$a"
                gcT f "ref.cast" rt
                gcTF f "struct.get" rt i
                lg f "$b"
                gcT f "ref.cast" rt
                gcTF f "struct.get" rt i
                callf f "$equal"
                gcAbs f "ref.cast" "i31"
                i31get f
                ins f "i32.eqz"
                ifE f
                ic f 0
                refI31 f
                ret f
                endB f
            ic f 1
            refI31 f
        endFn f
        // $hash_rn
        let f = beginFn m [ "$v" ]
        local f "$h" "i32"
        localsDone f
        if isClassName rn then
            lg f "$v"
            gcT f "ref.cast" rt
            gcTF f "struct.get" rt 1
            callf f "$toi"
            ls f "$h"
            lg f "$h"
            ins f "i32.eqz"
            ifE f
            gg f "$nextid"
            ic f 1
            ins f "i32.add"
            gs f "$nextid"
            gg f "$nextid"
            ls f "$h"
            lg f "$v"
            gcT f "ref.cast" rt
            lg f "$h"
            callf f "$ofi"
            gcTF f "struct.set" rt 1
            endB f
            // spread the sequential ids so they do not cluster in a table
            lg f "$h"
            ic f -1640531527
            ins f "i32.mul"
            refI31 f
        else
            let firstField = 1
            if fieldCount <= firstField then
                ic f (descId rn)
                refI31 f
            else
                lg f "$v"
                gcT f "ref.cast" rt
                gcTF f "struct.get" rt firstField
                callf f "$hashv"
                for i in firstField + 1 .. fieldCount - 1 do
                    ic f 31
                    ins f "i32.mul"
                    lg f "$v"
                    gcT f "ref.cast" rt
                    gcTF f "struct.get" rt i
                    callf f "$hashv"
                    ins f "i32.add"
                refI31 f
        endFn f
    // identity adapters: the override carries a unit argument the slot
    // does not; pass one
    for _, arity, target in vecToList identityAdapters do
        let names = List.init arity (fun i -> "$p" + string i)
        let f = beginFn m names
        localsDone f
        for n in names do lg f n
        ic f 0
        refI31 f
        callf f target
        endFn f
    // lambda bodies: param + env; captured keys read from the env array.
    // The capture FILTER at each build site is "is it a local there", so the
    // body maps every free key optimistically; unreached slots never read.
    for name, (pv, _), body in vecToList st.LamBody do
        let f = beginFn m [ "$a"; "$env" ]
        let lv = dictNew<string * int, string> ()
        dictSet lv (pv.Path, pv.Offset) "$a"
        // env reads become locals loaded up front — one array.get per slot
        let free = (dictTryFind st.LamFree name).Value
        let scratchProbe = { st with Errors = vecNew () }
        // slot mapping mirrors the build-site filter only at RUN time; the
        // body binds each env slot to a fresh local before its code
        let envLocals = free |> List.mapi (fun i k -> k, i)
        let fB = f
        // first pass probes; handled inside emitWithLocals — here we bind
        // env slots as pseudo-locals via a prelude in the body: emit reads
        // after localsDone. To keep the two-pass scheme, the prelude is part
        // of a wrapper expression instead: read slots lazily at each use.
        // Simplest correct: lv marks env keys with a sentinel handled in
        // EVar; but two-pass naming needs stability — so bind ALL slots to
        // locals here, before emitWithLocals, via direct emission:
        // (locals must precede instructions, so this uses the scratch pass
        // machinery: slot binds are emitted as part of the body by wrapping)
        ignore envLocals
        ignore scratchProbe
        ignore fB
        // sentinel scheme: "@env:i" in lv, resolved in emitNode's EVar case
        free |> List.iteri (fun i k -> dictSet lv k ("@env:" + string i))
        markTails st body
        emitWithLocals st f lv name body true |> ignore
        endFn f
    for d in decls do
        match d with
        | DLet (_, _, _, ELam _) -> ()
        | DLet (_, v, _, rhs) ->
            let f = beginFn m []
            let lv = dictNew<string * int, string> ()
            if emitWithLocals st f lv (mangle v) rhs true then
                gs f (dictTryFind st.GlobalOf (v.Path, v.Offset)).Value
            endFn f
        | _ -> ()
    let f = beginFn m []
    localsDone f
    for i in vecToList inits do callf f i
    endFn f
    // curried wrapper bodies: requested lazily during body emission, so their
    // decls sit after $_start in the function section — bodies land here in
    // request order. Each .wk before the last conses its arg onto the env;
    // the last unspools the chain (latest arg first) and calls direct.
    for entry in vecToList st.LateFns do
        if entry.StartsWith "c:" then
            // a constructor as a function: build the case from the argument
            let name = entry.Substring 2
            let f = beginFn m [ "$a"; "$env" ]
            localsDone f
            ic f (dictTryFind st.CaseTag name).Value
            lg f "$a"
            gcT f "struct.new" "$du1"
            endFn f
        else
        let fname = entry.Substring 2
        let arity = (dictTryFind st.Wrappers fname).Value
        for k in 0 .. arity - 1 do
            let f = beginFn m [ "$a"; "$env" ]
            localsDone f
            if k = arity - 1 then
                let pks, rk =
                    match dictTryFind st.SigByName fname with
                    | Some (p, r) -> p, r
                    | None -> List.replicate arity "u", "u"
                for j in 0 .. arity - 1 do
                    (if j = k then lg f "$a"
                     else
                        lg f "$env"
                        for _ in 1 .. (k - 1 - j) do
                            gcT f "ref.cast" "$cons"
                            gcTF f "struct.get" "$cons" 1
                        gcT f "ref.cast" "$cons"
                        gcTF f "struct.get" "$cons" 0)
                    let pk = List.item j pks
                    if pk <> "u" then callf f (unboxOfK pk)
                callf f fname
                if rk <> "u" then callf f (boxOfK rk)
            else
                rf f (fname + ".w" + string (k + 1))
                lg f "$a"
                lg f "$env"
                gcT f "struct.new" "$cons"
                gcT f "struct.new" "$clo"
            endFn f
    assemble m 17 true, vecToList st.Errors, vecToList st.Warnings
