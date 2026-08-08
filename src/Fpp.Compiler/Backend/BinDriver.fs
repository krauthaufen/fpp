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
      mutable CellVars : Dict<string * int, bool>
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
      /// POD struct -> its alignment, which is also its backing word width
      PodAlign : Dict<string, int>
      /// POD struct -> "s" or "f" when every field is a float of the backing
      /// width, so the array itself can hold floats and a read is the
      /// `array.get` alone. "" otherwise.
      PodKind : Dict<string, string>
      /// Whether to optimize at all. A debug build wants code that matches
      /// the source it came from: a hoisted base and an elided branch are
      /// both invisible in the source, and a debugger stepping through them
      /// has nothing to point at.
      mutable Opt : bool
      /// A local bound to a POD ELEMENT, split into one unboxed local per
      /// field. `let v = pts.[i]` used to build a GC struct with boxed fields
      /// — an allocation per element, which is ruinous while a large POD
      /// array is live. Snapshotting the fields instead is exactly the same
      /// value, since a POD element is a value.
      PodElem : Dict<string * int, (string * string * string) list>
      /// POD types the program ever pins. An access to a type that is never
      /// pinned cannot be looking at linear memory, so it needs no test for
      /// it — which takes a branch out of every element read.
      PinnedTypes : Dict<string, bool>
      /// A top-level `let` bound to a LITERAL. Reading it as a global costs
      /// a load and an unbox at every use — inside a loop condition, every
      /// iteration — when the value was known at compile time all along.
      ConstGlobal : Dict<string * int, Expr>
      /// A POD array whose base has been hoisted out of the loop being
      /// emitted: global name -> (typed storage local, pin-pointer local).
      /// Nothing in a loop changes either, so fetching them once turns every
      /// element access into a single load.
      PodBase : Dict<string, string * string>
      /// locals on a RAW scalar rail: binder key -> kind (i/f/s/l). Reads
      /// box, writes unbox — and the peephole cancels both against their
      /// producers/consumers, which is what makes a hot loop alloc-free
      /// the frame id to push for the function being emitted, -1 for none
      mutable DbgFrame : int
      LocalKind : Dict<string * int, string>
      /// known functions with SCALAR signatures: param kinds + return kind.
      /// Calls unbox arguments and box results (both cancel on rails);
      /// bodies receive raw params and return raw
      SigKinds : Dict<string * int, string list * string>
      SigByName : Dict<string, string list * string>
      /// string-literal segments by CONTENT: duplicates share one segment
      /// and one hoisted global (so equal literals are the SAME reference)
      StrSegs : Dict<string, string * int>
      /// unions whose every case is nullary: their values are the global
      /// singletons, so equality IS identity (one ref.eq, no dispatch)
      EnumLikeUnion : Dict<string, bool>
      /// (record, field) -> declared type name, for EVERY record — uniform
      /// storage erases types, but the VALUE kind is still statically known
      RecFieldTy : Dict<string * string, string>
      /// the CURRENT body's return kind — return_call is legal only when
      /// callee and caller agree (the frame that would unbox is gone)
      mutable CurRet : string
      /// mentioned inside some lambda: those can never be rail locals
      mutable InLambda : Dict<string * int, bool>
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
    let key = bytesString bytes
    match dictTryFind st.StrSegs key with
    | Some (n, l) -> n, l
    | None ->
        let name = "$bd" + string st.M.DataCount
        dataSeg st.M name bytes
        // hoisted: one (ref $str) global per distinct literal
        globalStrLit st.M ("$sl:" + name)
        dictSet st.StrSegs key (name, bytes.Length)
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

let unescape (raw : string) : byte[] =
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
let charCode (raw : string) : int =
    let inner = if strLen raw >= 2 then substr raw 1 (strLen raw - 2) else raw
    if strLen inner > 1 && charAt inner 0 = '\\' then fst (escapeAt inner 0)
    else
        let bs = unescape raw
        if bs.Length > 0 then int bs.[0] else 0

/// "12" -> Some 12; anything with a non-digit (or empty) -> None. Spelled
/// out because the compiler compiles ITSELF: System.Int32.TryParse is not in
/// the subset, and a stubbed helper took the whole emitter down at startup.
let private parseDigits (s : string) : int option =
    if strLen s = 0 then None
    else
        let mutable ok = true
        for i in 0 .. strLen s - 1 do
            let c = charAt s i
            if c < '0' || c > '9' then ok <- false
        if ok then Some (int s) else None

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
        | ELet (_, v, _, EApp (EUnknown "$forcecell", [ r ]), b) ->
            // class-level `let mutable`: the instance field will hold the
            // CELL, so this binding is a cell no matter what the capture
            // analysis would say
            dictSet letBound (v.Path, v.Offset) true
            dictSet assigned (v.Path, v.Offset) true
            dictSet inLambda (v.Path, v.Offset) true
            g r
            g b
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
        | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) | EArrayBytes (_, a) | ECast (_, a, _) | ETypeTest (_, a) -> g a
        | EArrayCreate (_, n, v) -> g n; g v
        | EIfaceCall (_, _, recv, args) -> g recv; List.iter g args
        | ETry (b, cs) ->
            g b
            for _, gd, x in cs do
                (match gd with Some gd -> g gd | None -> ())
                g x
        | _ -> ()
    // A top-level function's own parameter lambda IS the function, not a
    // capture boundary: its body compiles to a wasm function whose params are
    // locals. Exactly ONE layer, though — `ArityOf` comes from that outermost
    // lambda's param list, so any lambda INSIDE it is a real closure and the
    // variables it reads are captures. Stripping every layer hid precisely
    // that: `let f (n : int) = (fun x -> x + n)` left `n` unmarked, so the
    // captured scalar went on a raw rail while the env slot stayed anyref, and
    // the module did not even validate.
    let skipParams (e : Expr) : Expr =
        match e with
        | ELam (_, b) -> b
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
    | ECast (_, x, _) | ETypeTest (_, x) | EArrayLen (_, x) | EArrayPin (_, x) | EArrayUnpin (_, x) | EArrayBytes (_, x) ->
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
        for k in 0 .. arity - 1 do
            let wk = fname + ".w" + string k
            declFn f.M wk "$u1"
            tblIdx f.M wk |> ignore

/// cast to (ref null eq) — ref.eq's operand type
let private castEq (f : Fn) : unit =
    gci f "ref.cast_null"
    emitS32 f.B (heapByte "eq" - 0x80)

/// the STATIC kind of an expression, where one is knowable without type
/// state: enough to pick the rail a kindless conversion reads from. Uniform
/// storage makes "u" safe everywhere else — the value carries its box.
/// a SHALLOW hash for Expr-keyed refmaps: no identity exists under
/// wasm-GC, but the node's surface (binder offsets, arities) spreads the
/// open-addressed clusters from all-in-one to a handful per shape. refEq
/// verifies, so collisions only cost probes.
let private shallowExprHash (e : Expr) : int =
    match e with
    | ELam ((pv, _) :: _, _) -> 31 * pv.Offset + 7
    | EApp ((EVar (v, _) | EVarI (v, _, _)), args) -> 31 * v.Offset + List.length args
    | EApp (_, args) -> 17 + List.length args
    | _ -> 7

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
/// A chain of field accesses rooted at an array element, flattened to the
/// dotted path the layout names its leaves by: `e.[i].Lo.PX` is "Lo.PX".
/// Without this a nested struct fell off the fused path and materialised the
/// whole element — three allocations per access for a box of two points.
let rec private podFieldChain (e : Expr) : (string * Expr * Expr * string) option =
    match e with
    | EField (EIndex (nm, a, i), fn, _) -> Some (nm, a, i, fn)
    | EField (inner, fn, _) ->
        (match podFieldChain inner with
         | Some (nm, a, i, p) -> Some (nm, a, i, p + "." + fn)
         | None -> None)
    | _ -> None

/// which split element (and which leaf of it) a field chain names
let rec private podVarChainOf (key : string * int) (e : Expr) : string option =
    match e with
    | EField (EVar (v, _), fn, _) when (v.Path, v.Offset) = key -> Some fn
    | EField (inner, fn, _) ->
        (match podVarChainOf key inner with
         | Some p -> Some (p + "." + fn)
         | None -> None)
    | _ -> None

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
    | EField (_, fname, owner) when owner <> "" ->
        // ONLY the lint-resolved owner: the last-wins FieldOwner fallback
        // can name a different record that shares the field name, and a
        // wrong KIND is a trap where a wrong index was merely the
        // pre-existing ambiguity
        (match dictTryFind st.RecFieldTy (owner, fname) with
         | Some "int" -> "i"
         | Some "float" -> "f"
         | Some "float32" -> "s"
         | Some "int64" -> "l"
         | _ -> "u")
    | ELit (LFloat t) ->
        if t.EndsWith "h" || t.EndsWith "H" then "u"
        elif t.EndsWith "f" || t.EndsWith "F" then "s"
        else "f"
    | ELit (LInt t) -> if t.EndsWith "L" then "l" else "i"
    | EUnknown n when n.StartsWith "$sizeof:" -> "i"
    | EPrim (op, _) when
        op.Length > 1 && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "-"; "*"; "/"; "%" ] ->
        let k = op.Substring (op.Length - 1)
        if k = "f" || k = "s" || k = "l" then k
        elif k = "p" then "i"
        else "u"
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
    | EApp (EUnknown "uint64", [ _ ]) -> "l"
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
        // uniform-representation struct tuples emit as boxed tuples, so
        // their arity needs a $tupN type too
        | ERecord (tn, fs) when tn.StartsWith "StructTuple" ->
            note (List.length fs)
            for _, v in fs do scan v
        | EField (r, fn2, owner) when owner.StartsWith "StructTuple" && fn2.StartsWith "Item" ->
            let core = (if owner.Contains "$<" then owner.Substring (0, owner.IndexOf "$<") else owner).Substring 11
            // the read may demand a larger arity than the owner names (an
            // inconsistent uniform template); the emitter casts to the
            // demanded arity, so that type must exist too
            let demanded =
                match parseDigits (fn2.Substring 4) with
                | Some k -> k
                | None -> 0
            (match parseDigits core with
             | Some v -> note (if demanded > v then demanded else v)
             | None -> note demanded)
            scan r
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
        | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) | EArrayBytes (_, a) -> scan a
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

/// the width of one backing word for this struct, and the suffix naming the
/// accessors that speak it
let private podW (st : St) (rn : string) : int =
    match dictTryFind st.PodAlign rn with Some a -> a | None -> 4
let private podK (st : St) (rn : string) : string =
    match dictTryFind st.PodKind rn with Some k -> k | None -> ""
let private podSfxOf (st : St) (rn : string) : string =
    Fpp.Backend.EmitBin.podSfx (podW st rn) (podK st rn)
let private podRtOf (st : St) (rn : string) = Fpp.Backend.EmitBin.podRtK (podW st rn) (podK st rn)
let private podTy (w : int) = match w with 1 -> "$pb" | 2 -> "$ph" | 4 -> "$pk" | _ -> "$pl"

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

/// push backing word `w` of the POD value in local `vl`. A leaf never
/// straddles a word (see the layout), so each leaf that lands in this word
/// contributes its bits shifted into place and the word is their union.
and private emitPodWord (st : St) (f : Fn) (rn : string) (vl : string) (w : int) : unit =
    emitPodWordOf st f rn (fun path k -> emitPodLeaf st f rn vl path k) w

/// the same, with the leaves coming from wherever the caller says
and private emitPodWordOf (st : St) (f : Fn) (rn : string) (push : string -> string -> unit) (w : int) : unit =
    let placed, _, _ = (dictTryFind st.Pod rn).Value
    if podK st rn <> "" then
        // one leaf per word, and the word IS the leaf: no bits to move
        match placed |> List.tryFind (fun (_, _, off) -> off / podW st rn = w) with
        | Some (fn, k, _) -> push fn k
        | None -> (if podK st rn = "f" then fc f 0L else sc f 0)
    else
    let width = podW st rn
    let wide = width = 8
    let sizeOfK (k : string) = match k with "b" | "n" -> 1 | "h" | "m" -> 2 | "i" | "s" -> 4 | _ -> 8
    let parts = placed |> List.filter (fun (_, _, off) -> off / width = w)
    /// the leaf's bits, in the WORD's type, shifted to its place in the word
    let one (fn : string, k : string, off : int) =
        push fn k
        // to raw bits, in the leaf's own width
        (match k with
         | "f" -> ins f "i64.reinterpret_f64"
         | "s" -> ins f "i32.reinterpret_f32"
         | "l" -> ()
         | "b" | "n" ->
             ic f 0xFF
             ins f "i32.and"
         | "h" | "m" ->
             ic f 0xFFFF
             ins f "i32.and"
         | _ -> ())
        // widen to the word, then shift into position
        let narrow = sizeOfK k <= 4
        if wide && narrow then ins f "i64.extend_i32_u"
        let sh = (off % width) * 8
        if sh <> 0 then
            if wide then
                lc f (int64 sh)
                ins f "i64.shl"
            else
                ic f sh
                ins f "i32.shl"
    match parts with
    | [] -> if wide then lc f 0L else ic f 0
    | first :: restP ->
        one first
        for p in restP do
            one p
            ins f (if wide then "i64.or" else "i32.or")

/// read the leaf of kind `k` at byte offset `off` out of the image: handle in
/// `hl`, the element's word base in `bl`.
and private emitPodLeafRead (st : St) (f : Fn) (rn : string) (hl : string) (bl : string) (k : string) (off : int) : unit =
    let width = podW st rn
    let wide = width = 8
    // INLINE rather than a call to $hwget. A call is an optimisation barrier:
    // the engine must assume it writes globals, so it cannot hoist the array
    // fetch or the casts that surround it out of a loop. Straight-line code
    // lets it. On a vertex sum this alone was 772ms -> 507ms.
    let ty, vt, getOp, loadOp, _ = podRtOf st rn
    let idx () =
        lg f bl
        ic f (off / width)
        ins f "i32.add"
    // the word, however it has to be reached — everything after this is the
    // same either way, so the match must not swallow it
    let everPinned = not st.Opt || (dictTryFind st.PinnedTypes rn).IsSome
    (match dictTryFind st.PodBase hl with
     | Some (sto, _) when not everPinned ->
         // nothing in the program pins this type, so the storage is there:
         // the load, and nothing else
         lg f sto
         idx ()
         gcT f getOp ty
     | Some (sto, ptr) ->
         // the base was hoisted: no global read, no casts, just the load
         lg f sto
         ins f "ref.is_null"
         ifV f vt
         lg f ptr
         idx ()
         ic f width
         ins f "i32.mul"
         ins f "i32.add"
         mem f loadOp
         elseB f
         lg f sto
         idx ()
         gcT f getOp ty
         endB f
     | None when not everPinned ->
         // never pinned anywhere, so the storage is always there: read it
         // without asking whether this array happens to be in linear memory
         lg f hl
         gcT f "ref.cast" "$hnd"
         gcTF f "struct.get" "$hnd" 0
         gcT f "ref.cast" ty
         idx ()
         gcT f getOp ty
     | None ->
         lg f hl
         gcT f "ref.cast" "$hnd"
         gcTF f "struct.get" "$hnd" 0
         ins f "ref.is_null"
         ifV f vt
         lg f hl
         gcT f "ref.cast" "$hnd"
         gcTF f "struct.get" "$hnd" 1
         idx ()
         ic f width
         ins f "i32.mul"
         ins f "i32.add"
         mem f loadOp
         elseB f
         lg f hl
         gcT f "ref.cast" "$hnd"
         gcTF f "struct.get" "$hnd" 0
         gcT f "ref.cast" ty
         idx ()
         gcT f getOp ty
         endB f)
    if podK st rn <> "" then
        // the value came out of the array already
        callf f (boxOfK k)
    else
    let sh = (off % width) * 8
    if sh <> 0 then
        if wide then
            lc f (int64 sh)
            ins f "i64.shr_u"
        else
            ic f sh
            ins f "i32.shr_u"
    // the word is i64 only when the struct is 8-aligned; a narrower leaf out
    // of one has to come down to i32 first
    let narrow = (match k with "b" | "n" | "h" | "i" | "s" -> true | _ -> false)
    if wide && narrow then ins f "i32.wrap_i64"
    match k with
    | "f" ->
        ins f "f64.reinterpret_i64"
        callf f "$off"
    | "l" -> callf f "$ofl"
    | "s" ->
        ins f "f32.reinterpret_i32"
        callf f "$oss"
    | "h" ->
        ic f 0xFFFF
        ins f "i32.and"
        callf f "$ofi"
    | "b" ->
        ic f 0xFF
        ins f "i32.and"
        callf f "$ofi"
    | "m" ->
        // int16: the stored half, sign-extended
        ic f 16
        ins f "i32.shl"
        ic f 16
        ins f "i32.shr_s"
        callf f "$ofi"
    | "n" ->
        // sbyte: the stored byte, sign-extended
        ic f 24
        ins f "i32.shl"
        ic f 24
        ins f "i32.shr_s"
        callf f "$ofi"
    | _ -> callf f "$ofi"

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
            emitPodLeafRead st f top hl bl k off
    gcT f "struct.new" ("$r_" + rn)

/// The split element a field chain reads from, and which of its leaves.
and private podElemRootOf (st : St) (e : Expr) : ((string * string * string) list * string) option =
    let rec root (x : Expr) : ((string * int) * string) option =
        match x with
        | EField (EVar (v, _), fn, _) -> Some ((v.Path, v.Offset), fn)
        | EField (inner, fn, _) ->
            (match root inner with
             | Some (k, p) -> Some (k, p + "." + fn)
             | None -> None)
        | _ -> None
    match root e with
    | Some (k, path) ->
        (match dictTryFind st.PodElem k with
         | Some slots -> Some (slots, path)
         | None -> None)
    | None -> None

/// Can this loop be unrolled twice, and if so what is the guard that says
/// two more iterations fit?
///
/// The shape looked for is the ordinary counted loop: `while i < bound` whose
/// body advances `i` by exactly one, once, and where `bound` does not change
/// while it runs. Then two iterations are safe exactly when the condition
/// still holds of `i + 1`, so the guard is the condition with `i + 1` in
/// place of `i` — no trip count, no arithmetic that could overflow where the
/// original would not.
///
/// Unrolling costs a copy of the body, so it is only worth it for a body
/// small enough that the loop's own overhead is a real share of the work.
and private unrollGuard (st : St) (c : Expr) (b : Expr) : Expr option =
    if not st.Opt then None
    else
        // the counter, and the comparison it rides in
        match c with
        | EPrim (op, [ EVar (iv, isch); bound ]) when
              (op = "<" || op = "<=" || (op.StartsWith "<" && op <> "<>")) ->
            let key = (iv.Path, iv.Offset)
            // A call cannot reach a LOCAL, so calls in the body are harmless
            // — unless the counter is captured, in which case it lives in a
            // cell that a closure could write, or it is a global.
            let reachable =
                (dictTryFind st.CellVars key).IsSome || (dictTryFind st.GlobalOf key).IsSome
            // `bound` must not move: a literal, or a variable nothing assigns
            let mutable bumps = 0
            let mutable otherAssign = false
            let mutable boundAssigned = false
            // INNERMOST loops only. Unrolling one that contains another copies
            // the inner loop too, and the copies multiply with depth — three
            // to the power of the nesting, which is how a two-deep loop turned
            // three element reads into twenty-seven.
            let mutable hasInnerLoop = false
            let boundKey =
                match bound with
                | EVar (bv, _) -> Some (bv.Path, bv.Offset)
                | _ -> None
            let rec scan (x : Expr) : unit =
                (match x with
                 | EAssign (av, rhs) ->
                     let ak = (av.Path, av.Offset)
                     if ak = key then
                         (match rhs with
                          | EPrim ("+", [ EVar (rv, _); ELit (LInt "1") ]) when (rv.Path, rv.Offset) = key ->
                              bumps <- bumps + 1
                          | _ -> otherAssign <- true)
                     if Some ak = boundKey then boundAssigned <- true
                 | EWhile _ -> hasInnerLoop <- true
                 | _ -> ())
                podScanChildren scan x
            scan b
            // and small enough to be worth copying
            let mutable size = 0
            let rec count (x : Expr) : unit =
                size <- size + 1
                podScanChildren count x
            count b
            let boundReachable =
                match boundKey with
                // a global bound is only safe if it is a CONSTANT: those are
                // emitted as their literal and nothing can write them
                | Some bk ->
                    (dictTryFind st.ConstGlobal bk).IsNone
                    && ((dictTryFind st.CellVars bk).IsSome || (dictTryFind st.GlobalOf bk).IsSome)
                | None -> false
            if bumps = 1 && not otherAssign && not boundAssigned && not hasInnerLoop
               && not reachable && not boundReachable && size <= 60 then
                Some (EPrim (op, [ EPrim ("+", [ EVar (iv, isch); ELit (LInt "1") ]); bound ]))
            else None
        | _ -> None

/// Store one backing word. The read path was inlined, hoisted and stripped of
/// its pin test long before this one was, and the asymmetry cost more than
/// everything the read path gained: filling a 1M-element array called a
/// runtime function three times per element, each re-reading the global and
/// casting twice. Same treatment here.
and private emitPodWordStore (st : St) (f : Fn) (nm : string) (hl : string) (bl : string) (w : int)
                             (pushValue : unit -> unit) : unit =
    let width = podW st nm
    let ty, _, _, _, storeOp = podRtOf st nm
    let everPinned = not st.Opt || (dictTryFind st.PinnedTypes nm).IsSome
    let idx () =
        lg f bl
        ic f w
        ins f "i32.add"
    if everPinned then
        match (if st.Opt then dictTryFind st.PodBase hl else None) with
        | Some (sto, ptr) ->
            // the base and the linear pointer are HOISTED: test the pin on
            // the hoisted storage inline, exactly as the read path does. A
            // program that pins f32 arrays ANYWHERE (float formatting does)
            // marks the whole kind ever-pinned, and a store in a hot fill
            // loop was paying a call plus two casts per word for it —
            // hwsets was 17% of the vertex benchmark.
            lg f sto
            ins f "ref.is_null"
            ifE f
            lg f ptr
            idx ()
            ic f width
            ins f "i32.mul"
            ins f "i32.add"
            pushValue ()
            mem f storeOp
            elseB f
            lg f sto
            idx ()
            pushValue ()
            gcT f "array.set" ty
            endB f
        | None ->
            // the array may be in linear memory: the runtime function decides
            podPushHandle st f hl
            idx ()
            pushValue ()
            callf f ("$hwset" + podSfxOf st nm)
    else
        (match dictTryFind st.PodBase hl with
         | Some (sto, _) -> lg f sto
         | None ->
             podPushHandle st f hl
             gcT f "ref.cast" "$hnd"
             gcTF f "struct.get" "$hnd" 0
             gcT f "ref.cast" ty)
        idx ()
        pushValue ()
        gcT f "array.set" ty

/// A statically all-zero init value: `array.new_default` already IS this
/// fill for a packed array. LNull counts — a POD layout has no reference
/// slots, so null only ever spells a numeric zero here.
and private podIsZeroInit (e : Expr) : bool =
    match e with
    | ERecord (_, fs) -> fs |> List.forall (fun (_, x) -> podIsZeroInit x)
    | ELit (LInt "0") | ELit (LInt "0L") -> true
    | ELit (LFloat "0.0") | ELit (LFloat "0.0f") -> true
    | ELit LNull -> true
    | _ -> false

/// Push the handle. `hl` is normally a local, but for an array whose base a
/// loop hoisted it is the GLOBAL's name — the write paths still want the
/// handle itself, so fetch it straight from the global there.
and private podPushHandle (st : St) (f : Fn) (hl : string) : unit =
    if (dictTryFind st.PodBase hl).IsSome then gg f hl else lg f hl

/// every sub-expression, exhaustively — a case missed here could hide an
/// `Array.pin` and let a stale base be hoisted over it
and private podScanChildren (g : Expr -> unit) (e : Expr) : unit =
    match e with
    | ELam (_, b) -> g b
    | EApp (h, args) -> g h; List.iter g args
    | ELet (_, _, _, r, b) -> g r; g b
    | EIf (a, b, c) -> g a; g b; g c
    | EMatch (s, cs) ->
        g s
        for _, gd, b in cs do
            (match gd with Some x -> g x | None -> ())
            g b
    | ETuple xs | EListLit xs | ESeq xs -> List.iter g xs
    | EPrim (_, xs) -> List.iter g xs
    | ECtor (_, _, xs) -> List.iter g xs
    | ERecord (_, fs) -> for _, v in fs do g v
    | ERecordExt (_, b, fs) ->
        g b
        for _, v in fs do g v
    | EField (x, _, _) -> g x
    | EIfaceCall (_, _, recv, args) -> g recv; List.iter g args
    | ECast (_, x, _) -> g x
    | ETypeTest (_, x) -> g x
    | EFieldSet (x, _, _, v) -> g x; g v
    | EWhile (c, b) -> g c; g b
    | EAssign (_, x) -> g x
    | EArray (_, xs) -> List.iter g xs
    | EIndex (_, a, i) -> g a; g i
    | EIndexSet (_, a, i, v) -> g a; g i; g v
    | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) | EArrayBytes (_, a) -> g a
    | EArrayCreate (_, a, b) -> g a; g b
    | ETry (b, cs) ->
        g b
        for _, gd, x in cs do
            (match gd with Some y -> g y | None -> ())
            g x
    | _ -> ()

/// The handle a POD access reads through. When the array is a top-level
/// binding whose base this loop already hoisted, the key IS the global name
/// and nothing is emitted; otherwise the handle goes into a fresh local as
/// before.
and private podHandleLocal (st : St) (f : Fn) (lv : Dict<string * int, string>) (a : Expr) : string =
    let hoisted =
        match a with
        | EVar (v, _) ->
            (match dictTryFind st.GlobalOf (v.Path, v.Offset) with
             | Some g when (dictTryFind st.PodBase g).IsSome -> Some g
             | _ -> None)
        | _ -> None
    match hoisted with
    | Some g -> g
    | None ->
        let hl = freshLocal f "$pha" "anyref"
        emitNode st f lv a
        ls f hl
        hl

/// Hoist the base of every POD array a loop reads out of the loop. The base —
/// the storage and the pin pointer — cannot change while the loop runs, so
/// fetching it once turns each access from `global.get; ref.cast; struct.get;
/// ref.cast; array.get` into a single load. Returns the globals registered,
/// for the caller to drop afterwards: the locals only hold the base from here
/// to the end of the loop, and code on another path must not read them.
and private podHoistLoop (st : St) (f : Fn) (parts : Expr list) : string list =
    let cand = dictNew<string, string> ()
    let mutable blocked = not st.Opt
    let rec scan (e : Expr) : unit =
        // pinning MOVES the storage, so a loop that pins keeps its base fresh
        (match e with
         | EArrayPin _ | EArrayUnpin _ -> blocked <- true
         | _ -> ())
        let note (nm : string) (a : Expr) =
            match a with
            | EVar (v, _) when (dictTryFind st.Pod nm).IsSome ->
                (match dictTryFind st.GlobalOf (v.Path, v.Offset) with
                 | Some g -> dictSet cand g nm
                 | None -> ())
            | _ -> ()
        (match e with
         | EIndex (nm, a, _) | EIndexSet (nm, a, _, _) -> note nm a
         | EField (EIndex (nm, a, _), _, _) -> note nm a
         | _ -> ())
        podScanChildren scan e
    for p in parts do scan p
    if blocked then []
    else
        let out = vecNew<string> ()
        // an enclosing loop may already have hoisted it; re-doing it here
        // would only clobber that registration and drop it early
        for g, nm in dictPairs cand do
          if not (dictTryFind st.PodBase g).IsSome then
            let width = podW st nm
            let ty, _, _, _, _ = podRtOf st nm
            let sto = freshLocal f "$pbs" ty
            let ptr = freshLocal f "$pbp" "i32"
            // storage, kept NULLABLE: a pinned array has none, and the
            // pointer path below is exactly what serves that case
            gg f g
            gcT f "ref.cast" "$hnd"
            gcTF f "struct.get" "$hnd" 0
            gcT f "ref.cast_null" ty
            ls f sto
            gg f g
            gcT f "ref.cast" "$hnd"
            gcTF f "struct.get" "$hnd" 1
            ls f ptr
            dictSet st.PodBase g (sto, ptr)
            vecAdd out g
        vecToList out

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
                else
                    // WRAP rather than throw: `-2147483648` lexes as unary
                    // minus over 2147483648, which does not fit an int32 —
                    // and wrapping gives exactly the bit pattern the negation
                    // then turns into the intended value. An unhandled
                    // OverflowException here crashed the whole compile.
                    // The SIGN is handled here, not by the parser: the two
                    // hosts' parseInt64In disagree about a leading '-' (the
                    // bootstrap one reads digits only), and that silently
                    // turned every `-1` into `1` in the self-hosted stage.
                    // int-of-int64 truncates, so an out-of-range magnitude
                    // wraps to the bit pattern the negation then completes.
                    let neg = digits.StartsWith "-"
                    let mag = if neg then digits.Substring 1 else digits
                    let v = int (parseInt64In 10 (if mag = "" then "0" else mag))
                    if neg then 0 - v else v
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
        pushUnit f
    | EUnknown n when n.StartsWith "$zero:" ->
        // the zero of a stamped `defaultof<'T>`: scalars get 0, the
        // rest (refs, $ref, still-symbolic canon copies) get null
        (match n.Substring 6 with
         | "int" | "bool" | "char" | "byte" | "sbyte" | "int16" | "uint16" | "uint32" -> ic f 0; refI31 f
         | "int64" | "uint64" -> lc f 0L; callf f "$ofl"
         | "float" | "float32" -> fc f 0L; callf f "$off"
         | _ -> refNull f "any")
    | EUnknown n when n.StartsWith "$sizeof:" ->
        // the byte size of the named type, from the SAME tables the layouts
        // come from: primitives at C's widths, a POD struct at its computed
        // layout size, any reference at pointer width
        let tn = n.Substring 8
        let size =
            match tn with
            | "byte" | "sbyte" | "bool" -> 1
            | "char" | "int16" | "uint16" | "float16" -> 2
            // the oracle's pointers ARE linear-memory offsets: 4 bytes
            | "int" | "uint32" | "float32" | "nativeint" | "unativeint" -> 4
            | "int64" | "uint64" | "float" -> 8
            | _ ->
                match dictTryFind st.Pod tn with
                | Some (_, sz, _) -> sz
                | None -> 8
        emitNode st f lv (ELit (LInt (string size)))
    | ELit LNull -> refNull f "any"
    | ELit (LString raw) ->
        let bytes = unescape raw
        let dn, _ = internStr st bytes
        gg f ("$sl:" + dn)
    | ESeq xs ->
        (match List.rev xs with
         | [] ->
             pushUnit f
         | last :: initRev ->
             for x in List.rev initRev do
                 emitNode st f lv x
                 dropU f
             emitNode st f lv last)
    | EVarI (v, sch, _) -> emitNode st f lv (EVar (v, sch))
    | EVar (v, _) when st.Opt && (dictTryFind st.ConstGlobal (v.Path, v.Offset)).IsSome
                       && not (dictTryFind lv (v.Path, v.Offset)).IsSome ->
        emitNode st f lv (dictTryFind st.ConstGlobal (v.Path, v.Offset)).Value
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
             ic f (tblIdx f.M (fn + ".w0"))
             refNull f "any"
             gcT f "struct.new" "$clo"
         | _ ->
             err st ("binary: unbound variable " + v.Name + " @" + v.Path + ":" + string v.Offset)
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
                // a binding is a step point for a debugger
                markSrc f v.Path v.Offset
                let nameIt (l : string) = nameLocal f l v.Name
                let key = (v.Path, v.Offset)
                // A POD element read into a local: take the fields, not the
                // struct. Only when every use in the body IS a field read —
                // anything that wants the element itself still gets one.
                let elemSplit =
                    if not st.Opt then None
                    else
                        match rhs with
                        | EIndex (nm, a, i) when (dictTryFind st.Pod nm).IsSome
                                                 && (dictTryFind st.CellVars key).IsNone
                                                 && (dictTryFind st.InLambda key).IsNone ->
                            let placed, _, _ = (dictTryFind st.Pod nm).Value
                            if List.length placed > 8 then None
                            else
                                let mutable ok = true
                                let rec chk (x : Expr) : unit =
                                    match podVarChainOf key x with
                                    | Some path ->
                                        // a chain that lands on a leaf is fine;
                                        // one that stops at an inner struct is
                                        // asking for the struct itself
                                        if not (placed |> List.exists (fun (p, _, _) -> p = path)) then ok <- false
                                    | None ->
                                        match x with
                                        | EVar (bv, _) when (bv.Path, bv.Offset) = key -> ok <- false
                                        | _ -> podScanChildren chk x
                                chk body
                                if ok then Some (nm, a, i, placed) else None
                        | _ -> None
                match elemSplit with
                | Some (nm, a, i, placed) ->
                    let _, _, wd = (dictTryFind st.Pod nm).Value
                    let hl = podHandleLocal st f lv a
                    let bl = freshLocal f "$peb" "i32"
                    emitNode st f lv i
                    callf f "$toi"
                    ic f wd
                    ins f "i32.mul"
                    ls f bl
                    let slots =
                        placed |> List.map (fun (path, kd, off) ->
                            let ty = match kd with "f" -> "f64" | "s" -> "f32" | "l" -> "i64" | _ -> "i32"
                            let l = freshLocal f "$pef" ty
                            emitPodLeafRead st f nm hl bl kd off
                            callf f (podUnbox kd)
                            ls f l
                            path, kd, l)
                    dictSet st.PodElem key slots
                    // the spine has to advance on THIS path too
                    cur <- body
                | None ->
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
                    nameIt l
                    dictSet st.LocalKind key k
                    dictSet lv key l
                    ls f l
                else
                    emitNode st f lv rhs
                    // a captured mutable: the frame holds the CELL, not the value
                    if (dictTryFind st.CellVars key).IsSome then
                        gcT f "struct.new" "$cell"
                    let l = freshLocal f "$bl" "anyref"
                    nameIt l
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
                     pushUnit f
                 elif fname = "__desc" && (dictTryFind st.ObjRec rn).IsSome then
                     gg f ("$desc_" + rn)
                 else
                     match fields |> List.tryFind (fun (fn, _) -> fn = fname) with
                     | Some (_, v) -> emitNode st f lv v
                     | None ->
                         match baseRn with
                         | Some bn when i < baseLen ->
                             // cast to the TOPMOST ancestor declaring slot i:
                             // an instantiation subclass's base value is the
                             // ORIGINAL base class's instance, not the
                             // template's — the shared prefix is what makes
                             // the index valid, so name the type that owns it
                             let rec ancestorFor (t : string) : string =
                                 match dictTryFind st.BaseOf t with
                                 | Some p ->
                                     (match dictTryFind st.FieldsOf p with
                                      | Some o when i < o.Length -> ancestorFor p
                                      | _ -> t)
                                 | None -> t
                             let tn = ancestorFor bn
                             lg f bl
                             gcT f "ref.cast" ("$r_" + tn)
                             gcTF f "struct.get" ("$r_" + tn) i
                         | Some _ ->
                             err st ("binary: missing field " + fname + " in " + rn + " (have " + String.concat "," (fields |> List.map fst) + ")")
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
                  // a MULTI-payload case (an existential packs its member
                  // fns as extra slots): the one payload slot holds a tuple
                  let tn = "$tup" + string (List.length many)
                  for a in many do emitNode st f lv a
                  gcT f "struct.new" tn)
             gcT f "struct.new" "$du1"
         | Some 1 ->
             // the constructor as a VALUE (`|> Some`): a closure whose
             // function builds the case; body emitted with the wrapper tail
             if not (dictTryFind st.CtorFns name).IsSome then
                 dictSet st.CtorFns name true
                 vecAdd st.LateFns ("c:" + name)
                 declFn f.M ("$ctorfn_" + name) "$u1"
             ic f (tblIdx f.M ("$ctorfn_" + name))
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
        pushUnit f
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
    | EApp (EUnknown "$str.ToUpper", [ s ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        callf f "$strUpper"
    | EApp (EUnknown "$str.ToLower", [ s ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        callf f "$strLower"
    // $strPad's flag means "content on the LEFT", so PadLeft (which pads on
    // the left and right-aligns the content) passes 0
    | EApp (EUnknown "$str.PadLeft", [ s; w ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv w
        callf f "$toi"
        ic f 32
        ic f 0
        callf f "$strPad"
    | EApp (EUnknown "$str.PadRight", [ s; w ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv w
        callf f "$toi"
        ic f 32
        ic f 1
        callf f "$strPad"
    | EApp (EUnknown "$str.ToCharArray", [ s ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        callf f "$strChars"
    // `TrimStart c` is the second overload; the runtime takes either a char or
    // a set, so both spellings emit the same call
    | EApp (EUnknown "$str.TrimStart", [ s; cs ])
    | EApp (EUnknown "$str.TrimStart#2", [ s; cs ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv cs
        callf f "$strTrimStartChars"
    | EApp (EUnknown "$str.Insert", [ s; i; v ]) ->
        // s.[0..i-1] + v + s.[i..]
        let sl = freshLocal f "$sia" "anyref"
        let il = freshLocal f "$sii" "i32"
        emitNode st f lv s
        ls f sl
        emitNode st f lv i
        callf f "$toi"
        ls f il
        lg f sl
        gcT f "ref.cast" "$str"
        ic f 0
        lg f il
        callf f "$strsub"
        gcT f "ref.cast" "$str"
        emitNode st f lv v
        gcT f "ref.cast" "$str"
        callf f "$strcat"
        gcT f "ref.cast" "$str"
        lg f sl
        gcT f "ref.cast" "$str"
        lg f il
        lg f sl
        gcT f "ref.cast" "$str"
        gci f "array.len"
        lg f il
        ins f "i32.sub"
        callf f "$strsub"
        gcT f "ref.cast" "$str"
        callf f "$strcat"
    | EApp (EUnknown "$str.Remove", [ s; i ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        ic f 0
        emitNode st f lv i
        callf f "$toi"
        callf f "$strsub"
    | EApp (EUnknown "$str.Remove#2", [ s; i; n ]) ->
        // the head before i, then the tail after i+n
        let sl = freshLocal f "$sra" "anyref"
        let il = freshLocal f "$sri" "i32"
        let nl = freshLocal f "$srn" "i32"
        emitNode st f lv s
        ls f sl
        emitNode st f lv i
        callf f "$toi"
        ls f il
        emitNode st f lv n
        callf f "$toi"
        ls f nl
        lg f sl
        gcT f "ref.cast" "$str"
        ic f 0
        lg f il
        callf f "$strsub"
        gcT f "ref.cast" "$str"
        lg f sl
        gcT f "ref.cast" "$str"
        lg f il
        lg f nl
        ins f "i32.add"
        lg f sl
        gcT f "ref.cast" "$str"
        gci f "array.len"
        lg f il
        ins f "i32.sub"
        lg f nl
        ins f "i32.sub"
        callf f "$strsub"
        gcT f "ref.cast" "$str"
        callf f "$strcat"
    | EApp (EUnknown "$str.StartsWith#2", [ s; c ]) ->
        // the CHAR overload: first byte, empty string is false
        let sl = freshLocal f "$ssa" "anyref"
        emitNode st f lv s
        ls f sl
        lg f sl
        gcT f "ref.cast" "$str"
        gci f "array.len"
        ic f 0
        ins f "i32.gt_u"
        ifV f "i32"
        lg f sl
        gcT f "ref.cast" "$str"
        ic f 0
        gcT f "array.get_u" "$str"
        emitNode st f lv c
        callf f "$toi"
        ins f "i32.eq"
        elseB f
        ic f 0
        endB f
        refI31 f
    | EApp (EUnknown "$str.EndsWith#2", [ s; c ]) ->
        let sl = freshLocal f "$sea" "anyref"
        emitNode st f lv s
        ls f sl
        lg f sl
        gcT f "ref.cast" "$str"
        gci f "array.len"
        ic f 0
        ins f "i32.gt_u"
        ifV f "i32"
        lg f sl
        gcT f "ref.cast" "$str"
        lg f sl
        gcT f "ref.cast" "$str"
        gci f "array.len"
        ic f 1
        ins f "i32.sub"
        gcT f "array.get_u" "$str"
        emitNode st f lv c
        callf f "$toi"
        ins f "i32.eq"
        elseB f
        ic f 0
        endB f
        refI31 f
    | EApp (EUnknown "$str.Contains#2", [ s; c ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv c
        callf f "$toi"
        callf f "$strFindChar"
        ic f 0
        ins f "i32.ge_s"
        refI31 f
    | EApp (EUnknown "$str.TrimEnd", [ s; cs ])
    | EApp (EUnknown "$str.TrimEnd#2", [ s; cs ]) ->
        emitNode st f lv s
        gcT f "ref.cast" "$str"
        emitNode st f lv cs
        callf f "$strTrimEndChars"
    | EIfaceCall (iface, mname, recv, args) ->
        (match dictTryFind st.SlotOf ((match iface.IndexOf '`' with | i when i > 0 -> iface.Substring (0, i) | _ -> iface), mname) with
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
             elif iface = "IEnumerator" && mname = "Dispose" then
                 // the built-in list/array iterator has no vtable and holds
                 // nothing to release, so disposing it is a no-op
                 lg f t
                 gcT f "ref.test" "$iter"
                 ifA f
                 pushUnit f
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
        // An INSTANTIATED name (a stamped `:? 'T`) tests its erased head:
        // the descriptor does not carry type arguments.
        let tn = if tn.Contains "$<" then tn.Substring (0, tn.IndexOf "$<") else tn
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
        let tn = if tn.Contains "$<" then tn.Substring (0, tn.IndexOf "$<") else tn
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
                 emitNode st f lv (ELit (LString ("\"invalid cast to " + tn + " from typeid \"")))
                 gcT f "ref.cast" "$str"
                 lg f t
                 gcT f "ref.cast" "$obj"
                 gcTF f "struct.get" "$obj" 0
                 gcT f "ref.cast" "$desc"
                 gcTF f "struct.get" "$desc" 0
                 callf f "$itoa"
                 gcT f "ref.cast" "$str"
                 callf f "$strcat"
                 gcT f "struct.new" "$du1"
                 throwExn f
             | None -> ins f "unreachable")
            endB f
    // the shadow stack, readable from the program itself
    | EApp (EUnknown "stackDepth", [ _ ]) ->
        if (dictTryFind f.M.GlobalIdx "$dbgDepth").IsSome then gg f "$dbgDepth" else ic f 0
        callf f "$ofi"
    | EApp (EUnknown "stackFrame", [ i ]) ->
        if (dictTryFind f.M.GlobalIdx "$dbgDepth").IsSome then
            gg f "$dbgFrames"
            emitNode st f lv i
            callf f "$toi"
            ic f 512
            ins f "i32.rem_u"
            gcT f "array.get" "$parr_i"
        else ic f 0
        callf f "$ofi"
    // ---- raw linear memory ------------------------------------------------
    // The pin heap is where a pinned POD array already lives, so a serializer
    // that writes here can BLIT such an array instead of walking it: one
    // memory.copy, whatever the element type.
    // ---- the JavaScript boundary ------------------------------------------
    // objects cross as externref (one conversion instruction each way);
    // property keys stage as (ptr, len) UTF-8 so an access is ONE crossing
    | EApp (EUnknown "jsGlobal", [ k ]) ->
        emitNode st f lv k
        callf f "$jsstage"
        callf f "$js_global"
        toAny f
    | EApp (EUnknown "jsGet", [ o; k ]) ->
        emitNode st f lv o
        toExtern f
        emitNode st f lv k
        callf f "$jsstage"
        callf f "$js_get"
        toAny f
    | EApp (EUnknown "jsSet", [ o; k; v ]) ->
        emitNode st f lv o
        toExtern f
        emitNode st f lv k
        callf f "$jsstage"
        emitNode st f lv v
        toExtern f
        callf f "$js_set"
        pushUnit f
    | EApp (EUnknown "jsGetNum", [ o; k ]) ->
        emitNode st f lv o
        toExtern f
        emitNode st f lv k
        callf f "$jsstage"
        callf f "$js_getNum"
        callf f "$off"
    | EApp (EUnknown "jsSetNum", [ o; k; v ]) ->
        emitNode st f lv o
        toExtern f
        emitNode st f lv k
        callf f "$jsstage"
        emitNode st f lv v
        callf f "$tof"
        callf f "$js_setNum"
        pushUnit f
    | EApp (EUnknown "jsItem", [ o; i ]) ->
        emitNode st f lv o
        toExtern f
        emitNode st f lv i
        callf f "$toi"
        callf f "$js_item"
        toAny f
    | EApp (EUnknown "jsItemSet", [ o; i; v ]) ->
        emitNode st f lv o
        toExtern f
        emitNode st f lv i
        callf f "$toi"
        emitNode st f lv v
        toExtern f
        callf f "$js_itemSet"
        pushUnit f
    | EApp (EUnknown cn, o :: k :: rest) when cn.StartsWith "jsCall" && strLen cn = 7 ->
        emitNode st f lv o
        toExtern f
        emitNode st f lv k
        callf f "$jsstage"
        for a in rest do
            emitNode st f lv a
            toExtern f
        callf f ("$js_call" + cn.Substring (strLen cn - 1))
        toAny f
    | EApp (EUnknown cn, ctor :: rest) when cn.StartsWith "jsNew" && strLen cn = 6 ->
        emitNode st f lv ctor
        toExtern f
        for a in rest do
            emitNode st f lv a
            toExtern f
        callf f ("$js_new" + cn.Substring (strLen cn - 1))
        toAny f
    | EApp (EUnknown "jsOfNum", [ a ]) ->
        emitNode st f lv a
        callf f "$tof"
        callf f "$js_num"
        toAny f
    | EApp (EUnknown "jsToNum", [ a ]) ->
        emitNode st f lv a
        toExtern f
        callf f "$js_toNum"
        callf f "$off"
    | EApp (EUnknown "jsToBool", [ a ]) ->
        emitNode st f lv a
        toExtern f
        callf f "$js_toBool"
        refI31 f
    | EApp (EUnknown "jsOfString", [ a ]) ->
        emitNode st f lv a
        callf f "$jsstage"
        callf f "$js_strNew"
        toAny f
    | EApp (EUnknown "jsToString", [ a ]) ->
        // two crossings: byte length (the glue caches the encoding), then
        // encodeInto the scratch; the $str is built from those bytes
        let jh = freshLocal f "$jh" "externref"
        let jp = freshLocal f "$jp" "i32"
        emitNode st f lv a
        toExtern f
        ls f jh
        lg f jh
        callf f "$js_strLen"
        callf f "$jsensure"
        ls f jp
        lg f jp
        lg f jh
        lg f jp
        callf f "$js_strWrite"
        callf f "$jsunstage"
    | EApp (EUnknown "jsCallback", [ clo ]) ->
        emitNode st f lv clo
        callf f "$js_mkFn"
        toAny f
    | EApp (EUnknown "jsNull", [ _ ]) ->
        refNull f "any"
    | EApp (EUnknown "jsIsNull", [ a ]) ->
        emitNode st f lv a
        ins f "ref.is_null"
        refI31 f
    // zero-copy TypedArray views over the exported linear memory at a
    // PINNED address: the JS side sees the array's real storage, both sides
    // alias, nothing copies
    | EApp (EUnknown vn, [ p; n ]) when vn.StartsWith "jsView" ->
        emitNode st f lv p
        callf f "$toi"
        emitNode st f lv n
        callf f "$toi"
        callf f ("$js_view" + vn.Substring 6)
        toAny f
    | EApp (EUnknown "memAlloc", [ n ]) ->
        emitNode st f lv n
        callf f "$toi"
        callf f "$balloc"
        callf f "$ofi"
    | EApp (EUnknown "memSize", [ _ ]) ->
        emitByte f.B 0x3F
        emitByte f.B 0
        ic f 16
        ins f "i32.shl"
        callf f "$ofi"
    | EApp (EUnknown "memCopy", [ dst; src; n ]) ->
        emitNode st f lv dst
        callf f "$toi"
        emitNode st f lv src
        callf f "$toi"
        emitNode st f lv n
        callf f "$toi"
        memCopy f
        pushUnit f
    | EApp (EUnknown "memLoadByte", [ p ]) ->
        emitNode st f lv p
        callf f "$toi"
        mem f "i32.load8_u"
        callf f "$ofi"
    | EApp (EUnknown "memStoreByte", [ p; v ]) ->
        emitNode st f lv p
        callf f "$toi"
        emitNode st f lv v
        callf f "$toi"
        mem f "i32.store8"
        pushUnit f
    | EApp (EUnknown "memLoadInt", [ p ]) ->
        emitNode st f lv p
        callf f "$toi"
        mem f "i32.load"
        callf f "$ofi"
    | EApp (EUnknown "memStoreInt", [ p; v ]) ->
        emitNode st f lv p
        callf f "$toi"
        emitNode st f lv v
        callf f "$toi"
        mem f "i32.store"
        pushUnit f
    | EApp (EUnknown "memLoadInt64", [ p ]) ->
        emitNode st f lv p
        callf f "$toi"
        mem f "i64.load"
        callf f "$ofl"
    | EApp (EUnknown "memStoreInt64", [ p; v ]) ->
        emitNode st f lv p
        callf f "$toi"
        emitNode st f lv v
        callf f "$tol"
        mem f "i64.store"
        pushUnit f
    | EApp (EUnknown "memLoadFloat", [ p ]) ->
        emitNode st f lv p
        callf f "$toi"
        mem f "f64.load"
        callf f "$off"
    | EApp (EUnknown "memStoreFloat", [ p; v ]) ->
        emitNode st f lv p
        callf f "$toi"
        emitNode st f lv v
        callf f "$tof"
        mem f "f64.store"
        pushUnit f
    | EUnknown "hash" ->
        requestWrapper st f "$hashvBoxed" 1
        ic f (tblIdx f.M "$hashvBoxed.w0")
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
    | EApp (EUnknown "$forcecell", [ r ]) ->
        // marker only: the ELet's own cell-wrapping does the rest
        emitNode st f lv r
    | EApp (EUnknown "$cellof", [ EVar (v, _) ]) ->
        // the CELL itself, not its contents — what the instance field stores
        (match dictTryFind lv (v.Path, v.Offset) with
         | Some l when l.StartsWith "@env:" ->
             lg f "$env"
             gcT f "ref.cast" "$arr"
             ic f (int (l.Substring 5))
             gcT f "array.get" "$arr"
         | Some l -> lg f l
         | None ->
             err st ("binary: $cellof outside the constructor: " + v.Name)
             refNull f "any")
    | EApp (EUnknown "$cellget", [ inner ]) ->
        emitNode st f lv inner
        gcT f "ref.cast" "$cell"
        gcTF f "struct.get" "$cell" 0
    | EApp (EUnknown "$cellset", [ target; value ]) ->
        emitNode st f lv target
        gcT f "ref.cast" "$cell"
        emitNode st f lv value
        gcTF f "struct.set" "$cell" 0
        pushUnit f
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
    // the identity hash, boxed for expression position
    | EApp (EUnknown "$hasflag", [ a; b ]) ->
        // enum HasFlag: (a &&& b) = b on the int representation
        let t = freshLocal f "$bq" "anyref"
        emitNode st f lv b
        ls f t
        emitNode st f lv a
        callf f "$toi"
        lg f t
        callf f "$toi"
        ins f "i32.and"
        lg f t
        callf f "$toi"
        ins f "i32.eq"
        refI31 f
    | EApp (EUnknown "$idhash", [ a ]) ->
        emitNode st f lv a
        callf f "$idhash"
        refI31 f
    | EUnknown n when n = "$class:Ordered:compare:$ref" || n.StartsWith "$class:Ordered:compare:$tup" ->
        // `compare` at a UNIFORM reference: the runtime compares structurally.
        // A TUPLE spells its dispatch name by arity ("$tup2$<int.int>") so
        // Arb and friends can tell pair from triple — but its representation
        // is the same uniform reference, and the structural walk is still
        // the comparison
        requestWrapper st f "$cmpvBoxed" 2
        ic f (tblIdx f.M "$cmpvBoxed.w0")
        refNull f "any"
        gcT f "struct.new" "$clo"
    | EUnknown n when n.StartsWith "$class:Ordered:compare:" && n.Contains "#" ->
        // an UNSTAMPED template's compare — the operand type is a variable
        // that canonical (all-reference) code never substitutes. The runtime
        // $cmpv dispatches through the descriptor's compare slot, so the
        // value's OWN ordering applies; structural is the fallback.
        requestWrapper st f "$cmpvBoxed" 2
        ic f (tblIdx f.M "$cmpvBoxed.w0")
        refNull f "any"
        gcT f "struct.new" "$clo"
    | EApp (EUnknown n, [ a; b ]) when n.StartsWith "$class:Ordered:compare:" && n.Contains "#" ->
        emitNode st f lv a
        emitNode st f lv b
        callf f "$cmpv"
        callf f "$ofi"
    | EApp (EUnknown n, [ a ]) when n.Contains "#" && not (n.StartsWith "pad") ->
        // conversions whose source kind inference resolved: target#srckind.
        // nativeint IS int here — the oracle's addresses are i32 offsets —
        // so both the target and the source kind collapse onto the int rail
        let target =
            let t = n.Substring (0, n.IndexOf "#")
            if t = "nativeint" then "int" else t
        let src =
            let k = n.Substring (n.IndexOf "#" + 1)
            if k = "p" then "" else k
        let emitA () = emitNode st f lv a
        let strA () = emitA (); gcT f "ref.cast" "$str"
        let mask8 () = ic f 255; ins f "i32.and"
        let sext8 () = ic f 24; ins f "i32.shl"; ic f 24; ins f "i32.shr_s"
        let mask16 () = ic f 0xFFFF; ins f "i32.and"
        let sext16 () = ic f 16; ins f "i32.shl"; ic f 16; ins f "i32.shr_s"
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
         | "string", "v" -> emitA (); callf f "$tol"; callf f "$ultoa"
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
         | "uint16", "l" -> emitA (); callf f "$tol"; ins f "i32.wrap_i64"; mask16 (); callf f "$ofi"
         | "uint16", "f" -> emitA (); callf f "$tof"; ins f "i32.trunc_f64_s"; mask16 (); callf f "$ofi"
         | "uint16", "s" -> emitA (); callf f "$tos"; ins f "i32.trunc_f32_s"; mask16 (); callf f "$ofi"
         | "uint16", _ -> emitA (); callf f "$toi"; mask16 (); callf f "$ofi"
         | "int16", "l" -> emitA (); callf f "$tol"; ins f "i32.wrap_i64"; sext16 (); callf f "$ofi"
         | "int16", "f" -> emitA (); callf f "$tof"; ins f "i32.trunc_f64_s"; sext16 (); callf f "$ofi"
         | "int16", "s" -> emitA (); callf f "$tos"; ins f "i32.trunc_f32_s"; sext16 (); callf f "$ofi"
         | "int16", _ -> emitA (); callf f "$toi"; sext16 (); callf f "$ofi"
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
    | EApp (EUnknown "uint64", [ a ]) ->
        (match kindOfLite st a with
         | "l" -> emitNode st f lv a
         | "f" -> emitNode st f lv a; callf f "$tof"; ins f "i64.trunc_f64_u"; callf f "$ofl"
         | "s" -> emitNode st f lv a; callf f "$tos"; ins f "i64.trunc_f32_u"; callf f "$ofl"
         // an int widens UNSIGNED into a uint64: `uint64 -1` is 2^64-1 only
         // if the source was already unsigned, and F# agrees
         | "w" -> emitNode st f lv a; callf f "$toi"; ins f "i64.extend_i32_u"; callf f "$ofl"
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
        pushUnit f
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
        pushUnit f
    | EApp (EUnknown "printc", [ a ]) ->
        // a char prints as the character, not its code
        emitNode st f lv a
        callf f "$toi"
        callf f "$putc"
        ic f 10
        callf f "$putc"
        pushUnit f
    | EApp (EUnknown "prints", [ a ]) ->
        emitNode st f lv a
        gcT f "ref.cast" "$str"
        callf f "$prints"
        pushUnit f
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
    | EPrim (op, [ a; b ]) when
        (op.StartsWith "=@" || op.StartsWith "<>@")
        && (dictTryFind st.EnumLikeUnion (op.Substring (op.IndexOf "@" + 1))).IsSome ->
        // every case is nullary, so the values ARE the module's singletons:
        // one ref.eq replaces the whole structural walk (the parser compares
        // token kinds constantly)
        emitNode st f lv a
        castEq f
        emitNode st f lv b
        castEq f
        ins f "ref.eq"
        (if op.StartsWith "<>@" then ins f "i32.eqz")
        refI31 f
    | EPrim (op, [ a; b ]) when op.StartsWith "=@" || op.StartsWith "<>@" ->
        // an equality whose operand type the backend cannot spell is the
        // STRUCTURAL one — records, unions, options all compare via $equal
        emitNode st f lv a
        emitNode st f lv b
        callf f "$equal"
        (if op.StartsWith "<>@" then
            gcAbs f "ref.cast" "i31"
            i31get f
            ins f "i32.eqz"
            refI31 f)
    | EPrim ("=", [ a; b ]) when kindOfLite st a = "i" && kindOfLite st b = "i" ->
        emitNode st f lv a
        callf f "$toi"
        emitNode st f lv b
        callf f "$toi"
        ins f "i32.eq"
        refI31 f
    | EPrim ("<>", [ a; b ]) when kindOfLite st a = "i" && kindOfLite st b = "i" ->
        emitNode st f lv a
        callf f "$toi"
        emitNode st f lv b
        callf f "$toi"
        ins f "i32.ne"
        refI31 f
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
    | EPrim (("=t" | "<>t") as op, [ a; b ]) ->
        emitNode st f lv a
        gcT f "ref.cast" "$str"
        emitNode st f lv b
        gcT f "ref.cast" "$str"
        callf f "$streq"
        (if op = "<>t" then ins f "i32.eqz")
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
        && (op.EndsWith "f" || op.EndsWith "s" || op.EndsWith "l" || op.EndsWith "i"
            || op.EndsWith "p")
        && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "-"; "*"; "/"; "%"; "<"; ">"; "<="; ">="; "="; "<>" ] ->
        let baseOp = op.Substring (0, op.Length - 1)
        let kind = op.Substring (op.Length - 1)
        let un, box_, ty, flt =
            match kind with
            | "f" -> "$tof", "$off", "f64", true
            | "s" -> "$tos", "$oss", "f32", true
            | "l" -> "$tol", "$ofl", "i64", false
            | _ -> "$toi", "$ofi", "i32", false    // "i" and "p" share the rail
        if baseOp = "%" && flt then
            err st "binary: float remainder unsupported"
            refNull f "any"
        else
            emitNode st f lv a
            callf f un
            emitNode st f lv b
            callf f un
            let cmp = List.contains baseOp [ "<"; ">"; "<="; ">="; "="; "<>" ]
            let insn =
                match baseOp with
                | "+" -> ty + ".add" | "-" -> ty + ".sub" | "*" -> ty + ".mul"
                | "/" -> if flt then ty + ".div" else ty + ".div_s"
                | "%" -> ty + ".rem_s"
                | "=" -> ty + ".eq" | "<>" -> ty + ".ne"
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
        op.Length > 1 && op.EndsWith "v"
        && List.contains (op.Substring (0, op.Length - 1))
            [ "+"; "-"; "*"; "/"; "%"; "<"; ">"; "<="; ">="; "="; "<>"; "&&&"; "|||"; "^^^"; "<<<"; ">>>" ] ->
        // the UNSIGNED long family: uint64 semantics on the i64 rail. The
        // representation is int64's — same bits, same box — and only the
        // operations that READ the sign differ.
        let baseOp = op.Substring (0, op.Length - 1)
        emitNode st f lv a
        callf f "$tol"
        emitNode st f lv b
        (match baseOp with
         | "<<<" | ">>>" ->
             // the shift count is an int
             callf f "$toi"
             ins f "i64.extend_i32_u"
         | _ -> callf f "$tol")
        let cmp = List.contains baseOp [ "<"; ">"; "<="; ">="; "="; "<>" ]
        ins f (match baseOp with
               | "+" -> "i64.add" | "-" -> "i64.sub" | "*" -> "i64.mul"
               | "/" -> "i64.div_u" | "%" -> "i64.rem_u"
               | "=" -> "i64.eq" | "<>" -> "i64.ne"
               | "<" -> "i64.lt_u" | ">" -> "i64.gt_u"
               | "<=" -> "i64.le_u" | ">=" -> "i64.ge_u"
               | "&&&" -> "i64.and" | "|||" -> "i64.or" | "^^^" -> "i64.xor"
               | "<<<" -> "i64.shl" | _ -> "i64.shr_u")
        if cmp then refI31 f else callf f "$ofl"
    | EPrim (op, [ a; b ]) when
        op.Length > 1 && op.EndsWith "p"
        && List.contains (op.Substring (0, op.Length - 1))
            [ "+"; "-"; "*"; "/"; "%"; "<"; ">"; "<="; ">="; "="; "<>"; "&&&"; "|||"; "^^^"; "<<<"; ">>>" ] ->
        // nativeint bit ops: the i32 rail, like the ints they are here
        emitNode st f lv (EPrim (op.Substring (0, op.Length - 1), [ a; b ]))
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
        pushUnit f
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
    | EPrim ("u-p", [ a ]) -> emitNode st f lv (EPrim ("u-", [ a ]))
    | EPrim ("u~~~p", [ a ]) -> emitNode st f lv (EPrim ("u~~~", [ a ]))
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
    | ERecord (tyName, fields) when
          tyName.StartsWith "StructTuple"
          && not (dictTryFind st.FieldsOf tyName).IsSome
          && fields |> List.forall (fun (fn, _) -> fn.StartsWith "Item") ->
        // uniform-representation struct tuple: build the boxed tuple
        let ordered = fields |> List.sortBy (fun (fn, _) -> int (fn.Substring 4))
        for _, v in ordered do emitNode st f lv v
        gcT f "struct.new" ("$tup" + string (List.length ordered))
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
                      pushUnit f
                  | None ->
                      err st ("binary: missing field " + fname + " in " + rn + " (have " + String.concat "," (fields |> List.map fst) + ")")
                      refNull f "any")
             gcT f "struct.new" ("$r_" + rn)
         | None ->
             err st ("binary: record with unknown type " + tyName)
             refNull f "any")
    // a field of a POD element that was split into locals
    | EField _ when
          (match podElemRootOf st e with
           | Some (slots, path) -> slots |> List.exists (fun (p, _, _) -> p = path)
           | None -> false) ->
        let slots, fname = (podElemRootOf st e).Value
        let _, kd, l = slots |> List.find (fun (p, _, _) -> p = fname)
        lg f l
        callf f (boxOfK kd)
    | EField _ when
          (match podFieldChain e with
           | Some (nm, _, _, path) ->
               (dictTryFind st.Pod nm).IsSome
               && ((dictTryFind st.Pod nm).Value
                   |> fun (placed, _, _) -> placed |> List.exists (fun (p, _, _) -> p = path))
           | None -> false) ->
        let nm, a, i, fname = (podFieldChain e).Value
        // fusion: pts.[i].X reads that field straight out of the image — no
        // struct materialization, one box instead of the whole element
        let placed, _, wd = (dictTryFind st.Pod nm).Value
        let _, k, off = placed |> List.find (fun (p, _, _) -> p = fname)
        let hl = podHandleLocal st f lv a
        let bl = freshLocal f "$pfb" "i32"
        emitNode st f lv i
        callf f "$toi"
        ic f wd
        ins f "i32.mul"
        ls f bl
        emitPodLeafRead st f nm hl bl k off
    | EField (r, "Length", _) when not (dictTryFind st.FieldOwner "Length").IsSome ->
        // no record claims a Length field: this is the built-in one, across
        // strings and every array representation
        emitNode st f lv r
        callf f "$lenv"
    | EField (r, fname, owner) when
          owner.StartsWith "StructTuple" && fname.StartsWith "Item"
          && not (dictTryFind st.FieldIdx (owner, fname)).IsSome ->
        // a struct tuple at the UNIFORM representation (an unstamped
        // template, or a canonical all-reference instantiation): it is laid
        // out as the boxed tuple, so read it as one. Falling through to the
        // by-field-name owner guess picked WHATEVER record declares ItemN.
        let arity =
            let core = (if owner.Contains "$<" then owner.Substring (0, owner.IndexOf "$<") else owner).Substring 11
            (match parseDigits core with
             | Some v -> v
             | None -> 2)
        let idx = (int (fname.Substring 4)) - 1
        // an owner that names a SMALLER arity than the field demands is an
        // inconsistent template (uniform-representation dead code): cast to
        // the arity the READ needs, so the module validates and the path
        // traps at the cast if it is ever actually taken
        let arity = if idx >= arity then idx + 1 else arity
        emitNode st f lv r
        gcT f "ref.cast" ("$tup" + string arity)
        gcTF f "struct.get" ("$tup" + string arity) idx
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
             pushUnit f
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
        pushUnit f
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
        pushUnit f
    | EWhile (c, b) ->
        let hoisted = podHoistLoop st f [ c; b ]
        // Two bodies per test where the shape allows it. The remainder loop
        // after it runs at most once, so nothing is skipped and nothing is
        // reordered — the bodies execute in the same order, with the same
        // values, just with one less branch between every other pair.
        (match unrollGuard st c b with
         | Some guard ->
             blockE f "$wbrk2"
             loopE f "$wgo2"
             emitNode st f lv guard
             callf f "$toi"
             ins f "i32.eqz"
             brIf f "$wbrk2"
             emitNode st f lv b
             dropU f
             emitNode st f lv b
             dropU f
             br f "$wgo2"
             endB f
             endB f
         | None -> ())
        blockE f "$wbrk"
        loopE f "$wgo"
        emitNode st f lv c
        callf f "$toi"
        ins f "i32.eqz"
        brIf f "$wbrk"
        emitNode st f lv b
        dropU f
        br f "$wgo"
        endB f
        endB f
        for g in hoisted do dictRemove st.PodBase g
        pushUnit f
    | EApp (EUnknown "failwith", [ a ]) ->
        // the payload is Failure(msg), so `with Failure msg` matches it
        (match dictTryFind st.CaseTag "Failure" with
         | Some tg ->
             ic f tg
             emitNode st f lv a
             gcT f "struct.new" "$du1"
         | None -> emitNode st f lv a)
        throwExn f
        pushUnit f
    | EApp (EUnknown "raise", [ a ]) ->
        emitNode st f lv a
        throwExn f
        pushUnit f
    | EApp (EUnknown "ignore", [ a ]) ->
        emitNode st f lv a
        ins f "drop"
        pushUnit f
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
        pushUnit f
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
        let arrTy, _, _, _, _ = podRtOf st nm
        arrNewFixed f arrTy (List.length xs * wd)
        ic f 0
        ic f 0
        gcT f "struct.new" "$hnd"
    | EIndex (nm, a, i) when (dictTryFind st.Pod nm).IsSome ->
        let _, _, wd = (dictTryFind st.Pod nm).Value
        let hl = podHandleLocal st f lv a
        let bl = freshLocal f "$phb" "i32"
        emitNode st f lv i
        callf f "$toi"
        ic f wd
        ins f "i32.mul"
        ls f bl
        emitPodBuild st f nm hl bl nm ""
    // Storing a record LITERAL into a POD array: write the fields straight
    // into the image. The obvious lowering materializes a GC struct and then
    // reads it back apart, and that allocation is ruinous — not for its own
    // cost, but because a live POD array is large, so a million short-lived
    // structs make the collector trace it over and over. Filling a 1M-element
    // V3f[] took 3246ms that way and 210ms without the allocation.
    | EIndexSet (nm, a, i, ERecord (rn, fs)) when
          (dictTryFind st.Pod nm).IsSome
          && rn = nm ->
        let placed, _, wd = (dictTryFind st.Pod nm).Value
        let hl = podHandleLocal st f lv a
        let bl = freshLocal f "$shb" "i32"
        emitNode st f lv i
        callf f "$toi"
        ic f wd
        ins f "i32.mul"
        ls f bl
        // Each leaf once, in source order, into an UNBOXED local. Boxing them
        // would only trade one allocation per element for several: the whole
        // point is that nothing is allocated at all. A nested literal is
        // walked into its leaves — `{ Lo = { PX = ..` is the leaf "Lo.PX".
        let railOf (k : string) = match k with "f" -> "f64" | "s" -> "f32" | "l" -> "i64" | _ -> "i32"
        let slot = dictNew<string, string> ()
        let rec take (prefix : string) (fields : (string * Expr) list) : unit =
            for fn, fe in fields do
                let full = if prefix = "" then fn else prefix + "." + fn
                match fe with
                | ERecord (sub, subFs) when (dictTryFind st.StructFields sub).IsSome -> take full subFs
                | _ ->
                    match placed |> List.tryFind (fun (p, _, _) -> p = full) with
                    | Some (_, k, _) ->
                        let l = freshLocal f "$shf" (railOf k)
                        emitNode st f lv fe
                        callf f (podUnbox k)
                        ls f l
                        dictSet slot full l
                    | None -> ()
        take "" fs
        for w in 0 .. wd - 1 do
            emitPodWordStore st f nm hl bl w (fun () ->
                emitPodWordOf st f nm (fun path k ->
                    match dictTryFind slot path with
                    | Some l -> lg f l
                    | None ->
                        // a field the literal omits cannot happen for a
                        // record, but zero is the honest answer if it ever does
                        (match k with
                         | "f" -> fc f 0L
                         | "s" -> sc f 0
                         | "l" -> lc f 0L
                         | _ -> ic f 0)) w)
        pushUnit f
    | EIndexSet (nm, a, i, v) when (dictTryFind st.Pod nm).IsSome ->
        let _, _, wd = (dictTryFind st.Pod nm).Value
        let hl = podHandleLocal st f lv a
        let bl = freshLocal f "$phb" "i32"
        let vl = freshLocal f "$phv" "anyref"
        emitNode st f lv i
        callf f "$toi"
        ic f wd
        ins f "i32.mul"
        ls f bl
        emitNode st f lv v
        ls f vl
        for w in 0 .. wd - 1 do
            emitPodWordStore st f nm hl bl w (fun () -> emitPodWord st f nm vl w)
        pushUnit f
    | EArrayCreate (nm, n, EUnknown "$zero") when (dictTryFind st.Pod nm).IsSome ->
        let _, _, wd = (dictTryFind st.Pod nm).Value
        emitNode st f lv n
        callf f "$toi"
        ic f wd
        ins f "i32.mul"
        let arrTy2, _, _, _, _ = podRtOf st nm
        gcT f "array.new_default" arrTy2
        ic f 0
        ic f 0
        gcT f "struct.new" "$hnd"
    | EArrayCreate (nm, n, v) when (dictTryFind st.Pod nm).IsSome && podIsZeroInit v ->
        // zeroCreate of a POD struct arrives as a zero-RECORD init (struct
        // elements zero to instances — a null slot is a trap for CLASS
        // shapes), but a packed array has no instance slots at all:
        // array.new_default IS the zero fill. The seeding loop this
        // replaces called $hwset per WORD — 3M calls on the vertex
        // benchmark's zeroCreate, a quarter of its whole runtime.
        let _, _, wd = (dictTryFind st.Pod nm).Value
        emitNode st f lv n
        callf f "$toi"
        ic f wd
        ins f "i32.mul"
        let arrTy2, _, _, _, _ = podRtOf st nm
        gcT f "array.new_default" arrTy2
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
        let arrTy2, _, _, _, _ = podRtOf st nm
        gcT f "array.new_default" arrTy2
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
            callf f ("$hwset" + podSfxOf st nm)
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
        callf f ("$hlen" + podSfxOf st nm)
        ic f wd
        ins f "i32.div_u"
        callf f "$ofi"
    | EArrayPin (nm, a) ->
        (if (dictTryFind st.Pod nm).IsSome then
            emitNode st f lv a
            callf f ("$pinh" + podSfxOf st nm)
            callf f "$ofi"
         else
            err st "binary: Array.pin requires a POD struct array"
            refNull f "any")
    | EArrayUnpin (nm, a) ->
        (if (dictTryFind st.Pod nm).IsSome then
            emitNode st f lv a
            callf f ("$unpinh" + podSfxOf st nm)
            callf f "$ofi"
         else
            err st "binary: Array.unpin requires a POD struct array"
            refNull f "any")
    // the word count times the word width — the image's real size, which is
    // what a blit has to move and what no caller can work out for itself
    | EArrayBytes (nm, a) ->
        (if (dictTryFind st.Pod nm).IsSome then
            emitNode st f lv a
            callf f ("$hlen" + podSfxOf st nm)
            ic f (podW st nm)
            ins f "i32.mul"
            callf f "$ofi"
         else
            err st "binary: Array.byteSize requires a POD struct array"
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
        pushUnit f
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
        // NUMERIC kinds get their boxed zero; EVERYTHING else — a class, a
        // record, a DU, a type variable — is a reference and its zero is
        // NULL. (An i31 zero in a class-element array made `isNull` false
        // and the first field read a cast failure.)
        (match nm with
         | "float" | "float32" | "double" | "single" ->
             fc f 0L
             gcT f "struct.new" "$boxf"
         | "int" | "uint32" | "int64" | "uint64" | "int16" | "uint16"
         | "byte" | "sbyte" | "char" | "bool" ->
             pushUnit f
         | _ -> refNull f "any")
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
        pushUnit f
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
        pushUnit f
    | EArrayLen (("$str" | "byte" | "sbyte"), a) ->
        emitNode st f lv a
        gcT f "ref.cast" "$str"
        gci f "array.len"
        callf f "$ofi"
    | EArrayLen (nm, a) when parrK nm <> "" ->
        emitNode st f lv a
        gcT f "ref.cast" (parrTy (parrK nm))
        gci f "array.len"
        callf f "$ofi"
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
             ic f (tblIdx f.M name)
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
        // generic application: the applyc chain. NOT inlined: measured, the
        // inline form (struct.gets + call_indirect at every site) grew the
        // module 11% for ZERO time change — wasmtime's call to a tiny
        // function is already cheap, and the bigger code hurts the I-cache.
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
    | PCtor (name, _, _) when (dictTryFind st.EnumConst name).IsSome ->
        // an ENUM literal in pattern position: the value is its int
        lg f slot
        callf f "$toi"
        ic f (dictTryFind st.EnumConst name).Value
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
             // ONE sub-pattern reads the payload slot directly; several
             // read it as the tuple the multi-payload ctor packed
             (match args with
              | [ _ ] | [] ->
                  for sub in args do
                      let pl = freshLocal f "$bq" "anyref"
                      lg f slot
                      gcT f "ref.cast" "$du1"
                      gcTF f "struct.get" "$du1" 1
                      ls f pl
                      emitPat st f lv failLbl pl sub
              | several ->
                  let tn = "$tup" + string (List.length several)
                  let mutable i = 0
                  for sub in several do
                      let pl = freshLocal f "$bq" "anyref"
                      lg f slot
                      gcT f "ref.cast" "$du1"
                      gcTF f "struct.get" "$du1" 1
                      gcT f "ref.cast" tn
                      gcTF f "struct.get" tn i
                      ls f pl
                      emitPat st f lv failLbl pl sub
                      i <- i + 1)
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
        // a string pattern is a STRING compare: $streq (identity, length,
        // bytes) instead of the structural dispatch. Every `match name with
        // "i32.add" -> ...` in the emitter's own opcode tables lands here.
        lg f slot
        gcT f "ref.cast" "$str"
        let bytes = unescape raw
        let dn, _ = internStr st bytes
        gg f ("$sl:" + dn)
        callf f "$streq"
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
        // `:? T` in a pattern: same tests as ETypeTest, branch to fail.
        // An instantiated name tests its erased head — see ETypeTest.
        let tn = if tn.Contains "$<" then tn.Substring (0, tn.IndexOf "$<") else tn
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
        { SrcNames = dictNew (); M = f.M; B = scratchB; LocalIdx = dictNew (); LocalTys = vecNew ()
          NParams = f.NParams; Labels = labelsNew (); PatchAt = 0; Replay = -1
          PeepLast = None; PeepPrev = None; UnitAt = -1; UnitEnd = -1 }
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
        // the shadow-stack push goes here: after the locals, before the body
        if st.DbgFrame >= 0 then dbgFrame f 1 st.DbgFrame
        clearKinds ()
        f.Replay <- 0
        let lv1 = dictNew<string * int, string> ()
        for k, v in dictPairs lv do dictSet lv1 k v
        emitNode st f lv1 body
        true

/// the whole program: globals + per-decl init functions + _start
/// Emit, and report where each piece of code came from. `mapUrl` is written
/// into a `sourceMappingURL` custom section when non-empty — a debugger reads
/// it to find the map, and it changes the bytes, so it stays opt-in.
/// One LAYOUT, one NAME. A record instantiation is named by its arguments,
/// but every REFERENCE argument shares the uniform representation — so
/// `StructTuple2$<int.IAdaptiveObject>` and the canonical template's
/// `StructTuple2$<int.#34665>` are the same layout and must be the same
/// wasm type. Reference and symbolic arguments canonicalize to `obj`;
/// primitives and struct arguments (recursively canonicalized) keep their
/// names, because those DO change the layout.
let private canonRecordNames (decls : Decl list) : Decl list =
    let prims =
        [ "int"; "uint32"; "int64"; "uint64"; "int16"; "uint16"; "byte"; "sbyte"
          "char"; "bool"; "float"; "float32"; "float16"; "double"; "single"; "obj"; "$ref" ]
    let structBases = dictNew<string, bool> ()
    for d in decls do
        match d with
        | DRecord (n, _, _, true) ->
            let b = match n.IndexOf "$<" with | i when i > 0 -> n.Substring (0, i) | _ -> n
            dictSet structBases b true
        | _ -> ()
    let splitArgs (inner : string) : string list =
        let args = vecNew<string> ()
        let cur = vecNew<string> ()
        let mutable depth = 0
        for c in inner do
            if c = '<' then depth <- depth + 1; vecAdd cur (string c)
            elif c = '>' then depth <- depth - 1; vecAdd cur (string c)
            elif c = '.' && depth = 0 then
                vecAdd args (String.concat "" (vecToList cur))
                vecClear cur
            else vecAdd cur (string c)
        if vecLen cur > 0 then vecAdd args (String.concat "" (vecToList cur))
        vecToList args
    let rec canonName (n : string) : string =
        let i = n.IndexOf "$<"
        if i < 0 || not (n.EndsWith ">") then n
        else
            let b = n.Substring (0, i)
            let args = splitArgs (n.Substring (i + 2, n.Length - i - 3))
            b + "$<" + String.concat "." (args |> List.map canonArg) + ">"
    and canonArg (a : string) : string =
        if List.contains a prims then a
        elif a.StartsWith "#" then "obj"
        else
            let b = match a.IndexOf "$<" with | i when i > 0 -> a.Substring (0, i) | _ -> a
            if (dictTryFind structBases b).IsSome then canonName a else "obj"
    let cn (n : string) = if n.Contains "$<" then canonName n else n
    let rec cx (e : Expr) : Expr =
        match e with
        | ERecord (n, fs) -> ERecord (cn n, fs |> List.map (fun (k, v) -> k, cx v))
        | ERecordExt (n, b, fs) -> ERecordExt (cn n, cx b, fs |> List.map (fun (k, v) -> k, cx v))
        | EField (r, f2, o) -> EField (cx r, f2, cn o)
        | EFieldSet (r, f2, o, v) -> EFieldSet (cx r, f2, cn o, cx v)
        | ECast (t, x, d) -> ECast (cn t, cx x, d)
        | ETypeTest (t, x) -> ETypeTest (cn t, cx x)
        | ELam (ps, b) -> ELam (ps, cx b)
        | EApp (g, args) -> EApp (cx g, List.map cx args)
        | ELet (rc, v, s2, r, b) -> ELet (rc, v, s2, cx r, cx b)
        | EIf (a, b, c) -> EIf (cx a, cx b, cx c)
        | EMatch (sc, cs) -> EMatch (cx sc, cs |> List.map (fun (p2, g, b) -> p2, Option.map cx g, cx b))
        | ETry (b, cs) -> ETry (cx b, cs |> List.map (fun (p2, g, x) -> p2, Option.map cx g, cx x))
        | ETuple xs -> ETuple (List.map cx xs)
        | EListLit xs -> EListLit (List.map cx xs)
        | ESeq xs -> ESeq (List.map cx xs)
        | EPrim (op, xs) -> EPrim (op, List.map cx xs)
        | ECtor (n2, s2, xs) -> ECtor (n2, s2, List.map cx xs)
        | EWhile (c, b) -> EWhile (cx c, cx b)
        | EAssign (v, x) -> EAssign (v, cx x)
        | EArray (n2, xs) -> EArray (n2, List.map cx xs)
        | EIndex (n2, a, i2) -> EIndex (n2, cx a, cx i2)
        | EIndexSet (n2, a, i2, v) -> EIndexSet (n2, cx a, cx i2, cx v)
        | EArrayLen (n2, a) -> EArrayLen (n2, cx a)
        | EArrayCreate (n2, a, b) -> EArrayCreate (n2, cx a, cx b)
        | EArrayPin (n2, a) -> EArrayPin (n2, cx a)
        | EArrayUnpin (n2, a) -> EArrayUnpin (n2, cx a)
        | EArrayBytes (n2, a) -> EArrayBytes (n2, cx a)
        | EIfaceCall (i2, m2, r, args) -> EIfaceCall (i2, m2, cx r, List.map cx args)
        | other -> other
    let seenRec = dictNew<string, bool> ()
    decls
    |> List.choose (fun d ->
        match d with
        | DRecord (n, ps, fs, stf) ->
            let n2 = cn n
            if (dictTryFind seenRec n2).IsSome then None
            else
                dictSet seenRec n2 true
                // field TYPE names: canonicalize only STRUCT-based ones —
                // they name a layout; a reference-typed field is "r" either
                // way and its name is never cast against
                let cfs =
                    fs |> List.map (fun (f2, t) ->
                        let b = match t.IndexOf "$<" with | i when i > 0 -> t.Substring (0, i) | _ -> t
                        if (dictTryFind structBases b).IsSome then f2, cn t else f2, t)
                Some (DRecord (n2, ps, cfs, stf))
        | DLet (rc, v, sch, e) -> Some (DLet (rc, v, sch, cx e))
        // class declarations carry record NAMES too — the instantiation
        // subclass and its base; leaving them unnormalized broke the BaseOf
        // chain, so the subclass record inherited NO fields and its
        // constructor built a one-field husk
        | DClass (n, b, own, impls) -> Some (DClass (cn n, Option.map cn b, own, impls))
        | DMembers (n, own) -> Some (DMembers (cn n, own))
        | other -> Some other)

let emitBinaryWithPositions (mapUrl : string) (decls : Decl list)
        : byte[] * string list * string list * (int * string * int) list =
    let decls = canonRecordNames decls
    // a DEBUG build carries the shadow stack that makes a guest-visible
    // stack trace possible; a plain one pays nothing for it
    let debugBuild = mapUrl <> ""
    let m = modNew ()
    let st =
        { M = m; Errors = vecNew (); CaseTag = dictNew (); CaseArity = dictNew ()
          EnumConst = dictNew (); GlobalOf = dictNew (); FnOf = dictNew ()
          ArityOf = dictNew (); Warnings = vecNew ()
          Wrappers = dictNew ()
          CtorFns = dictNew (); LateFns = vecNew (); Externs = dictNew ()
          FieldsOf = dictNew (); FieldIdx = dictNew (); FieldOwner = dictNew (); DataN = 0
          LamName = refMapNew shallowExprHash
          LamFree = dictNew (); LamBody = vecNew (); CellVars = fst (cellScan decls)
          ObjRec = dictNew (); ClassName = dictNew (); DescIdOf = dictNew ()
          SlotOf = dictNew (); IfaceName = dictNew (); ImplsOf = dictNew ()
          SubsOf = dictNew (); BaseOf = dictNew ()
          TailApp = refMapNew shallowExprHash
          Pod = dictNew (); PodAlign = dictNew (); PodKind = dictNew (); PodBase = dictNew ()
          ConstGlobal = dictNew (); PinnedTypes = dictNew (); PodElem = dictNew ()
          // a debug build keeps the code shaped like its source
          Opt = not debugBuild
          StructFields = dictNew ()
          DbgFrame = -1
          LocalKind = dictNew (); InLambda = snd (cellScan decls)
          SigKinds = dictNew (); SigByName = dictNew (); CurRet = "u"
          StrSegs = dictNew (); RecFieldTy = dictNew ()
          EnumLikeUnion = dictNew () }
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
    // slot keys use the BARE interface name: an impl clause, a dispatch site
    // and the declaration spell the arity differently (`aval`,
    // `IAdaptiveValue<'T>`, IAdaptiveValue`1) and every spelling must land in
    // one slot
    let bareIface (n : string) =
        match n.IndexOf '`' with
        | i when i > 0 -> n.Substring (0, i)
        | _ -> n
    let vtableSlots =
        ((interfaceDecls |> List.collect (fun (i, ms) -> ms |> List.map (fun (mn, _) -> bareIface i, mn)))
         @ (classImpls |> List.collect (fun (_, impls) -> impls |> List.collect (fun (i, ms) -> ms |> List.map (fun (mn, _) -> bareIface i, mn)))))
        |> List.distinct
        |> List.sort
    let slotImpl (cn : string) (owner : string) (mn : string) : VarId option =
        let fromIface =
            chainOf cn
            |> List.tryPick (fun c ->
                classDecls
                |> List.tryPick (fun (n2, _, _, impls) ->
                    if n2 <> c then None
                    else impls |> List.tryPick (fun (i, ms) -> if bareIface i = owner then ms |> List.tryPick (fun (mm, v) -> if mm = mn then Some v else None) else None)))
        match fromIface with
        | Some v -> Some v
        | None ->
            if List.contains owner (chainOf cn) then
                chainOf cn
                |> List.tryPick (fun c ->
                    ownMembersOf c |> Option.bind (fun own -> own |> List.tryPick (fun (mm, v) -> if mm = mn then Some v else None)))
            else None
    // slots 0, 1 and 2 of every vtable are Equals, GetHashCode and Compare
    // (the last is NULL unless the type declares CompareTo — the runtime
    // $cmpv dispatches through it, which is what makes an Index inside a
    // generic comparer order by ITS OWN rule rather than structurally)
    let identitySlots = 3
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
    // C's widths, so that every numeric type is blittable: one byte for a
    // byte and for a bool (C's _Bool is one), two for a char (UTF-16) and a
    // half, four and eight for the rest.
    let fieldKind (ty : string) : string =
        match ty with
        | "float" -> "f"
        | "float32" -> "s"
        | "int64" | "uint64" -> "l"
        | "int" | "uint32" -> "i"
        | "char" | "float16" | "uint16" -> "h"
        | "int16" -> "m"
        | "byte" | "bool" -> "b"
        | "sbyte" -> "n"
        | t when List.contains t structNames -> "S:" + t
        | _ -> "r"
    let scalarSize (k : string) =
        match k with
        | "b" | "n" -> 1
        | "m" -> 2
        | "h" -> 2
        | "i" | "s" -> 4
        | _ -> 8
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
                        if k <> "r" && not (k.StartsWith "S:") then true
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
                        if k <> "r" && not (k.StartsWith "S:") then
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
                    // The backing word is the struct's ALIGNMENT. A size is
                    // always a multiple of its alignment, so an element is a
                    // whole number of words and the stride is exactly C's —
                    // for a three-byte colour as much as for a pair of
                    // doubles. It also means a field never straddles a word:
                    // its offset is a multiple of its own size, and the word
                    // is a multiple of that too.
                    dictSet st.PodAlign rn maxA
                    // homogeneous float struct: back it with a float array
                    let leafList = vecToList leaves
                    let allOf (k : string) = leafList |> List.forall (fun (_, lk, _) -> lk = k)
                    dictSet st.PodKind rn
                        (if maxA = 4 && allOf "s" then "s"
                         elif maxA = 8 && allOf "f" then "f"
                         else "")
                    dictSet st.Pod rn (vecToList leaves, sizeof_, sizeof_ / maxA)
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
        dictSet st.IfaceName (bareIface ifn) true
        let impls =
            classImpls
            |> List.filter (fun (_, impls) -> impls |> List.exists (fun (i, _) -> bareIface i = bareIface ifn))
            |> List.collect (fun (cn, _) -> subclassesOf cn)
            |> List.distinct
            |> List.filter isObjRecord
        dictSet st.ImplsOf ifn impls
        dictSet st.ImplsOf (bareIface ifn) impls
    // functions reachable through a vtable keep the canonical all-anyref
    // signature — that IS the dispatch contract, so no specialization
    let ifaceImplKeys =
        (classImpls |> List.collect (fun (_, impls) -> impls |> List.collect (fun (_, ms) -> ms |> List.map (fun (_, v) -> v.Path, v.Offset))))
        @ (classDecls
           |> List.collect (fun (cn, _, _, _) ->
                vtableSlots |> List.choose (fun (i, mn) -> slotImpl cn i mn |> Option.map (fun v -> v.Path, v.Offset))))
        @ (declaredMembers
           |> List.collect (fun (_, own) ->
                own |> List.choose (fun (mn, v) -> if mn = "Equals" || mn = "GetHashCode" || mn = "CompareTo" then Some (v.Path, v.Offset) else None)))
        @ (classDecls
           |> List.collect (fun (_, _, own, _) ->
                own |> List.choose (fun (mn, v) -> if mn = "Equals" || mn = "GetHashCode" || mn = "CompareTo" then Some (v.Path, v.Offset) else None)))
    let isIfaceImpl (key : string * int) = List.contains key ifaceImplKeys
    let scalarKindOfTy (t : Fpp.Analysis.Types.Type) : string =
        match Fpp.Analysis.Types.prune t with
        | Fpp.Analysis.Types.TCon ("float", []) -> "f"
        | Fpp.Analysis.Types.TCon ("float32", []) -> "s"
        | Fpp.Analysis.Types.TCon ("int64", []) -> "l"
        | Fpp.Analysis.Types.TCon ("uint64", []) -> "l"
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
            if cases |> List.forall (fun (_, ar) -> ar = 0) then
                dictSet st.EnumLikeUnion un true
            for cn, ar in cases do
                dictSet st.CaseTag cn tag
                dictSet st.CaseArity cn ar
                dictSet caseOwner cn un
                tag <- tag + 1
        | DEnum (_, cs) -> for c, v in cs do dictSet st.EnumConst c v
        | _ -> ()
    let tupArities = ([ 2; 3 ] @ scanTupleArities decls) |> List.distinct |> List.sort
    frame m vArities tupArities
    // the JS boundary imports — ONLY when the program touches Js.* (every
    // declared import must be satisfied at instantiation, so an unused set
    // would break plain wasmtime programs)
    let jsUsed =
        let mutable found = false
        let rec scanJs (e : Expr) : unit =
            (match e with
             | EApp (EUnknown n, _) when strLen n > 2 && n.StartsWith "js"
                                         && System.Char.IsUpper (charAt n 2) ->
                 found <- true
             | _ -> ())
            podScanChildren scanJs e
        for d in decls do
            match d with
            | DLet (_, _, _, e) -> scanJs e
            | _ -> ()
        found
    if jsUsed then jsImports m
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
        // what a debugger and a heap snapshot will call these fields
        nameFields m ("$r_" + rn) names
        for fn, ty in fields do
            if fn <> "__desc" && fn <> "__idhash" then dictSet st.RecFieldTy (rn, fn) ty
        names |> List.iteri (fun i fn ->
            dictSet st.FieldIdx (rn, fn) i
            // An INSTANTIATED subclass (`C$<int>`, one per element type, for
            // the vtable) redeclares its base's field names and nothing of
            // its own. Letting it claim ownership would point every
            // unqualified read of those fields at the instantiation, and
            // canonical code holding a plain C would fail the cast.
            if fn <> "__desc" && fn <> "__idhash" && not (rn.Contains "$<") then
                dictSet st.FieldOwner fn rn)
        if not stf && isObjRecord rn then
            // a FIELDLESS abstract base (all it declares is abstract members)
            // is lowered without a record of its own, so there is no $r_ type
            // to extend — such a class derives straight from $obj. Extending
            // a name that was never declared handed tyStructSub index -1.
            let super =
                match baseOf rn with
                | Some b when b <> rn && isObjRecord b -> "$r_" + b
                // a base-less CLASS roots at $objh (identity-hash slot);
                // plain records keep $obj
                | _ -> if isClassName rn then "$objh" else "$obj"
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
    rtTypesJs m
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
    rtDeclsJs m
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
    // A top-level binding is only constant if nothing ever assigns to it.
    let assignedVars = dictNew<string * int, bool> ()
    let rec scanAssign (e : Expr) : unit =
        (match e with
         | EAssign (v, _) -> dictSet assignedVars (v.Path, v.Offset) true
         | EArrayPin (nm, _) | EArrayUnpin (nm, _) | EArrayBytes (nm, _) ->
             dictSet st.PinnedTypes nm true
         | _ -> ())
        podScanChildren scanAssign e
    for d in decls do
        match d with
        | DLet (_, _, _, body) -> scanAssign body
        | _ -> ()
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
        | DLet (isRec, v, _, rhs) ->
            let g = mangle v
            dictSet st.GlobalOf (v.Path, v.Offset) g
            globalAnyref m g
            (match rhs with
             | ELit _ when not isRec && not (dictTryFind assignedVars (v.Path, v.Offset)).IsSome ->
                 dictSet st.ConstGlobal (v.Path, v.Offset) rhs
             | _ -> ())
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
                [ "Equals", "$eq_" + cn, 2; "GetHashCode", "$hash_" + cn, 1
                  "CompareTo", "", 2 ]
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
    // Cell-ness is PER DECLARATION: the tables are keyed by (path, offset),
    // and alpha-renamed stamp clones can COLLIDE across declarations — one
    // clone's captured mutable marked another clone's plain parameter as a
    // cell, so the build stored raw and the read dereferenced. Each body is
    // emitted under its OWN declaration's scan; a lambda under its OWNER's.
    let perDeclCells =
        decls |> List.map (fun d ->
            match d with
            | DLet (_, _, _, _) -> cellScan [ d ]
            | _ -> (dictNew (), dictNew ()))
    let setCellCtx (di : int) : unit =
        let (cells, inl) = List.item di perDeclCells
        st.CellVars <- cells
        st.InLambda <- inl
    let lamOwner = dictNew<string, int> ()
    decls |> List.iteri (fun di d ->
        match d with
        | DLet (_, _, _, body) ->
            let before = vecLen st.LamBody
            discoverLams st (dictNew ()) body
            let mutable j = before
            while j < vecLen st.LamBody do
                let (nm, _, _) = vecGet st.LamBody j
                dictSet lamOwner nm di
                j <- j + 1
        | _ -> ())
    for name, _, _ in vecToList st.LamBody do
        declFn m name "$u1"
        tblIdx m name |> ignore
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
    declFn m "$strinit" "$init_t"
    exportFn m "_start" "$_start"
    exportFn m "jscall" "$jscall"
    // `[<Export>]`: one wrapper per exported function, with a REAL scalar
    // signature so the host passes numbers rather than reference values.
    // The wrapper boxes on the way in and unboxes on the way out, which is
    // the same crossing an extern makes in the other direction.
    let exports =
        decls |> List.choose (fun d ->
            match d with
            | DExport (v, n) ->
                (match dictTryFind st.FnOf (v.Path, v.Offset), dictTryFind st.ArityOf (v.Path, v.Offset) with
                 | Some fn, Some 1 ->
                     // the callee may already ride a scalar rail, in which
                     // case it takes and returns i32 and the wrapper is a
                     // pure forward — box only where the rail is uniform
                     let pk, rk =
                         match dictTryFind st.SigKinds (v.Path, v.Offset) with
                         | Some (pks, r) -> (match pks with [ k ] -> k | _ -> "a"), r
                         | None -> "a", "a"
                     Some (v, n, fn, pk, rk)
                 | _ ->
                     err st ("binary: [<Export>] " + n + " must be a function of one int argument")
                     None)
            | _ -> None)
    if not (List.isEmpty exports) then tyFunc m "$exp_i2i" [ "i32" ] [ "i32" ]
    for _, n, _, _, _ in exports do
        declFn m ("$export$" + n) "$exp_i2i"
        exportFn m n ("$export$" + n)
    // bodies, in declaration order
    rtCore m
    rtCore2 m
    let duEqDirect = duEqSlots |> List.forall (fun x -> x = "$eq_du_default")
    let duHashDirect = duHashSlots |> List.forall (fun x -> x = "$hash_du_default")
    rtCore3 m tupArities duEqDirect
    rtCore4 m
    rtCore5 m
    rtCore6 m
    rtCore7 m tupArities duHashDirect
    rtCore8 m
    rtCore9 m
    rtCore10 m
    rtCore11 m
    rtCore12 m
    rtCore13 m
    rtCoreJs m
    // ---- the shadow stack (debug builds) ---------------------------------
    // wasm gives the guest no way to look at its own call stack, so a debug
    // build keeps one: a depth counter and a ring of frame ids, maintained at
    // entry, at exit, and BEFORE a tail call — where the frame is replaced
    // rather than pushed.
    if debugBuild then
        globalI32Mut m "$dbgDepth" 0
        globalArrI32 m "$dbgFrames" 512
    // bodies in DECLARATION order: all functions first, then all inits —
    // interleaving them put code into the wrong slots
    decls |> List.iteri (fun declIdx d ->
        match d with
        | DLet (_, v, _, ELam (ps, body)) ->
            setCellCtx declIdx
            // parameters keep the names they were WRITTEN with, so a debugger's
            // scope view reads `p` rather than `a0`. Uniquified by position,
            // since two parameters may share a spelling after inlining.
            let names =
                let raw =
                    ps
                    |> List.mapi (fun i (pv : VarId, _) ->
                        if pv.Name = "" || pv.Name = "_" then "a" + string i else pv.Name)
                // a suffix only where two parameters really do share a name
                // a suffix only where two parameters really do share a name
                raw
                |> List.mapi (fun i n ->
                    if (raw |> List.filter (fun x -> x = n) |> List.length) > 1 then "$" + n + string i
                    else "$" + n)
            let f = beginFn m names
            // this function's code starts here, and it came from there
            markSrc f v.Path v.Offset
            // the frame id is this function's index, which the name section
            // already maps to a name
            st.DbgFrame <- (if debugBuild then m.ImportedFuncs + m.CodeCount else -1)
            let lv = dictNew<string * int, string> ()
            List.iteri (fun i (pv : VarId, _) -> dictSet lv (pv.Path, pv.Offset) (List.item i names)) ps
            let pks, rk =
                match dictTryFind st.SigKinds (v.Path, v.Offset) with
                | Some (p, r) -> p, r
                | None -> (ps |> List.map (fun _ -> "u")), "u"
            // a capped stamp's scheme can disagree with the lambda's own
            // parameter list. Its CALLERS read SigKinds, so the header must
            // keep them agreeing with itself is impossible — the whole
            // function becomes an unreachable STUB instead: it only exists
            // because a poisoned vtable materialized it, and no real path
            // calls it.
            let poisoned = List.length pks <> List.length ps
            let pks = if poisoned then ps |> List.map (fun _ -> "u") else pks
            let body = if poisoned then EUnknown "poisoned stamp" else body
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
            let emitted = emitWithLocalsK st f lv (mangle v) body paramKinds
            st.DbgFrame <- -1
            if rk <> "u" then callf f (unboxOfK rk)
            // and the pop, on the way out
            if debugBuild && emitted then dbgFrame f -1 -1
            st.CurRet <- "u"
            endFn f
        | _ -> ())
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
                pushUnit f
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
        pushUnit f
        callf f target
        endFn f
    // lambda bodies: param + env; captured keys read from the env array.
    // The capture FILTER at each build site is "is it a local there", so the
    // body maps every free key optimistically; unreached slots never read.
    for name, (pv, _), body in vecToList st.LamBody do
        (match dictTryFind lamOwner name with
         | Some di -> setCellCtx di
         | None -> ())
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
    decls |> List.iteri (fun declIdx d ->
        match d with
        | DLet (_, _, _, ELam _) -> ()
        | DLet (_, v, _, rhs) ->
            setCellCtx declIdx
            let f = beginFn m []
            let lv = dictNew<string * int, string> ()
            if emitWithLocals st f lv (mangle v) rhs true then
                gs f (dictTryFind st.GlobalOf (v.Path, v.Offset)).Value
            endFn f
        | _ -> ())
    let f = beginFn m []
    localsDone f
    callf f "$strinit"
    for i in vecToList inits do callf f i
    endFn f
    // $strinit: build every hoisted literal, in intern order
    let f = beginFn m []
    localsDone f
    for _, (dn, len) in dictPairs st.StrSegs do
        ic f 0
        ic f len
        arrNewData f "$str" dn
        gs f ("$sl:" + dn)
    endFn f
    // export wrappers: declared right after $strinit, so their bodies land
    // here — before the lazily requested curried wrappers, exactly as the
    // function section orders them
    for _, _, fn, pk, rk in exports do
        let f = beginFn m [ "$p" ]
        localsDone f
        lg f "$p"
        if pk <> "i" then callf f "$ofi"
        callf f fn
        if rk <> "i" then callf f "$toi"
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
                ic f (tblIdx f.M (fname + ".w" + string (k + 1)))
                lg f "$a"
                lg f "$env"
                gcT f "struct.new" "$cons"
                gcT f "struct.new" "$clo"
            endFn f
    let bytes = assembleWith m 17 true mapUrl
    // positions were recorded relative to the code payload; shift them to
    // absolute offsets in the file now that assembly has placed it
    let positions =
        vecToList m.SrcPos |> List.map (fun (off, path, srcOff) -> lastCodeStart + off, path, srcOff)
    bytes, vecToList st.Errors, vecToList st.Warnings, positions

/// the plain module: no positions, no source map
let emitBinary (decls : Decl list) : byte[] * string list * string list =
    let bytes, errs, warns, _ = emitBinaryWithPositions "" decls
    bytes, errs, warns
