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
      mutable DataN : int }

let private err (st : St) (msg : string) : unit = vecAdd st.Errors msg

let private mangle (v : VarId) : string =
    "$b" + string (abs (strHash v.Path % 1000)) + "_" + string v.Offset + "_"
    + (v.Name |> String.map (fun c -> if isLetterOrDigit c then c else '_'))

/// intern a string literal as a data segment, return its name and length
let private internStr (st : St) (bytes : byte[]) : string * int =
    let name = "$bd" + string st.DataN
    st.DataN <- st.DataN + 1
    dataSeg st.M name bytes
    name, bytes.Length

// unescape for string literals — decimal/hex/named escapes, same rules as
// the text emitter's (shared logic would be better placed in Prelude later)
let private unescape (raw : string) : byte[] =
    let inner =
        if strLen raw >= 6 && charAt raw 0 = '"' && charAt raw 1 = '"' then substr raw 3 (strLen raw - 6)
        elif strLen raw >= 3 && charAt raw 0 = '@' then substr raw 2 (strLen raw - 3)
        elif strLen raw >= 2 then substr raw 1 (strLen raw - 2)
        else raw
    let out = vecNew<byte> ()
    let mutable i = 0
    while i < strLen inner do
        let c = charAt inner i
        if c = '\\' && i + 1 < strLen inner then
            let n = charAt inner (i + 1)
            let code, w =
                match n with
                | 'n' -> 10, 2 | 't' -> 9, 2 | 'r' -> 13, 2
                | '\\' -> 92, 2 | '"' -> 34, 2 | '\'' -> 39, 2
                | d when d >= '0' && d <= '9' && i + 3 < strLen inner
                         && isDigit (charAt inner (i + 2)) && isDigit (charAt inner (i + 3)) ->
                    ((int d - 48) * 100 + (int (charAt inner (i + 2)) - 48) * 10
                     + (int (charAt inner (i + 3)) - 48)) % 256, 4
                | o -> int o, 2
            vecAdd out (byte code)
            i <- i + w
        else
            vecAdd out (byte c)
            i <- i + 1
    vecToArray out

let rec private emitNode (st : St) (f : Fn) (e : Expr) : unit =
    match e with
    | ELit (LInt s) when not (s.EndsWith "L") ->
        let digits = s |> String.filter (fun c -> isDigit c || c = '-')
        ic f (if digits = "" then 0 else int digits)
        callf f "$ofi"
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
                 emitNode st f x
                 ins f "drop"
             emitNode st f last)
    | EVar (v, _) ->
        (match dictTryFind st.GlobalOf (v.Path, v.Offset) with
         | Some g -> gg f g
         | None ->
             err st ("binary: unbound variable " + v.Name)
             refNull f "any")
    | ECtor (name, _, args) ->
        (match dictTryFind st.CaseArity name with
         | Some 0 -> gg f ("$c_" + name)
         | Some _ when not (List.isEmpty args) ->
             ic f (dictTryFind st.CaseTag name).Value
             (match args with
              | [ one ] -> emitNode st f one
              | many ->
                  err st "binary: multi-payload ctor not ported"
                  refNull f "any")
             gcT f "struct.new" "$du1"
         | _ ->
             err st ("binary: ctor shape not ported: " + name)
             refNull f "any")
    | EApp (EUnknown "print", [ a ]) ->
        emitNode st f a
        callf f "$printval"
        ic f 10
        callf f "$putc"
        ic f 0
        refI31 f
    | EApp (EUnknown "prints", [ a ]) ->
        emitNode st f a
        gcT f "ref.cast" "$str"
        callf f "$prints"
        ic f 0
        refI31 f
    | EPrim ("+", [ a; b ]) ->
        emitNode st f a
        emitNode st f b
        callf f "$addv"
    | EPrim ("=", [ a; b ]) ->
        emitNode st f a
        emitNode st f b
        callf f "$equal"
    | EPrim (op, [ a; b ]) when List.contains op [ "-"; "*"; "/" ] ->
        let insn = match op with "-" -> "i32.sub" | "*" -> "i32.mul" | _ -> "i32.div_s"
        emitNode st f a
        callf f "$toi"
        emitNode st f b
        callf f "$toi"
        ins f insn
        callf f "$ofi"
    | other ->
        err st ("binary: expression case not ported yet")
        refNull f "any"

/// the whole program: globals + per-decl init functions + _start
let emitBinary (decls : Decl list) : byte[] * string list =
    let m = modNew ()
    let st =
        { M = m; Errors = vecNew (); CaseTag = dictNew (); CaseArity = dictNew ()
          EnumConst = dictNew (); GlobalOf = dictNew (); FnOf = dictNew ()
          ArityOf = dictNew (); DataN = 0 }
    // tags in declaration order, like the text prepass
    let mutable tag = 0
    for d in decls do
        match d with
        | DUnion (_, _, cases) ->
            for cn, ar in cases do
                dictSet st.CaseTag cn tag
                dictSet st.CaseArity cn ar
                tag <- tag + 1
        | _ -> ()
    frame m [ 1; 2; 3 ] [ 2; 3 ]
    rtTypes2 m
    rtTypes3 m
    rtTypes4 m
    tyFunc m "$init_t" [] []
    rtDecls m
    rtCoreDecls2 m
    rtDecls3 m
    rtDecls4 m
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
    globalVt m "$duEq" (List.init (max tag 1) (fun _ -> "$eq_du_default"))
    // program globals + init function declarations
    let inits = vecNew<string> ()
    for d in decls do
        match d with
        | DLet (_, v, _, ELam _) -> ()  // functions: next milestone
        | DLet (_, v, _, _) ->
            let g = mangle v
            dictSet st.GlobalOf (v.Path, v.Offset) g
            globalAnyref m g
        | _ -> ()
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
    rtCore3 m [ 2; 3 ]
    rtCore4 m
    for d in decls do
        match d with
        | DLet (_, _, _, ELam _) -> ()
        | DLet (_, v, _, rhs) ->
            let f = beginFn m []
            localsDone f
            emitNode st f rhs
            gs f (dictTryFind st.GlobalOf (v.Path, v.Offset)).Value
            endFn f
        | _ -> ()
    let f = beginFn m []
    localsDone f
    for i in vecToList inits do callf f i
    endFn f
    assemble m 17 true, vecToList st.Errors
