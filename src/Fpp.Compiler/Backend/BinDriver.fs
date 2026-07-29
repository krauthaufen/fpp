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
      mutable DataN : int }

let private err (st : St) (msg : string) : unit = vecAdd st.Errors msg

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
    | ESeq xs | ETuple xs | EListLit xs | EPrim (_, xs) | ECtor (_, _, xs) ->
        for x in xs do discoverLams st outer x
    | ERecord (_, fs) -> for _, v in fs do discoverLams st outer v
    | EField (r, _, _) -> discoverLams st outer r
    | EFieldSet (r, _, _, v) -> discoverLams st outer r; discoverLams st outer v
    | EWhile (c, b) -> discoverLams st outer c; discoverLams st outer b
    | EAssign (_, x) -> discoverLams st outer x
    | EIfaceCall (_, _, r, args) -> discoverLams st outer r; for a in args do discoverLams st outer a
    | ECast (_, x, _) | ETypeTest (_, x) -> discoverLams st outer x
    | ETry (b, cs) ->
        discoverLams st outer b
        for _, g, x in cs do
            (match g with Some gg -> discoverLams st outer gg | None -> ())
            discoverLams st outer x
    | _ -> ()

let rec private emitNode (st : St) (f : Fn) (lv : Dict<string * int, string>) (e : Expr) : unit =
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
                 emitNode st f lv x
                 ins f "drop"
             emitNode st f lv last)
    | EVarI (v, sch, _) -> emitNode st f lv (EVar (v, sch))
    | EVar (v, _) ->
        (match dictTryFind lv (v.Path, v.Offset) with
         | Some l when l.StartsWith "@env:" ->
             lg f "$env"
             gcT f "ref.cast" "$arr"
             ic f (int (l.Substring 5))
             gcT f "array.get" "$arr"
         | Some l -> lg f l
         | None ->
         match dictTryFind st.GlobalOf (v.Path, v.Offset) with
         | Some g -> gg f g
         | None ->
             err st ("binary: unbound variable " + v.Name)
             refNull f "any")
    | ELet (_, _, _, _, _) ->
        // the let spine, iteratively, exactly like the text emitter
        let mutable cur = e
        let mutable walking = true
        while walking do
            match cur with
            | ELet (_, v, _, rhs, body) ->
                emitNode st f lv rhs
                let l = freshLocal f "$bl" "anyref"
                dictSet lv (v.Path, v.Offset) l
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
    | EApp (EUnknown "prints", [ a ]) ->
        emitNode st f lv a
        gcT f "ref.cast" "$str"
        callf f "$prints"
        ic f 0
        refI31 f
    | EPrim ("+", [ a; b ]) ->
        emitNode st f lv a
        emitNode st f lv b
        callf f "$addv"
    | EPrim ("=", [ a; b ]) ->
        emitNode st f lv a
        emitNode st f lv b
        callf f "$equal"
    | EPrim (op, [ a; b ]) when List.contains op [ "-"; "*"; "/" ] ->
        let insn = match op with "-" -> "i32.sub" | "*" -> "i32.mul" | _ -> "i32.div_s"
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
                  | None ->
                      err st ("binary: missing field " + fname + " in " + rn)
                      refNull f "any")
             gcT f "struct.new" ("$r_" + rn)
         | None ->
             err st ("binary: record with unknown type " + tyName)
             refNull f "any")
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
        for a in args do emitNode st f lv a
        callf f (dictTryFind st.FnOf (v.Path, v.Offset)).Value
    | EAssign (v, rhs) ->
        (match dictTryFind lv (v.Path, v.Offset) with
         | Some l when not (l.StartsWith "@env:") ->
             emitNode st f lv rhs
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
    | EArray (_, xs) ->
        for x in xs do emitNode st f lv x
        arrNewFixed f "$arr" (List.length xs)
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
        emitNode st f lv a
        gcT f "ref.cast" "$arr"
        gci f "array.len"
        callf f "$ofi"
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
                          err st "binary: capture not in scope at build site"
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
        let l = freshLocal f "$bp" "anyref"
        dictSet lv (v.Path, v.Offset) l
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
             (match args with
              | [] -> ()
              | [ sub ] ->
                  let pl = freshLocal f "$bq" "anyref"
                  lg f slot
                  gcT f "ref.cast" "$du1"
                  gcTF f "struct.get" "$du1" 1
                  ls f pl
                  emitPat st f lv failLbl pl sub
              | _ -> err st "binary: multi-arg ctor pattern not ported")
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
    | _ -> err st "binary: pattern case not ported yet"

/// Emit a body whose locals are only discovered DURING emission: run the
/// emission once into a scratch buffer (locals allocate in a deterministic
/// order), then declare exactly those locals and splice the bytes. Local
/// indices agree because both passes allocate in the same order.
and private emitWithLocals (st : St) (f : Fn) (lv : Dict<string * int, string>)
                           (owner : string) (body : Expr) (needsResult : bool) : bool =
    let scratchB = bytesNew ()
    let scratch =
        { M = f.M; B = scratchB; LocalIdx = dictNew (); LocalTys = vecNew ()
          NParams = f.NParams; Labels = labelsNew (); PatchAt = 0; Replay = -1 }
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
        f.Replay <- 0
        let lv1 = dictNew<string * int, string> ()
        for k, v in dictPairs lv do dictSet lv1 k v
        emitNode st f lv1 body
        ignore needsResult
        true

/// the whole program: globals + per-decl init functions + _start
let emitBinary (decls : Decl list) : byte[] * string list * string list =
    let m = modNew ()
    let st =
        { M = m; Errors = vecNew (); CaseTag = dictNew (); CaseArity = dictNew ()
          EnumConst = dictNew (); GlobalOf = dictNew (); FnOf = dictNew ()
          ArityOf = dictNew (); Warnings = vecNew ()
          FieldsOf = dictNew (); FieldIdx = dictNew (); FieldOwner = dictNew (); DataN = 0
          LamName = refMapNew (fun (_ : Expr) -> 7)
          LamFree = dictNew (); LamBody = vecNew () }
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
    // record types: UNIFORM anyref fields (scalarization is a parity task,
    // not a bring-up task); names as declared, stamped clones included
    for d in decls do
        match d with
        | DRecord (rn, _, fs, _) ->
            let names = fs |> List.map fst
            dictSet st.FieldsOf rn names
            names |> List.iteri (fun i fn ->
                dictSet st.FieldIdx (rn, fn) i
                dictSet st.FieldOwner fn rn)
            tyStruct m ("$r_" + rn) (names |> List.map (fun _ -> fld true "anyref"))
        | _ -> ()
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
        | DLet (_, v, _, ELam (ps, _)) ->
            let fn = mangle v
            dictSet st.FnOf (v.Path, v.Offset) fn
            dictSet st.ArityOf (v.Path, v.Offset) (List.length ps)
            declFn m fn ("$v" + string (List.length ps))
        | DLet (_, v, _, _) ->
            let g = mangle v
            dictSet st.GlobalOf (v.Path, v.Offset) g
            globalAnyref m g
        | _ -> ()
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
    rtCore3 m [ 2; 3 ]
    rtCore4 m
    // bodies in DECLARATION order: all functions first, then all inits —
    // interleaving them put code into the wrong slots
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, body)) ->
            let names = ps |> List.mapi (fun i _ -> "$a" + string i)
            let f = beginFn m names
            let lv = dictNew<string * int, string> ()
            List.iteri (fun i (pv : VarId, _) -> dictSet lv (pv.Path, pv.Offset) ("$a" + string i)) ps
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
            emitWithLocals st f lv (mangle v) body true |> ignore
            endFn f
        | _ -> ()
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
    assemble m 17 true, vecToList st.Errors, vecToList st.Warnings
