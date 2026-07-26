module Fpp.Backend.EmitWasm

open Fpp.Prelude
open Fpp.Core.Ir

// Core -> wasm-GC (WAT text), v0: the uniform representation from
// REPRESENTATION.md. Everything is anyref; ints/bools/chars/unit ride i31,
// floats box, strings are i8 arrays, records/DU cases are GC structs,
// lists are $cons/null, closures are { code; env-chain }. Known full-arity
// calls go direct; everything else curries through unary closures.
// Specialization (tier 1) arrives with the linker; native backends reuse
// the same lowering decisions with different encodings.

type EmitResult =
    { Wat : string
      Errors : string list }

let emit (decls : Decl list) : EmitResult =
    let errors = vecNew<string> ()
    let sb = System.Text.StringBuilder()
    let line (s : string) = sb.AppendLine s |> ignore

    // ---- program shape ----------------------------------------------------

    let unions = decls |> List.choose (fun d -> match d with DUnion (n, _, cs) -> Some (n, cs) | _ -> None)
    let records = decls |> List.choose (fun d -> match d with DRecord (n, _, fs, st) -> Some (n, fs, st) | _ -> None)

    // struct records store fields UNBOXED by kind; plain records stay anyref
    let kindOfField (isStruct : bool) (k : string) = if isStruct then k else "r"
    // flat-array element classification: primitive kind or a struct name
    let primKindOf (tyName : string) : string =
        match tyName with
        | "int" | "bool" | "char" -> "i"
        | "float" -> "f"
        | "float32" -> "s"
        | "int64" -> "l"
        | _ -> ""
    let structRecords = decls |> List.choose (fun d -> match d with DRecord (n, _, fs, true) -> Some (n, fs) | _ -> None)
    let isStructName (n : string) = structRecords |> List.exists (fun (rn, _) -> rn = n)
    let parrOf (k : string) = "$parr_" + k
    // ---- C ABI layout for POD structs (clang natural alignment) ----------
    // fields: (name, kind, byteOffset); sizeof rounded to max align;
    // storage = shared GC (array (mut i64)), strideWords per element
    let podLayout = dictNew<string, (string * string * int) list * int * int> ()
    for rn, fs in structRecords do
        if fs |> List.forall (fun (_, k) -> k = "i" || k = "f" || k = "s" || k = "l") then
            let mutable off = 0
            let mutable maxA = 1
            let placed =
                fs |> List.map (fun (fn, k) ->
                    let sz = if k = "i" || k = "s" then 4 else 8
                    off <- ((off + sz - 1) / sz) * sz
                    let o = off
                    off <- off + sz
                    if sz > maxA then maxA <- sz
                    fn, k, o)
            let sizeof_ = ((off + maxA - 1) / maxA) * maxA
            dictSet podLayout rn (placed, sizeof_, (sizeof_ + 7) / 8)
    let isPod (n : string) = (dictTryFind podLayout n).IsSome
    /// word read/write through a handle: GC storage or linear when pinned
    let hWordGet (hExpr : string) (idxExpr : string) : string =
        "(if (result i64) (ref.is_null (struct.get $hnd 0 (ref.cast (ref $hnd) " + hExpr + ")))"
        + " (then (i64.load (i32.add (struct.get $hnd 1 (ref.cast (ref $hnd) " + hExpr + ")) (i32.mul " + idxExpr + " (i32.const 8)))))"
        + " (else (array.get $pk (ref.as_non_null (struct.get $hnd 0 (ref.cast (ref $hnd) " + hExpr + "))) " + idxExpr + ")))"
    let hWordSet (hExpr : string) (idxExpr : string) (valExpr : string) : string =
        "(if (ref.is_null (struct.get $hnd 0 (ref.cast (ref $hnd) " + hExpr + ")))"
        + " (then (i64.store (i32.add (struct.get $hnd 1 (ref.cast (ref $hnd) " + hExpr + ")) (i32.mul " + idxExpr + " (i32.const 8))) " + valExpr + "))"
        + " (else (array.set $pk (ref.as_non_null (struct.get $hnd 0 (ref.cast (ref $hnd) " + hExpr + "))) " + idxExpr + " " + valExpr + ")))"
    let hLen (hExpr : string) : string =
        "(if (result i32) (ref.is_null (struct.get $hnd 0 (ref.cast (ref $hnd) " + hExpr + ")))"
        + " (then (struct.get $hnd 2 (ref.cast (ref $hnd) " + hExpr + ")))"
        + " (else (array.len (ref.as_non_null (struct.get $hnd 0 (ref.cast (ref $hnd) " + hExpr + "))))))"

    /// raw field value FROM a word expression (kind-typed result)
    let fieldFromWords (rn : string) (arrW : string) (baseW : string) (fn : string) : string =
        let placed, _, _ = (dictTryFind podLayout rn).Value
        let _, k, off = placed |> List.find (fun (n, _, _) -> n = fn)
        let word = hWordGet arrW ("(i32.add " + baseW + " (i32.const " + string (off / 8) + "))")
        let sh = (off % 8) * 8
        match k with
        | "f" -> "(f64.reinterpret_i64 " + word + ")"
        | "l" -> word
        | "s" ->
            let bits = if sh = 0 then "(i32.wrap_i64 " + word + ")" else "(i32.wrap_i64 (i64.shr_u " + word + " (i64.const " + string sh + ")))"
            "(f32.reinterpret_i32 " + bits + ")"
        | _ ->
            if sh = 0 then "(i32.wrap_i64 " + word + ")"
            else "(i32.wrap_i64 (i64.shr_u " + word + " (i64.const " + string sh + ")))"
    /// i64 word w built from a struct value in local `vl`
    let wordFromStruct (rn : string) (vl : string) (w : int) : string =
        let placed, _, _ = (dictTryFind podLayout rn).Value
        let fidx = structRecords |> List.pick (fun (n, fs) -> if n = rn then Some (fs |> List.mapi (fun i (fn, _) -> fn, i)) else None)
        let parts =
            placed
            |> List.filter (fun (_, _, off) -> off / 8 = w)
            |> List.map (fun (fn, k, off) ->
                let i = fidx |> List.find (fun (n, _) -> n = fn) |> snd
                let fv = "(struct.get $r_" + rn + " " + string i + " (ref.cast (ref $r_" + rn + ") (local.get " + vl + ")))"
                let sh = (off % 8) * 8
                match k with
                | "f" -> "(i64.reinterpret_f64 " + fv + ")"
                | "l" -> fv
                | "s" ->
                    let b = "(i64.extend_i32_u (i32.reinterpret_f32 " + fv + "))"
                    if sh = 0 then b else "(i64.shl " + b + " (i64.const " + string sh + "))"
                | _ ->
                    let b = "(i64.and (i64.extend_i32_u " + fv + ") (i64.const 4294967295))"
                    if sh = 0 then b else "(i64.shl " + b + " (i64.const " + string sh + "))")
        match parts with
        | [] -> "(i64.const 0)"
        | [ one ] -> one
        | many -> many |> List.reduce (fun a b -> "(i64.or " + a + " " + b + ")")
    let boxOfKind (k : string) = match k with "f" -> "$off" | "s" -> "$oss" | "l" -> "$ofl" | _ -> "$ofi"
    let unboxOfKind (k : string) = match k with "f" -> "$tof" | "s" -> "$tos" | "l" -> "$tol" | _ -> "$toi"
    // field name -> (record, index, kind); F# shadowing: last declaration wins
    let fieldIndex = dictNew<string, string * int * string> ()
    for rn, fs, st in records do
        fs |> List.iteri (fun i (f, k) -> dictSet fieldIndex f (rn, i, kindOfField st k))
    let recordOrder = dictNew<string, (string * string) list> ()
    for rn, fs, st in records do
        dictSet recordOrder rn (fs |> List.map (fun (f, k) -> f, kindOfField st k))

    let caseArity = dictNew<string, int> ()
    let caseOwner = dictNew<string, string> ()
    let caseTag = dictNew<string, int> ()
    let mutable nextTag = 0
    for un, cs in unions do
        for cn, a in cs do
            dictSet caseArity cn a
            dictSet caseOwner cn un
            dictSet caseTag cn nextTag
            nextTag <- nextTag + 1

    let topArity = dictNew<string * int, int> ()   // (path,offset) -> arity of top-level fn
    let topName = dictNew<string * int, string> ()
    let mangle (v : VarId) = "$g" + string (abs (hash v.Path % 1000)) + "_" + string v.Offset + "_" + (v.Name |> String.map (fun c -> if System.Char.IsLetterOrDigit c then c else '_'))
    // extern signatures: param/result kinds derived from the scheme.
    // "i" = int (i32 ABI, wrapped), "r" = reference/other (opaque anyref)
    // scalar-typed signatures: (paramKinds, resultKind) for top-level fns
    // whose scheme is monomorphic in the scalar positions
    let sigKinds = dictNew<string * int, string list * string> ()
    let externs = dictNew<string * int, string list * string> ()
    let rec arrowArity (t : Fpp.Analysis.Types.Type) : int =
        match Fpp.Analysis.Types.prune t with
        | Fpp.Analysis.Types.TFun (_, b) -> 1 + arrowArity b
        | _ -> 0
    let abiKind (t : Fpp.Analysis.Types.Type) : string =
        match Fpp.Analysis.Types.prune t with
        | Fpp.Analysis.Types.TCon ("int", []) -> "i"
        | Fpp.Analysis.Types.TCon ("bool", []) -> "i"
        | Fpp.Analysis.Types.TCon ("char", []) -> "i"
        | _ -> "r"
    let rec abiSig (t : Fpp.Analysis.Types.Type) : string list * string =
        match Fpp.Analysis.Types.prune t with
        | Fpp.Analysis.Types.TFun (a, b) ->
            let ps, r = abiSig b
            abiKind a :: ps, r
        | r -> [], abiKind r
    let scalarKindOfTy (t : Fpp.Analysis.Types.Type) : string =
        match Fpp.Analysis.Types.prune t with
        | Fpp.Analysis.Types.TCon ("float", []) -> "f"
        | Fpp.Analysis.Types.TCon ("float32", []) -> "s"
        | Fpp.Analysis.Types.TCon ("int64", []) -> "l"
        | _ -> "u"
    let rec splitArrow (n : int) (t : Fpp.Analysis.Types.Type) : string list * string =
        if n = 0 then [], scalarKindOfTy t
        else
            match Fpp.Analysis.Types.prune t with
            | Fpp.Analysis.Types.TFun (a, b) ->
                let ps, r = splitArrow (n - 1) b
                scalarKindOfTy a :: ps, r
            | other -> [], scalarKindOfTy other
    for d in decls do
        match d with
        | DLet (_, v, sch, ELam (ps, _)) ->
            dictSet topArity (v.Path, v.Offset) ps.Length
            dictSet topName (v.Path, v.Offset) (mangle v)
            let pk, rk = splitArrow ps.Length sch.Body
            if pk.Length = ps.Length && (rk <> "u" || List.exists (fun k -> k <> "u") pk) then
                dictSet sigKinds (v.Path, v.Offset) (pk, rk)
        | DLet (_, v, _, _) ->
            dictSet topName (v.Path, v.Offset) (mangle v)
        | DExtern (v, sch) ->
            let ar = arrowArity sch.Body
            dictSet topArity (v.Path, v.Offset) ar
            dictSet topName (v.Path, v.Offset) (mangle v)
            dictSet externs (v.Path, v.Offset) (abiSig sch.Body)
        | _ -> ()

    // tuple arities used anywhere
    let tupleArities = vecNew<int> ()
    let noteTuple (n : int) =
        if not (List.contains n (vecToList tupleArities)) then vecAdd tupleArities n
    let rec scanPat (p : Pat) =
        match p with
        | PTuple ps -> noteTuple ps.Length; List.iter scanPat ps
        | PCtor (_, _, ps) | PListLit ps | POr ps -> List.iter scanPat ps
        | PCons (a, b) -> scanPat a; scanPat b
        | PAs (p, _, _) -> scanPat p
        | _ -> ()
    let rec scanExpr (e : Expr) =
        match e with
        | ETuple xs -> noteTuple xs.Length; List.iter scanExpr xs
        | ELam (_, b) -> scanExpr b
        | EApp (f, args) -> scanExpr f; List.iter scanExpr args
        | ELet (_, _, _, r, b) -> scanExpr r; scanExpr b
        | EIf (a, b, c) -> scanExpr a; scanExpr b; scanExpr c
        | EMatch (s, cs) ->
            scanExpr s
            for p, g, b in cs do
                scanPat p
                (match g with Some g -> scanExpr g | None -> ())
                scanExpr b
        | EListLit xs | ESeq xs | EPrim (_, xs) -> List.iter scanExpr xs
        | ECtor (_, _, xs) -> List.iter scanExpr xs
        | ERecord (_, fs) -> for _, v in fs do scanExpr v
        | EField (r, _) -> scanExpr r
        | EWhile (c, b) -> scanExpr c; scanExpr b
        | EAssign (_, e) -> scanExpr e
        | EArray (_, xs) -> List.iter scanExpr xs
        | EIndex (_, a, i) -> scanExpr a; scanExpr i
        | EIndexSet (_, a, i, v) -> scanExpr a; scanExpr i; scanExpr v
        | EArrayLen (_, a) -> scanExpr a
        | EArrayCreate (_, n, v) -> scanExpr n; scanExpr v
        | EArrayPin (_, a) -> scanExpr a
        | EArrayUnpin (_, a) -> scanExpr a
        | ETry (b, cs) ->
            scanExpr b
            for p, g, e in cs do
                scanPat p
                (match g with Some g -> scanExpr g | None -> ())
                scanExpr e
        | _ -> ()
    for d in decls do
        match d with
        | DLet (_, _, _, e) -> scanExpr e
        | _ -> ()

    // string literals -> passive data segments
    let strings = vecNew<string> ()
    let internString (bytes : string) : int =
        vecAdd strings bytes
        vecLen strings - 1

    let unescape (raw : string) : string =
        // raw includes the surrounding quotes
        let inner = substr raw 1 (strLen raw - 2)
        let out = System.Text.StringBuilder()
        let mutable i = 0
        while i < strLen inner do
            let c = charAt inner i
            if c = '\\' && i + 1 < strLen inner then
                (match charAt inner (i + 1) with
                 | 'n' -> out.Append '\n' |> ignore
                 | 't' -> out.Append '\t' |> ignore
                 | 'r' -> out.Append '\r' |> ignore
                 | '\\' -> out.Append '\\' |> ignore
                 | '"' -> out.Append '"' |> ignore
                 | '\'' -> out.Append '\'' |> ignore
                 | o -> out.Append o |> ignore)
                i <- i + 2
            else
                out.Append c |> ignore
                i <- i + 1
        out.ToString()

    let charCode (raw : string) : int =
        let s = unescape raw
        if strLen s > 0 then int (charAt s 0) else 0

    // ---- per-function compilation -----------------------------------------

    // lifted lambdas emitted at the end
    let lifted = vecNew<string> ()
    let mutable liftCount = 0
    // curry wrappers requested for top-level functions: (name, arity)
    let wrappers = vecNew<string * int> ()
    let requestWrappers (fname : string) (arity : int) =
        if not (vecToList wrappers |> List.exists (fun (n, _) -> n = fname)) then
            vecAdd wrappers (fname, arity)

    let boolWat (w : string) = "(ref.i31 " + w + ")"
    let unwrapI32 (w : string) = "(call $toi " + w + ")"
    let intWat (w : string) = "(call $ofi " + w + ")"

    // ---- scalar kind analysis: "f" f64, "s" f32, "l" i64, "u" uniform ----
    // (ints stay uniform: i31 immediates are allocation-free already)
    let localKinds = dictNew<string * int, string> ()
    let suffixedOps = [ "+"; "-"; "*"; "/"; "%" ]
    let rec kindOf (e : Expr) : string =
        match e with
        | ELit (LFloat t) -> if t.EndsWith "f" || t.EndsWith "F" then "s" else "f"
        | ELit (LInt t) -> if t.EndsWith "L" then "l" else "u"
        | EVar (v, _) ->
            (match dictTryFind localKinds (v.Path, v.Offset) with
             | Some k -> k
             | None -> "u")
        | EPrim (op, _) when op.Length > 1 && List.contains (op.Substring (0, op.Length - 1)) suffixedOps ->
            (let k = op.Substring (op.Length - 1)
             if k = "f" || k = "s" || k = "l" then k else "u")
        | EPrim ("u-f", _) -> "f"
        | EPrim ("u-s", _) -> "s"
        | EPrim ("u-l", _) -> "l"
        | EField (_, fname) ->
            (match dictTryFind fieldIndex fname with
             | Some (_, _, k) when k = "f" || k = "s" || k = "l" -> k
             | _ -> "u")
        | EIndex (nm, _, _) ->
            let k = primKindOf nm
            if k = "f" || k = "s" || k = "l" then k else "u"
        | EApp (EVar (v, _), args) ->
            (match dictTryFind sigKinds (v.Path, v.Offset), dictTryFind topArity (v.Path, v.Offset) with
             | Some (_, rk), Some ar when ar = args.Length -> rk
             | _ -> "u")
        | ELet (_, _, _, _, body) -> kindOf body
        | ESeq xs -> (match List.tryLast xs with Some x -> kindOf x | None -> "u")
        | EIf (_, t, f) ->
            let a, b = kindOf t, kindOf f
            if a = b then a else "u"
        | _ -> "u"
    let wasmTyOf (k : string) =
        match k with
        | "f" -> "f64" | "s" -> "f32" | "l" -> "i64" | _ -> "anyref"
    let boxK (k : string) (w : string) =
        match k with
        | "f" -> "(call $off " + w + ")" | "s" -> "(call $oss " + w + ")"
        | "l" -> "(call $ofl " + w + ")" | _ -> w
    let unboxK (k : string) (w : string) =
        match k with
        | "f" -> "(call $tof " + w + ")" | "s" -> "(call $tos " + w + ")"
        | "l" -> "(call $tol " + w + ")" | _ -> w

    /// Compile one function body. `locals` maps (path,offset) to wasm local
    /// names; `extraLocals` collects locals to declare.
    let rec compileExpr (locals : Dict<string * int, string>) (extraLocals : Vec<string * string>)
                        (freeEnv : Dict<string * int, int>) (tail : bool) (e : Expr) : string =
        let recur = compileExpr locals extraLocals freeEnv false
        let recurT = compileExpr locals extraLocals freeEnv tail
        let newTypedLocal (base_ : string) (ty : string) : string =
            let n = "$l" + string (vecLen extraLocals) + "_" + base_
            vecAdd extraLocals (n, ty)
            n
        let newLocal (base_ : string) : string = newTypedLocal base_ "anyref"
        match e with
        | ELit (LInt s) ->
            let digits =
                if s.StartsWith "0x" || s.StartsWith "0X" then
                    string (System.Convert.ToInt32 (s.TrimEnd ([| 'L'; 'u' |]), 16))
                else s |> String.filter (fun c -> isDigit c || c = '-')
            if s.EndsWith "L" then
                "(call $ofl (i64.const " + (if digits = "" then "0" else digits) + "))"
            else
                let v = if digits = "" then 0 else int digits
                "(call $ofi (i32.const " + string v + "))"
        | ELit (LBool b) -> "(ref.i31 (i32.const " + (if b then "1" else "0") + "))"
        | ELit LUnit -> "(ref.i31 (i32.const 0))"
        | ELit (LChar raw) -> "(ref.i31 (i32.const " + string (charCode raw) + "))"
        | ELit (LFloat s) ->
            let num = s |> String.filter (fun c -> isDigit c || c = '.' || c = '-' || c = 'e')
            if s.EndsWith "f" || s.EndsWith "F" then
                "(struct.new $boxs (f32.const " + num + "))"
            else
                "(struct.new $boxf (f64.const " + num + "))"
        | ELit (LString raw) ->
            let bytes = unescape raw
            let id = internString bytes
            "(array.new_data $str $d" + string id + " (i32.const 0) (i32.const " + string (System.Text.Encoding.UTF8.GetByteCount bytes) + "))"
        | EVar (v, _) ->
            let key = (v.Path, v.Offset)
            (match dictTryFind locals key with
             | Some l ->
                 (match dictTryFind localKinds key with
                  | Some k when k <> "u" -> boxK k ("(local.get " + l + ")")
                  | _ -> "(local.get " + l + ")")
             | None ->
                 match dictTryFind freeEnv key with
                 | Some idx ->
                     // walk the env cons-chain
                     let mutable w = "(local.get $env)"
                     for _ in 1 .. idx do
                         w <- "(struct.get $cons 1 (ref.cast (ref $cons) " + w + "))"
                     "(struct.get $cons 0 (ref.cast (ref $cons) " + w + "))"
                 | None ->
                     match dictTryFind topArity key, dictTryFind topName key with
                     | Some arity, Some fname ->
                         // function as a value: curried closure chain
                         requestWrappers fname arity
                         "(struct.new $clo (ref.func " + fname + ".w0) (ref.null any))"
                     | None, Some gname ->
                         "(global.get " + gname + ")"
                     | _ ->
                         vecAdd errors ("unbound variable " + v.Name)
                         "(ref.i31 (i32.const 0))")
        | EUnknown n ->
            vecAdd errors ("unknown name reaches emission: " + n)
            "(ref.i31 (i32.const 0))"
        | EApp (EField (EUnknown "Array", "create"), [ _; _ ]) ->
            vecAdd errors "Array.create needs a statically known element type"
            "(ref.i31 (i32.const 0))"
        | EApp (EField (EUnknown "Array", "length"), [ a ]) ->
            "(call $lenv " + recur a + ")"
        | EApp (EUnknown "memLoadF64", [ a ]) ->
            "(call $off (f64.load (call $toi " + recur a + ")))"
        | EApp (EUnknown "memStoreF32", [ a; v ]) ->
            // raw linear-memory store: the zero-copy bridge to JS/WebGPU
            "(block (result anyref) (f32.store (call $toi " + recur a + ") (f32.demote_f64 (call $tof " + recur v + "))) (ref.i31 (i32.const 0)))"
        | EApp (EUnknown "hash", [ a ]) ->
            "(call $ofi (call $hashv " + recur a + "))"
        | EApp (EUnknown "refEq", [ a; b ]) ->
            boolWat ("(ref.eq (ref.cast (ref null eq) " + recur a + ") (ref.cast (ref null eq) " + recur b + "))")
        | EApp (EUnknown "print", [ a ]) ->
            "(block (result anyref) (call $printval " + recur a + ") (call $putc (i32.const 10)) (ref.i31 (i32.const 0)))"
        | EApp (EUnknown "ignore", [ a ]) ->
            "(block (result anyref) (drop " + recur a + ") (ref.i31 (i32.const 0)))"
        | EApp (EUnknown "failwith", [ a ]) ->
            (match dictTryFind caseArity "Failure" with
             | Some _ -> "(block (result anyref) (throw $fppexn (struct.new $du1 (i32.const " + string (dictTryFind caseTag "Failure").Value + ") " + recur a + ")) (ref.i31 (i32.const 0)))"
             | None -> "(unreachable)")
        | EApp (EUnknown "raise", [ a ]) ->
            "(block (result anyref) (throw $fppexn " + recur a + ") (ref.i31 (i32.const 0)))"
        | EApp (EVar (v, _), args) when (dictTryFind topArity (v.Path, v.Offset)) = Some args.Length ->
            // known full-arity call: direct (tail position -> return_call)
            let fname = (dictTryFind topName (v.Path, v.Offset)).Value
            (match dictTryFind externs (v.Path, v.Offset) with
             | Some (pks, rk) ->
                 // FFI boundary: ints cross as i32, references pass opaque
                 let wrapped =
                     List.zip pks args
                     |> List.map (fun (k, a) -> if k = "i" then unwrapI32 (recur a) else recur a)
                 let call = "(call " + fname + " " + String.concat " " wrapped + ")"
                 if rk = "i" then "(call $ofi " + call + ")" else call
             | None ->
            let op = if tail then "return_call" else "call"
            match dictTryFind sigKinds (v.Path, v.Offset) with
            | Some (pks, rk) when pks.Length = args.Length ->
                let wrapped =
                    List.zip pks args
                    |> List.map (fun (k, a) -> if k = "u" then recur a else unboxK k (recur a))
                // tail calls need matching result types; a boxed result
                // means the raw call cannot be a tail call
                let opv = if rk = "u" then op else "call"
                let call = "(" + opv + " " + fname + " " + String.concat " " wrapped + ")"
                if rk = "u" then call else boxK rk call
            | _ -> "(" + op + " " + fname + " " + String.concat " " (List.map recur args) + ")")
        | EApp (f, args) ->
            let mutable w = recur f
            for a in args do
                w <- "(call $applyc " + w + " " + recur a + ")"
            w
        | ELam (ps, body) ->
            // curry to unary, closure-convert
            let rec curry (ps : (VarId * Fpp.Analysis.Types.Scheme) list) (body : Expr) : Expr =
                match ps with
                | [] -> body
                | [ _ ] -> ELam (ps, body)
                | p :: rest -> ELam ([ p ], curry rest body)
            (match curry ps body with
             | ELam ([ (pv, _) ], b) -> compileLambda locals freeEnv pv b recur
             | other -> recur other)
        | ELet (_, v, _, rhs, body) ->
            let k = kindOf rhs
            let l = newTypedLocal (v.Name |> String.map (fun c -> if System.Char.IsLetterOrDigit c then c else '_')) (wasmTyOf k)
            let r = recur rhs
            dictSet locals (v.Path, v.Offset) l
            dictSet localKinds (v.Path, v.Offset) k
            let stored = if k = "u" then r else unboxK k r
            "(block (result anyref) (local.set " + l + " " + stored + ") " + recurT body + ")"
        | EIf (c, t, f) ->
            "(if (result anyref) (i32.ne (i32.const 0) " + unwrapI32 (recur c) + ") (then "
            + recurT t + ") (else " + recurT f + "))"
        | EPrim (op, [ a; b ]) when
            (op.Length > 1 && (op.EndsWith "f" || op.EndsWith "l" || op.EndsWith "s" || op.EndsWith "t")
             && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "-"; "*"; "/"; "%"; "<"; ">"; "<="; ">=" ]) ->
            let baseOp = op.Substring (0, op.Length - 1)
            let kind = op.Substring (op.Length - 1)
            let un, box_, ty =
                match kind with
                | "f" -> "$tof", "$off", "f64"
                | "s" -> "$tos", "$oss", "f32"
                | "l" -> "$tol", "$ofl", "i64"
                | _ -> "$toi", "$ofi", "i32"
            let wa = "(call " + un + " " + recur a + ")"
            let wb = "(call " + un + " " + recur b + ")"
            if kind = "t" then
                // string ops: only + (concat) and comparisons via $equal
                (match baseOp with
                 | "+" -> "(call $strcat (ref.cast (ref $str) " + recur a + ") (ref.cast (ref $str) " + recur b + "))"
                 | _ ->
                     vecAdd errors ("unsupported string operator " + baseOp)
                     "(ref.i31 (i32.const 0))")
            else
                let instr =
                    match baseOp, kind with
                    | "+", ("f" | "s") -> ty + ".add" | "-", ("f" | "s") -> ty + ".sub"
                    | "*", ("f" | "s") -> ty + ".mul" | "/", ("f" | "s") -> ty + ".div"
                    | "%", ("f" | "s") -> "" // no float rem in wasm
                    | "+", _ -> ty + ".add" | "-", _ -> ty + ".sub"
                    | "*", _ -> ty + ".mul" | "/", _ -> ty + ".div_s" | "%", _ -> ty + ".rem_s"
                    | "<", ("f" | "s") -> ty + ".lt" | ">", ("f" | "s") -> ty + ".gt"
                    | "<=", ("f" | "s") -> ty + ".le" | ">=", ("f" | "s") -> ty + ".ge"
                    | "<", _ -> ty + ".lt_s" | ">", _ -> ty + ".gt_s"
                    | "<=", _ -> ty + ".le_s" | _ -> ty + ".ge_s"
                if instr = "" then
                    vecAdd errors "float remainder unsupported"
                    "(ref.i31 (i32.const 0))"
                elif baseOp = "<" || baseOp = ">" || baseOp = "<=" || baseOp = ">=" then
                    boolWat ("(" + instr + " " + wa + " " + wb + ")")
                else
                    "(call " + box_ + " (" + instr + " " + wa + " " + wb + "))"
        | EPrim ("u-f", [ a ]) -> "(call $off (f64.neg (call $tof " + recur a + ")))"
        | EPrim ("u-s", [ a ]) -> "(call $oss (f32.neg (call $tos " + recur a + ")))"
        | EPrim ("u-l", [ a ]) -> "(call $ofl (i64.sub (i64.const 0) (call $tol " + recur a + ")))"
        | EPrim ("u~~~", [ a ]) -> intWat ("(i32.xor " + unwrapI32 (recur a) + " (i32.const -1))")
        | EPrim (op, [ a; b ]) ->
            let ia = fun () -> unwrapI32 (recur a)
            let ib = fun () -> unwrapI32 (recur b)
            (match op with
             | "+" -> "(call $addv " + recur a + " " + recur b + ")"
             | "-" -> intWat ("(i32.sub " + ia () + " " + ib () + ")")
             | "*" -> intWat ("(i32.mul " + ia () + " " + ib () + ")")
             | "/" -> intWat ("(i32.div_s " + ia () + " " + ib () + ")")
             | "%" -> intWat ("(i32.rem_s " + ia () + " " + ib () + ")")
             | "<" -> boolWat ("(i32.lt_s " + ia () + " " + ib () + ")")
             | ">" -> boolWat ("(i32.gt_s " + ia () + " " + ib () + ")")
             | "<=" -> boolWat ("(i32.le_s " + ia () + " " + ib () + ")")
             | ">=" -> boolWat ("(i32.ge_s " + ia () + " " + ib () + ")")
             | "=" -> "(call $equal " + recur a + " " + recur b + ")"
             | "<>" -> boolWat ("(i32.eqz " + unwrapI32 ("(call $equal " + recur a + " " + recur b + ")") + ")")
             | "&&" -> recur (EIf (a, b, ELit (LBool false)))
             | "||" -> recur (EIf (a, ELit (LBool true), b))
             | "&&&" -> intWat ("(i32.and " + ia () + " " + ib () + ")")
             | "|||" -> intWat ("(i32.or " + ia () + " " + ib () + ")")
             | "^^^" -> intWat ("(i32.xor " + ia () + " " + ib () + ")")
             | "<<<" -> intWat ("(i32.shl " + ia () + " " + ib () + ")")
             | ">>>" -> intWat ("(i32.shr_s " + ia () + " " + ib () + ")")
             | "::" -> "(struct.new $cons " + recur a + " " + recur b + ")"
             | "@" -> "(call $append " + recur a + " " + recur b + ")"
             | _ ->
                 vecAdd errors ("unsupported operator " + op)
                 "(ref.i31 (i32.const 0))")
        | EPrim ("unot", [ a ]) -> boolWat ("(i32.eqz " + unwrapI32 (recur a) + ")")
        | EPrim ("u-", [ a ]) -> intWat ("(i32.sub (i32.const 0) " + unwrapI32 (recur a) + ")")
        | EPrim (op, _) ->
            vecAdd errors ("unsupported operator " + op)
            "(ref.i31 (i32.const 0))"
        | ETuple xs ->
            "(struct.new $tup" + string xs.Length + " " + String.concat " " (List.map recur xs) + ")"
        | EListLit xs ->
            List.foldBack (fun x acc -> "(struct.new $cons " + recur x + " " + acc + ")") xs "(ref.null any)"
        | ECtor (name, _, args) ->
            (match dictTryFind caseArity name with
             | Some 0 -> "(global.get $c_" + name + ")"
             | Some _ when not (List.isEmpty args) ->
                 "(struct.new $du1 (i32.const " + string (dictTryFind caseTag name).Value + ") " + String.concat " " (List.map recur args) + ")"
             | Some _ ->
                 // payload ctor referenced unapplied
                 vecAdd errors ("unapplied constructor " + name)
                 "(ref.i31 (i32.const 0))"
             | None ->
                 vecAdd errors ("unknown constructor " + name)
                 "(ref.i31 (i32.const 0))")
        | ERecord (_, fields) ->
            (match fields |> List.tryPick (fun (f, _) -> dictTryFind fieldIndex f) with
             | Some (rn, _, _) ->
                 let order = (dictTryFind recordOrder rn).Value
                 let unboxBy (k : string) (w : string) =
                     match k with
                     | "f" -> "(call $tof " + w + ")" | "s" -> "(call $tos " + w + ")"
                     | "l" -> "(call $tol " + w + ")" | "i" -> "(call $toi " + w + ")"
                     | _ -> w
                 let vals =
                     order
                     |> List.map (fun (fname, k) ->
                         match fields |> List.tryFind (fun (f, _) -> f = fname) with
                         | Some (_, v) -> unboxBy k (recur v)
                         | None ->
                             vecAdd errors ("missing field " + fname + " in " + rn)
                             "(ref.i31 (i32.const 0))")
                 "(struct.new $r_" + rn + " " + String.concat " " vals + ")"
             | None ->
                 vecAdd errors "record with unknown type"
                 "(ref.i31 (i32.const 0))")
        | EField (EIndex (nm, a, i), fname) when isPod nm && (dictTryFind fieldIndex fname).IsSome ->
            // fusion on packed arrays: single array.get + reinterpret
            let _, _, wd = (dictTryFind podLayout nm).Value
            let _, _, k = (dictTryFind fieldIndex fname).Value
            let baseW = "(i32.mul " + unwrapI32 (recur i) + " (i32.const " + string wd + "))"
            let raw = fieldFromWords nm (recur a) baseW fname
            (match k with
             | "f" | "s" | "l" -> boxK k raw
             | "i" -> "(call $ofi " + raw + ")"
             | _ -> raw)
        | EField (EIndex (nm, a, i), fname) when isStructName nm && (dictTryFind fieldIndex fname).IsSome ->
            // fusion: pts.[i].X reads the SoA field array directly — no
            // temporary struct materialization
            let _, fi, k = (dictTryFind fieldIndex fname).Value
            let src = "(struct.get $sarr_" + nm + " " + string fi + " (ref.cast (ref $sarr_" + nm + ") " + recur a + "))"
            let raw =
                match k with
                | "f" | "s" | "l" | "i" -> "(array.get " + parrOf k + " " + src + " " + unwrapI32 (recur i) + ")"
                | _ -> "(array.get $arr " + src + " " + unwrapI32 (recur i) + ")"
            (match k with
             | "f" | "s" | "l" -> boxK k raw
             | "i" -> "(call $ofi " + raw + ")"
             | _ -> raw)
        | EField (r, "Length") when not (dictTryFind fieldIndex "Length").IsSome ->
            "(call $lenv " + recur r + ")"
        | EField (r, fname) ->
            (match dictTryFind fieldIndex fname with
             | Some (rn, idx, k) ->
                 let raw = "(struct.get $r_" + rn + " " + string idx + " (ref.cast (ref $r_" + rn + ") " + recur r + "))"
                 (match k with
                  | "f" -> "(call $off " + raw + ")" | "s" -> "(call $oss " + raw + ")"
                  | "l" -> "(call $ofl " + raw + ")" | "i" -> "(call $ofi " + raw + ")"
                  | _ -> raw)
             | None ->
                 vecAdd errors ("unknown field " + fname)
                 "(ref.i31 (i32.const 0))")
        | ESeq xs ->
            (match List.rev xs with
             | [] -> "(ref.i31 (i32.const 0))"
             | last :: init ->
                 "(block (result anyref) "
                 + String.concat " " (List.rev init |> List.map (fun x -> "(drop " + recur x + ")"))
                 + " " + recurT last + ")")
        | EWhile (c, b) ->
            let lbl = newLocal "w"   // unique id (also declares a spare local)
            "(block (result anyref) (block $brk" + lbl + " (loop $cont" + lbl + " "
            + "(br_if $brk" + lbl + " (i32.eqz " + unwrapI32 (recur c) + ")) "
            + "(drop " + recur b + ") (br $cont" + lbl + "))) (ref.i31 (i32.const 0)))"
        | EAssign (v, e) ->
            (match dictTryFind locals (v.Path, v.Offset) with
             | Some l ->
                 let k = match dictTryFind localKinds (v.Path, v.Offset) with Some k -> k | None -> "u"
                 let stored = if k = "u" then recur e else unboxK k (recur e)
                 "(block (result anyref) (local.set " + l + " " + stored + ") (ref.i31 (i32.const 0)))"
             | None ->
                 match dictTryFind topName (v.Path, v.Offset) with
                 | Some g -> "(block (result anyref) (global.set " + g + " " + recur e + ") (ref.i31 (i32.const 0)))"
                 | None ->
                     vecAdd errors ("assignment to unknown " + v.Name)
                     "(ref.i31 (i32.const 0))")
        | EArray (elemName, xs) ->
            let pk = primKindOf elemName
            if pk <> "" then
                let vals = xs |> List.map (fun x -> "(call " + unboxOfKind pk + " " + recur x + ")")
                "(array.new_fixed " + parrOf pk + " " + string xs.Length + " " + String.concat " " vals + ")"
            elif isPod elemName then
                // C-image packed: N elements x strideWords i64 words
                let _, _, wd = (dictTryFind podLayout elemName).Value
                let elemLocals = xs |> List.map (fun _ -> newLocal "pk")
                let ops =
                    List.zip elemLocals xs
                    |> List.collect (fun (l, x) ->
                        [ for w in 0 .. wd - 1 ->
                            let word = wordFromStruct elemName l w
                            if w = 0 then "(block (result i64) (local.set " + l + " " + recur x + ") " + word + ")"
                            else word ])
                "(struct.new $hnd (array.new_fixed $pk " + string (xs.Length * wd) + " " + String.concat " " ops + ") (i32.const 0) (i32.const 0))"
            elif isStructName elemName then
                // SoA: element temps evaluated once (during the first field
                // array), then per-field extraction into typed arrays
                let fs = structRecords |> List.pick (fun (rn, fs) -> if rn = elemName then Some fs else None)
                let elemLocals = xs |> List.map (fun _ -> newLocal "sa")
                let fieldArr (fi : int) (k : string) =
                    let elemT = match k with "f" | "s" | "l" | "i" -> parrOf k | _ -> "$arr"
                    let ops =
                        List.zip elemLocals xs
                        |> List.map (fun (l, x) ->
                            let v = "(struct.get $r_" + elemName + " " + string fi + " (ref.cast (ref $r_" + elemName + ") (local.get " + l + ")))"
                            if fi = 0 then
                                "(block (result " + (match k with "f" -> "f64" | "s" -> "f32" | "l" -> "i64" | "i" -> "i32" | _ -> "anyref") + ") (local.set " + l + " " + recur x + ") " + v + ")"
                            else v)
                    "(array.new_fixed " + elemT + " " + string xs.Length + " " + String.concat " " ops + ")"
                let arrs = fs |> List.mapi (fun fi (_, k) -> fieldArr fi k)
                "(struct.new $sarr_" + elemName + " " + String.concat " " arrs + ")"
            else
                "(array.new_fixed $arr " + string xs.Length + " " + String.concat " " (List.map recur xs) + ")"
        | EIndex (nm, a, i) ->
            let pk = primKindOf nm
            if nm = "string" then
                "(ref.i31 (array.get_u $str (ref.cast (ref $str) " + recur a + ") " + unwrapI32 (recur i) + "))"
            elif pk <> "" then
                "(call " + boxOfKind pk + " (array.get " + parrOf pk + " (ref.cast (ref " + parrOf pk + ") " + recur a + ") " + unwrapI32 (recur i) + "))"
            elif isPod nm then
                let placed, _, wd = (dictTryFind podLayout nm).Value
                let al = newLocal "pa"
                let bl = newTypedLocal "pb" "i32"
                let arrW = "(local.get " + al + ")"
                let fieldsW =
                    placed |> List.map (fun (fn, _, _) -> fieldFromWords nm arrW ("(local.get " + bl + ")") fn)
                "(block (result anyref) (local.set " + al + " " + recur a + ") "
                + "(local.set " + bl + " (i32.mul " + unwrapI32 (recur i) + " (i32.const " + string wd + "))) "
                + "(struct.new $r_" + nm + " " + String.concat " " fieldsW + "))"
            elif isStructName nm then
                let fs = structRecords |> List.pick (fun (rn, fs) -> if rn = nm then Some fs else None)
                let al = newLocal "ia"
                let il = newLocal "ii"
                let idx = "(call $toi (local.get " + il + "))"
                let getF fi (k : string) =
                    let src = "(struct.get $sarr_" + nm + " " + string fi + " (ref.cast (ref $sarr_" + nm + ") (local.get " + al + ")))"
                    match k with
                    | "f" | "s" | "l" | "i" -> "(array.get " + parrOf k + " " + src + " " + idx + ")"
                    | _ -> "(array.get $arr " + src + " " + idx + ")"
                "(block (result anyref) (local.set " + al + " " + recur a + ") (local.set " + il + " (call $ofi " + unwrapI32 (recur i) + ")) "
                + "(struct.new $r_" + nm + " " + (fs |> List.mapi (fun fi (_, k) -> getF fi k) |> String.concat " ") + "))"
            else
                vecAdd errors "array read needs a statically known element type (specialization pending)"
                "(ref.i31 (i32.const 0))"
        | EIndexSet (nm, a, i, v) ->
            let pk = primKindOf nm
            if pk <> "" then
                "(block (result anyref) (array.set " + parrOf pk + " (ref.cast (ref " + parrOf pk + ") " + recur a + ") "
                + unwrapI32 (recur i) + " (call " + unboxOfKind pk + " " + recur v + ")) (ref.i31 (i32.const 0)))"
            elif isPod nm then
                let _, _, wd = (dictTryFind podLayout nm).Value
                let al = newLocal "wa"
                let bl = newTypedLocal "wb" "i32"
                let vl = newLocal "wv"
                let arrW = "(local.get " + al + ")"
                let sets =
                    [ for w in 0 .. wd - 1 ->
                        hWordSet arrW ("(i32.add (local.get " + bl + ") (i32.const " + string w + "))") (wordFromStruct nm vl w) ]
                "(block (result anyref) (local.set " + al + " " + recur a + ") "
                + "(local.set " + bl + " (i32.mul " + unwrapI32 (recur i) + " (i32.const " + string wd + "))) "
                + "(local.set " + vl + " " + recur v + ") "
                + String.concat " " sets + " (ref.i31 (i32.const 0)))"
            elif isStructName nm then
                let fs = structRecords |> List.pick (fun (rn, fs) -> if rn = nm then Some fs else None)
                let al = newLocal "sa"
                let il = newLocal "si"
                let vl = newLocal "sv"
                let setF fi (k : string) =
                    let dst = "(struct.get $sarr_" + nm + " " + string fi + " (ref.cast (ref $sarr_" + nm + ") (local.get " + al + ")))"
                    let fv = "(struct.get $r_" + nm + " " + string fi + " (ref.cast (ref $r_" + nm + ") (local.get " + vl + ")))"
                    match k with
                    | "f" | "s" | "l" | "i" -> "(array.set " + parrOf k + " " + dst + " (call $toi (local.get " + il + ")) " + fv + ")"
                    | _ -> "(array.set $arr " + dst + " (call $toi (local.get " + il + ")) " + fv + ")"
                "(block (result anyref) (local.set " + al + " " + recur a + ") (local.set " + il + " (call $ofi " + unwrapI32 (recur i) + ")) (local.set " + vl + " " + recur v + ") "
                + (fs |> List.mapi (fun fi (_, k) -> setF fi k) |> String.concat " ") + " (ref.i31 (i32.const 0)))"
            else
                vecAdd errors "array write needs a statically known element type (specialization pending)"
                "(ref.i31 (i32.const 0))"
        | EArrayPin (nm, a) ->
            if isPod nm then "(call $ofi (call $pinh " + recur a + "))"
            else
                vecAdd errors "Array.pin requires a POD struct array"
                "(ref.i31 (i32.const 0))"
        | EArrayUnpin (nm, a) ->
            if isPod nm then "(call $ofi (call $unpinh " + recur a + "))"
            else
                vecAdd errors "Array.unpin requires a POD struct array"
                "(ref.i31 (i32.const 0))"
        | EArrayLen (nm, a) ->
            let pk = primKindOf nm
            if nm = "string" then
                "(call $ofi (array.len (ref.cast (ref $str) " + recur a + ")))"
            elif pk <> "" then
                "(call $ofi (array.len (ref.cast (ref " + parrOf pk + ") " + recur a + ")))"
            elif isPod nm then
                let _, _, wd = (dictTryFind podLayout nm).Value
                "(call $ofi (i32.div_u " + hLen (recur a) + " (i32.const " + string wd + ")))"
            elif isStructName nm then
                "(call $ofi (array.len (struct.get $sarr_" + nm + " 0 (ref.cast (ref $sarr_" + nm + ") " + recur a + "))))"
            else
                vecAdd errors "length needs a statically known element type"
                "(ref.i31 (i32.const 0))"
        | EArrayCreate (nm, n, v) ->
            let pk = primKindOf nm
            if pk <> "" then
                "(array.new " + parrOf pk + " (call " + unboxOfKind pk + " " + recur v + ") " + unwrapI32 (recur n) + ")"
            elif isPod nm then
                let _, _, wd = (dictTryFind podLayout nm).Value
                let nl = newTypedLocal "kn" "i32"
                let vl = newLocal "kv"
                let arl = newLocal "ka"
                let jl = newTypedLocal "kj" "i32"
                let arrW = "(local.get " + arl + ")"
                let sets =
                    [ for w in 0 .. wd - 1 ->
                        hWordSet arrW ("(i32.add (i32.mul (local.get " + jl + ") (i32.const " + string wd + ")) (i32.const " + string w + "))") (wordFromStruct nm vl w) ]
                "(block (result anyref) (local.set " + nl + " " + unwrapI32 (recur n) + ") (local.set " + vl + " " + recur v + ") "
                + "(local.set " + arl + " (struct.new $hnd (array.new_default $pk (i32.mul (local.get " + nl + ") (i32.const " + string wd + "))) (i32.const 0) (i32.const 0))) "
                + "(local.set " + jl + " (i32.const 0)) "
                + "(block $kd" + jl + " (loop $kl" + jl + " (br_if $kd" + jl + " (i32.ge_u (local.get " + jl + ") (local.get " + nl + "))) "
                + String.concat " " sets + " (local.set " + jl + " (i32.add (local.get " + jl + ") (i32.const 1))) (br $kl" + jl + "))) "
                + "(local.get " + arl + "))"
            elif isStructName nm then
                let fs = structRecords |> List.pick (fun (rn, fs) -> if rn = nm then Some fs else None)
                let nl = newLocal "cn"
                let vl = newLocal "cv"
                let mk fi (k : string) =
                    let fv = "(struct.get $r_" + nm + " " + string fi + " (ref.cast (ref $r_" + nm + ") (local.get " + vl + ")))"
                    match k with
                    | "f" | "s" | "l" | "i" -> "(array.new " + parrOf k + " " + fv + " (call $toi (local.get " + nl + ")))"
                    | _ -> "(array.new $arr " + fv + " (call $toi (local.get " + nl + ")))"
                "(block (result anyref) (local.set " + nl + " (call $ofi " + unwrapI32 (recur n) + ")) (local.set " + vl + " " + recur v + ") "
                + "(struct.new $sarr_" + nm + " " + (fs |> List.mapi (fun fi (_, k) -> mk fi k) |> String.concat " ") + "))"
            else
                vecAdd errors "Array.create needs a statically known element type"
                "(ref.i31 (i32.const 0))"
        | ETry (body, cases) ->
            let cases =
                cases
                |> List.collect (fun (p, g, b) ->
                    match p with
                    | POr ps -> ps |> List.map (fun q -> q, g, b)
                    | _ -> [ p, g, b ])
            let res = newLocal "tres"
            let exn = newLocal "texn"
            let w = System.Text.StringBuilder()
            w.Append("(block (result anyref) (block $tdone" + res + " (local.set " + exn + " (block $tcatch" + res + " (result anyref) ") |> ignore
            w.Append("(try_table (catch $fppexn $tcatch" + res + ") (local.set " + res + " " + recur body + ")) ") |> ignore
            w.Append("(br $tdone" + res + "))) ") |> ignore
            cases |> List.iteri (fun i (pat, guard, cbody) ->
                let lbl = "$tcase" + res + "_" + string i
                w.Append("(block " + lbl + " ") |> ignore
                let tests = System.Text.StringBuilder()
                compilePat locals extraLocals freeEnv tests lbl ("(local.get " + exn + ")") pat
                w.Append(tests.ToString()) |> ignore
                (match guard with
                 | Some g -> w.Append("(br_if " + lbl + " (i32.eqz " + unwrapI32 (recur g) + ")) ") |> ignore
                 | None -> ())
                w.Append("(local.set " + res + " " + recur cbody + ") (br $tdone" + res + ") ") |> ignore
                w.Append(")") |> ignore)
            w.Append(" (throw $fppexn (local.get " + exn + "))) (local.get " + res + "))") |> ignore
            w.ToString()
        | EMatch (scrut, cases) ->
            // expand or-patterns into separate cases
            let cases =
                cases
                |> List.collect (fun (p, g, b) ->
                    match p with
                    | POr ps -> ps |> List.map (fun q -> q, g, b)
                    | _ -> [ p, g, b ])
            let sl = newLocal "scrut"
            let res = newLocal "res"
            let w = System.Text.StringBuilder()
            w.Append("(block (result anyref) (local.set " + sl + " " + recur scrut + ") (block $done" + res + " ") |> ignore
            cases |> List.iteri (fun i (pat, guard, body) ->
                let lbl = "$case" + res + "_" + string i
                w.Append("(block " + lbl + " ") |> ignore
                let tests = System.Text.StringBuilder()
                compilePat locals extraLocals freeEnv tests lbl ("(local.get " + sl + ")") pat
                w.Append(tests.ToString()) |> ignore
                (match guard with
                 | Some g ->
                     w.Append("(br_if " + lbl + " (i32.eqz " + unwrapI32 (recur g) + ")) ") |> ignore
                 | None -> ())
                w.Append("(local.set " + res + " " + recur body + ") (br $done" + res + ") ") |> ignore
                w.Append(")") |> ignore)
            w.Append(" (unreachable)) (local.get " + res + "))") |> ignore
            w.ToString()

    /// Emit tests (branching to failLbl on mismatch) and binds for a pattern
    /// against the value expression `v`.
    and compilePat locals extraLocals freeEnv (out : System.Text.StringBuilder) (failLbl : string) (v : string) (p : Pat) : unit =
        let app (s : string) = out.Append(s + " ") |> ignore
        let newLocal (base_ : string) =
            let n = "$p" + string (vecLen extraLocals) + "_" + base_
            vecAdd extraLocals (n, "anyref")
            n
        match p with
        | PWild -> ()
        | POr _ -> ()   // expanded at EMatch level
        | PVar (var, _) ->
            let l = newLocal "v"
            dictSet locals (var.Path, var.Offset) l
            app ("(local.set " + l + " " + v + ")")
        | PAs (inner, var, _) ->
            let l = newLocal "as"
            dictSet locals (var.Path, var.Offset) l
            app ("(local.set " + l + " " + v + ")")
            compilePat locals extraLocals freeEnv out failLbl ("(local.get " + l + ")") inner
        | PLit LUnit -> ()
        | PLit (LInt s) ->
            let digits =
                if s.StartsWith "0x" || s.StartsWith "0X" then
                    string (System.Convert.ToInt32 (s.TrimEnd ([| 'L'; 'u' |]), 16))
                else s |> String.filter (fun c -> isDigit c || c = '-')
            let n = if digits = "" then 0 else int digits
            app ("(br_if " + failLbl + " (i32.eqz (i32.or (ref.test (ref i31) " + v + ") (ref.test (ref $boxi) " + v + "))))")
            app ("(br_if " + failLbl + " (i32.ne (i32.const " + string n + ") " + unwrapI32 v + "))")
        | PLit (LBool b) ->
            app ("(br_if " + failLbl + " (i32.ne (i32.const " + (if b then "1" else "0") + ") " + unwrapI32 v + "))")
        | PLit (LChar raw) ->
            app ("(br_if " + failLbl + " (i32.ne (i32.const " + string (charCode raw) + ") " + unwrapI32 v + "))")
        | PLit (LString raw) ->
            let lit = compileExpr locals extraLocals freeEnv false (ELit (LString raw))
            app ("(br_if " + failLbl + " (i32.eqz " + unwrapI32 ("(call $equal " + v + " " + lit + ")") + "))")
        | PLit (LFloat _) ->
            vecAdd errors "float patterns unsupported"
        | PCtor (name, _, args) ->
            (match dictTryFind caseArity name with
             | Some a ->
                 let ty = if a = 0 then "$du0" else "$du1"
                 let tag = string (dictTryFind caseTag name).Value
                 app ("(br_if " + failLbl + " (i32.eqz (ref.test (ref " + ty + ") " + v + ")))")
                 app ("(br_if " + failLbl + " (i32.ne (i32.const " + tag + ") (struct.get " + ty + " 0 (ref.cast (ref " + ty + ") " + v + "))))")
                 args |> List.iteri (fun i a2 ->
                     let field = "(struct.get $du1 1 (ref.cast (ref $du1) " + v + "))"
                     compilePat locals extraLocals freeEnv out failLbl field a2)
             | None -> vecAdd errors ("unknown constructor pattern " + name))
        | PTuple ps ->
            let tn = "$tup" + string ps.Length
            ps |> List.iteri (fun i a ->
                let field = "(struct.get " + tn + " " + string i + " (ref.cast (ref " + tn + ") " + v + "))"
                compilePat locals extraLocals freeEnv out failLbl field a)
        | PCons (h, t) ->
            app ("(br_if " + failLbl + " (i32.eqz (ref.test (ref $cons) " + v + ")))")
            compilePat locals extraLocals freeEnv out failLbl ("(struct.get $cons 0 (ref.cast (ref $cons) " + v + "))") h
            compilePat locals extraLocals freeEnv out failLbl ("(struct.get $cons 1 (ref.cast (ref $cons) " + v + "))") t
        | PListLit ps ->
            let mutable cur = v
            for a in ps do
                app ("(br_if " + failLbl + " (i32.eqz (ref.test (ref $cons) " + cur + ")))")
                compilePat locals extraLocals freeEnv out failLbl ("(struct.get $cons 0 (ref.cast (ref $cons) " + cur + "))") a
                cur <- "(struct.get $cons 1 (ref.cast (ref $cons) " + cur + "))"
            app ("(br_if " + failLbl + " (i32.eqz (ref.is_null " + cur + ")))")

    /// Lift a unary lambda into a top-level $u1 function; returns closure
    /// construction code.
    and compileLambda (outerLocals : Dict<string * int, string>) (outerFree : Dict<string * int, int>)
                      (pv : VarId) (body : Expr) (recurOuter : Expr -> string) : string =
        // free variables: locals/free-env of the enclosing function used in body
        let free = vecNew<string * int> ()
        let bound = dictNew<string * int, bool> ()
        dictSet bound (pv.Path, pv.Offset) true
        let noteFree (k : string * int) =
            if not (dictTryFind bound k).IsSome
               && ((dictTryFind outerLocals k).IsSome || (dictTryFind outerFree k).IsSome)
               && not (vecToList free |> List.contains k) then
                vecAdd free k
        let rec walk (e : Expr) =
            match e with
            | EVar (v, _) -> noteFree (v.Path, v.Offset)
            | ELam (ps, b) ->
                for v, _ in ps do dictSet bound (v.Path, v.Offset) true
                walk b
            | ELet (_, v, _, r, b) ->
                walk r
                dictSet bound (v.Path, v.Offset) true
                walk b
            | EApp (f, args) -> walk f; List.iter walk args
            | EIf (a, b, c) -> walk a; walk b; walk c
            | EMatch (s, cs) ->
                walk s
                for p, g, b in cs do
                    let rec bindP (p : Pat) =
                        match p with
                        | PVar (v, _) | PAs (_, v, _) -> dictSet bound (v.Path, v.Offset) true
                        | PCtor (_, _, ps) | PTuple ps | PListLit ps | POr ps -> List.iter bindP ps
                        | PCons (a, b) -> bindP a; bindP b
                        | _ -> ()
                    bindP p
                    (match g with Some g -> walk g | None -> ())
                    walk b
            | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) -> List.iter walk xs
            | ECtor (_, _, xs) -> List.iter walk xs
            | ERecord (_, fs) -> for _, v in fs do walk v
            | EField (r, _) -> walk r
            | EWhile (c, b) -> walk c; walk b
            | EAssign (v, e) -> noteFree (v.Path, v.Offset); walk e
            | EArray (_, xs) -> List.iter walk xs
            | EIndex (_, a, i) -> walk a; walk i
            | EIndexSet (_, a, i, v) -> walk a; walk i; walk v
            | EArrayLen (_, a) -> walk a
            | EArrayCreate (_, n, v) -> walk n; walk v
            | EArrayPin (_, a) -> walk a
            | EArrayUnpin (_, a) -> walk a
            | ETry (b, cs) ->
                walk b
                for p, g, e in cs do
                    let rec bindP (p : Pat) =
                        match p with
                        | PVar (v, _) | PAs (_, v, _) -> dictSet bound (v.Path, v.Offset) true
                        | PCtor (_, _, ps) | PTuple ps | PListLit ps | POr ps -> List.iter bindP ps
                        | PCons (a, b) -> bindP a; bindP b
                        | _ -> ()
                    bindP p
                    (match g with Some g -> walk g | None -> ())
                    walk e
            | _ -> ()
        walk body
        let freeList = vecToList free
        liftCount <- liftCount + 1
        let fname = "$lam" + string liftCount
        // compile the lifted body: param -> $a, free vars -> env chain
        let innerLocals = dictNew<string * int, string> ()
        dictSet innerLocals (pv.Path, pv.Offset) "$a"
        let innerFree = dictNew<string * int, int> ()
        freeList |> List.iteri (fun i k -> dictSet innerFree k i)
        let innerExtra = vecNew<string * string> ()
        let bodyW = compileExpr innerLocals innerExtra innerFree true body
        let localDecls = vecToList innerExtra |> List.map (fun (l, ty) -> "(local " + l + " " + ty + ")") |> String.concat " "
        vecAdd lifted
            ("(func " + fname + " (type $u1) (param $a anyref) (param $env anyref) (result anyref) "
             + localDecls + " " + bodyW + ")")
        // build the env chain from the enclosing scope (reverse order so
        // index i is reached by i cdr steps)
        let envW =
            List.foldBack
                (fun k acc -> "(struct.new $cons " + recurOuter (EVar ({ Path = fst k; Offset = snd k; Name = "_free" }, Fpp.Analysis.Types.mono (Fpp.Analysis.Types.TCon ("?", [])))) + " " + acc + ")")
                freeList "(ref.null any)"
        "(struct.new $clo (ref.func " + fname + ") " + envW + ")"

    // ---- module assembly --------------------------------------------------

    line "(module"
    line "  (type $u1 (func (param anyref anyref) (result anyref)))"
    line "  (type $clo (struct (field (ref $u1)) (field anyref)))"
    line "  (type $cons (struct (field anyref) (field anyref)))"
    line "  (type $str (array (mut i8)))"
    line "  (type $boxf (struct (field f64)))"
    line "  (type $boxi (struct (field i32)))"
    line "  (type $arr (array (mut anyref)))"
    line "  (type $parr_i (array (mut i32)))"
    line "  (type $parr_f (array (mut f64)))"
    line "  (type $parr_s (array (mut f32)))"
    line "  (type $parr_l (array (mut i64)))"
    line "  (type $pk (array (mut i64)))"
    // POD array value = handle: storage (null while pinned), ptr, words
    line "  (type $hnd (struct (field (mut (ref null $pk))) (field (mut i32)) (field (mut i32))))"
    line "  (type $boxl (struct (field i64)))"
    line "  (type $boxs (struct (field f32)))"
    line "  (import \"wasi_snapshot_preview1\" \"fd_write\" (func $fd_write (param i32 i32 i32 i32) (result i32)))"
    for d in decls do
        match d with
        | DExtern (v, sch) ->
            let pks, rk = abiSig sch.Body
            let ps = pks |> List.map (fun k -> if k = "i" then "(param i32)" else "(param anyref)") |> String.concat " "
            let rs = if rk = "i" then "(result i32)" else "(result anyref)"
            line ("  (import \"env\" \"" + v.Name + "\" (func " + mangle v + " " + ps + " " + rs + "))")
        | _ -> ()
    line "  (memory (export \"memory\") 17)"   // 1 page scratch + 16 pages pin heap
    line "  (tag $fppexn (param anyref))"
    line "  (global $heap (mut i32) (i32.const 65536))"

    // program-declared types
    for rn, fs, st in records do
        let fieldTy (k : string) =
            match kindOfField st k with
            | "f" -> "(field f64)" | "s" -> "(field f32)"
            | "l" -> "(field i64)" | "i" -> "(field i32)"
            | _ -> "(field anyref)"
        let fields = fs |> List.map (fun (_, k) -> fieldTy k) |> String.concat " "
        line ("  (type $r_" + rn + " (struct " + fields + "))")
    for rn, fs in structRecords do
      if not (isPod rn) then
        let fa (k : string) =
            match k with
            | "f" | "s" | "l" | "i" -> "(field (ref " + parrOf k + "))"
            | _ -> "(field (ref $arr))"
        line ("  (type $sarr_" + rn + " (struct " + (fs |> List.map (fun (_, k) -> fa k) |> String.concat " ") + "))")
    // DU cases share two tagged layouts — wasm-GC canonicalizes
    // same-shaped struct types into ONE heap type, so per-case types
    // cannot be distinguished by ref.test; the i32 tag does it instead
    line "  (type $du0 (struct (field i32)))"
    line "  (type $du1 (struct (field i32) (field anyref)))"
    for n in vecToList tupleArities do
        let fields = List.replicate n "(field anyref)" |> String.concat " "
        line ("  (type $tup" + string n + " (struct " + fields + "))")

    // nullary case singletons
    for _, cs in unions do
        for cn, a in cs do
            if a = 0 then
                line ("  (global $c_" + cn + " (ref $du0) (struct.new $du0 (i32.const " + string (dictTryFind caseTag cn).Value + ")))")

    // runtime: putc, print, itoa, equal, append, apply
    line """  (func $putc (param $c i32)
    (i32.store8 (i32.const 64) (local.get $c))
    (i32.store (i32.const 0) (i32.const 64))
    (i32.store (i32.const 4) (i32.const 1))
    (drop (call $fd_write (i32.const 1) (i32.const 0) (i32.const 1) (i32.const 8))))
  (func $printi (param $n i32)
    (local $m i32)
    (if (i32.lt_s (local.get $n) (i32.const 0))
      (then (call $putc (i32.const 45))
            (local.set $n (i32.sub (i32.const 0) (local.get $n)))))
    (local.set $m (i32.div_s (local.get $n) (i32.const 10)))
    (if (i32.gt_s (local.get $m) (i32.const 0)) (then (call $printi (local.get $m))))
    (call $putc (i32.add (i32.const 48) (i32.rem_s (local.get $n) (i32.const 10)))))
  (func $prints (param $s (ref $str))
    (local $i i32)
    (block $done
      (loop $go
        (br_if $done (i32.ge_u (local.get $i) (array.len (local.get $s))))
        (call $putc (array.get_u $str (local.get $s) (local.get $i)))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $go))))
  (func $printval (param $v anyref)
    (if (ref.test (ref i31) (local.get $v))
      (then (call $printi (i31.get_s (ref.cast (ref i31) (local.get $v)))) (return)))
    (if (ref.test (ref $str) (local.get $v))
      (then (call $prints (ref.cast (ref $str) (local.get $v))) (return)))
    (if (ref.test (ref $boxi) (local.get $v))
      (then (call $printi (struct.get $boxi 0 (ref.cast (ref $boxi) (local.get $v)))) (return)))
    (if (ref.test (ref $boxl) (local.get $v))
      (then (call $printl (struct.get $boxl 0 (ref.cast (ref $boxl) (local.get $v)))) (return)))
    (if (ref.test (ref $boxf) (local.get $v))
      (then (call $printf64 (struct.get $boxf 0 (ref.cast (ref $boxf) (local.get $v)))) (return)))
    (if (ref.test (ref $boxs) (local.get $v))
      (then (call $printf64 (f64.promote_f32 (struct.get $boxs 0 (ref.cast (ref $boxs) (local.get $v))))) (return)))
    (call $putc (i32.const 63)))
  (func $equal (param $a anyref) (param $b anyref) (result anyref)
    (local $i i32)
    (if (i32.and (ref.test (ref i31) (local.get $a)) (ref.test (ref i31) (local.get $b)))
      (then (return (ref.i31 (i32.eq (i31.get_s (ref.cast (ref i31) (local.get $a)))
                                     (i31.get_s (ref.cast (ref i31) (local.get $b))))))))
    (if (i32.and (ref.test (ref $str) (local.get $a)) (ref.test (ref $str) (local.get $b)))
      (then
        (if (i32.ne (array.len (ref.cast (ref $str) (local.get $a))) (array.len (ref.cast (ref $str) (local.get $b))))
          (then (return (ref.i31 (i32.const 0)))))
        (block $ne
          (loop $go
            (br_if $ne (i32.ge_u (local.get $i) (array.len (ref.cast (ref $str) (local.get $a)))))
            (if (i32.ne (array.get_u $str (ref.cast (ref $str) (local.get $a)) (local.get $i))
                        (array.get_u $str (ref.cast (ref $str) (local.get $b)) (local.get $i)))
              (then (return (ref.i31 (i32.const 0)))))
            (local.set $i (i32.add (local.get $i) (i32.const 1)))
            (br $go)))
        (return (ref.i31 (i32.const 1)))))
    (if (i32.and (ref.test (ref $boxl) (local.get $a)) (ref.test (ref $boxl) (local.get $b)))
      (then (return (ref.i31 (i64.eq (struct.get $boxl 0 (ref.cast (ref $boxl) (local.get $a)))
                                     (struct.get $boxl 0 (ref.cast (ref $boxl) (local.get $b))))))))
    (if (i32.and (ref.test (ref $boxf) (local.get $a)) (ref.test (ref $boxf) (local.get $b)))
      (then (return (ref.i31 (f64.eq (struct.get $boxf 0 (ref.cast (ref $boxf) (local.get $a)))
                                     (struct.get $boxf 0 (ref.cast (ref $boxf) (local.get $b))))))))
    (if (i32.and (ref.test (ref $boxs) (local.get $a)) (ref.test (ref $boxs) (local.get $b)))
      (then (return (ref.i31 (f32.eq (struct.get $boxs 0 (ref.cast (ref $boxs) (local.get $a)))
                                     (struct.get $boxs 0 (ref.cast (ref $boxs) (local.get $b))))))))
    (if (i32.and (ref.test (ref $boxi) (local.get $a)) (ref.test (ref $boxi) (local.get $b)))
      (then (return (ref.i31 (i32.eq (struct.get $boxi 0 (ref.cast (ref $boxi) (local.get $a)))
                                     (struct.get $boxi 0 (ref.cast (ref $boxi) (local.get $b))))))))
    (if (i32.and (ref.is_null (local.get $a)) (ref.is_null (local.get $b)))
      (then (return (ref.i31 (i32.const 1)))))
    (if (i32.and (ref.test (ref $cons) (local.get $a)) (ref.test (ref $cons) (local.get $b)))
      (then
        (if (i32.eqz (i31.get_s (ref.cast (ref i31) (call $equal
              (struct.get $cons 0 (ref.cast (ref $cons) (local.get $a)))
              (struct.get $cons 0 (ref.cast (ref $cons) (local.get $b)))))))
          (then (return (ref.i31 (i32.const 0)))))
        (return (call $equal
          (struct.get $cons 1 (ref.cast (ref $cons) (local.get $a)))
          (struct.get $cons 1 (ref.cast (ref $cons) (local.get $b)))))))
    (ref.i31 (ref.eq (ref.cast (ref null eq) (local.get $a)) (ref.cast (ref null eq) (local.get $b)))))
  (func $balloc (param $bytes i32) (result i32)
    (local $p i32)
    (local.set $p (global.get $heap))
    (global.set $heap (i32.and (i32.add (i32.add (local.get $p) (local.get $bytes)) (i32.const 7)) (i32.const -8)))
    (local.get $p))
  (func $pinh (param $h anyref) (result i32)
    (local $s (ref null $pk)) (local $n i32) (local $i i32) (local $p i32)
    (local.set $s (struct.get $hnd 0 (ref.cast (ref $hnd) (local.get $h))))
    (if (ref.is_null (local.get $s))
      (then (return (struct.get $hnd 1 (ref.cast (ref $hnd) (local.get $h))))))
    (local.set $n (array.len (local.get $s)))
    (local.set $p (call $balloc (i32.mul (local.get $n) (i32.const 8))))
    (block $d (loop $go
      (br_if $d (i32.ge_u (local.get $i) (local.get $n)))
      (i64.store (i32.add (local.get $p) (i32.mul (local.get $i) (i32.const 8)))
                 (array.get $pk (local.get $s) (local.get $i)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $go)))
    (struct.set $hnd 1 (ref.cast (ref $hnd) (local.get $h)) (local.get $p))
    (struct.set $hnd 2 (ref.cast (ref $hnd) (local.get $h)) (local.get $n))
    ;; drop the GC storage: managed side is reclaimed while pinned
    (struct.set $hnd 0 (ref.cast (ref $hnd) (local.get $h)) (ref.null $pk))
    (local.get $p))
  (func $unpinh (param $h anyref) (result i32)
    (local $s (ref $pk)) (local $n i32) (local $i i32) (local $p i32)
    (if (i32.eqz (ref.is_null (struct.get $hnd 0 (ref.cast (ref $hnd) (local.get $h)))))
      (then (return (i32.const 0))))
    (local.set $n (struct.get $hnd 2 (ref.cast (ref $hnd) (local.get $h))))
    (local.set $p (struct.get $hnd 1 (ref.cast (ref $hnd) (local.get $h))))
    (local.set $s (array.new_default $pk (local.get $n)))
    (block $d (loop $go
      (br_if $d (i32.ge_u (local.get $i) (local.get $n)))
      (array.set $pk (local.get $s) (local.get $i)
                 (i64.load (i32.add (local.get $p) (i32.mul (local.get $i) (i32.const 8)))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $go)))
    (struct.set $hnd 0 (ref.cast (ref $hnd) (local.get $h)) (local.get $s))
    (struct.set $hnd 1 (ref.cast (ref $hnd) (local.get $h)) (i32.const 0))
    (i32.const 0))
  (func $hashv (param $v anyref) (result i32)
    (local $i i32) (local $h i32)
    (if (ref.test (ref i31) (local.get $v))
      (then (return (i31.get_s (ref.cast (ref i31) (local.get $v))))))
    (if (ref.test (ref $boxi) (local.get $v))
      (then (return (struct.get $boxi 0 (ref.cast (ref $boxi) (local.get $v))))))
    (if (ref.test (ref $boxl) (local.get $v))
      (then (return (i32.xor
        (i32.wrap_i64 (struct.get $boxl 0 (ref.cast (ref $boxl) (local.get $v))))
        (i32.wrap_i64 (i64.shr_u (struct.get $boxl 0 (ref.cast (ref $boxl) (local.get $v))) (i64.const 32)))))))
    (if (ref.test (ref $boxf) (local.get $v))
      (then (return (i32.xor
        (i32.wrap_i64 (i64.reinterpret_f64 (struct.get $boxf 0 (ref.cast (ref $boxf) (local.get $v)))))
        (i32.wrap_i64 (i64.shr_u (i64.reinterpret_f64 (struct.get $boxf 0 (ref.cast (ref $boxf) (local.get $v)))) (i64.const 32)))))))
    (if (ref.test (ref $str) (local.get $v))
      (then
        (local.set $h (i32.const -2128831035))
        (block $d (loop $go
          (br_if $d (i32.ge_u (local.get $i) (array.len (ref.cast (ref $str) (local.get $v)))))
          (local.set $h (i32.mul (i32.xor (local.get $h)
            (array.get_u $str (ref.cast (ref $str) (local.get $v)) (local.get $i))) (i32.const 16777619)))
          (local.set $i (i32.add (local.get $i) (i32.const 1)))
          (br $go)))
        (return (local.get $h))))
    (if (ref.is_null (local.get $v)) (then (return (i32.const 0))))
    (if (ref.test (ref $cons) (local.get $v))
      (then (return (i32.xor
        (i32.mul (call $hashv (struct.get $cons 0 (ref.cast (ref $cons) (local.get $v)))) (i32.const 31))
        (call $hashv (struct.get $cons 1 (ref.cast (ref $cons) (local.get $v))))))))
    (i32.const 1))
  (func $append (param $a anyref) (param $b anyref) (result anyref)
    (if (result anyref) (ref.test (ref $cons) (local.get $a))
      (then (struct.new $cons
        (struct.get $cons 0 (ref.cast (ref $cons) (local.get $a)))
        (call $append (struct.get $cons 1 (ref.cast (ref $cons) (local.get $a))) (local.get $b))))
      (else (local.get $b))))
  (func $strcat (param $a (ref $str)) (param $b (ref $str)) (result anyref)
    (local $r (ref $str)) (local $i i32) (local $la i32)
    (local.set $la (array.len (local.get $a)))
    (local.set $r (array.new_default $str (i32.add (local.get $la) (array.len (local.get $b)))))
    (block $d1 (loop $l1
      (br_if $d1 (i32.ge_u (local.get $i) (local.get $la)))
      (array.set $str (local.get $r) (local.get $i) (array.get_u $str (local.get $a) (local.get $i)))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $l1)))
    (local.set $i (i32.const 0))
    (block $d2 (loop $l2
      (br_if $d2 (i32.ge_u (local.get $i) (array.len (local.get $b))))
      (array.set $str (local.get $r) (i32.add (local.get $la) (local.get $i)) (array.get_u $str (local.get $b) (local.get $i)))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $l2)))
    (local.get $r))
  (func $addv (param $a anyref) (param $b anyref) (result anyref)
    (if (i32.and (ref.test (ref $str) (local.get $a)) (ref.test (ref $str) (local.get $b)))
      (then (return (call $strcat (ref.cast (ref $str) (local.get $a)) (ref.cast (ref $str) (local.get $b))))))
    (call $ofi (i32.add (call $toi (local.get $a)) (call $toi (local.get $b)))))
  (func $tof (param $v anyref) (result f64)
    (struct.get $boxf 0 (ref.cast (ref $boxf) (local.get $v))))
  (func $off (param $x f64) (result anyref) (struct.new $boxf (local.get $x)))
  (func $tos (param $v anyref) (result f32)
    (struct.get $boxs 0 (ref.cast (ref $boxs) (local.get $v))))
  (func $oss (param $x f32) (result anyref) (struct.new $boxs (local.get $x)))
  (func $tol (param $v anyref) (result i64)
    (if (result i64) (ref.test (ref i31) (local.get $v))
      (then (i64.extend_i32_s (i31.get_s (ref.cast (ref i31) (local.get $v)))))
      (else (struct.get $boxl 0 (ref.cast (ref $boxl) (local.get $v))))))
  (func $ofl (param $n i64) (result anyref)
    (if (result anyref)
        (i64.eq (local.get $n)
                (i64.shr_s (i64.shl (local.get $n) (i64.const 33)) (i64.const 33)))
      (then (ref.i31 (i32.wrap_i64 (local.get $n))))
      (else (struct.new $boxl (local.get $n)))))
  (func $printl (param $n i64)
    (local $m i64)
    (if (i64.lt_s (local.get $n) (i64.const 0))
      (then (call $putc (i32.const 45))
            (local.set $n (i64.sub (i64.const 0) (local.get $n)))))
    (local.set $m (i64.div_s (local.get $n) (i64.const 10)))
    (if (i64.gt_s (local.get $m) (i64.const 0)) (then (call $printl (local.get $m))))
    (call $putc (i32.add (i32.const 48) (i32.wrap_i64 (i64.rem_s (local.get $n) (i64.const 10))))))
  (func $printf64 (param $v f64)
    (local $ip f64) (local $frac f64) (local $k i32) (local $d i32)
    (if (f64.lt (local.get $v) (f64.const 0))
      (then (call $putc (i32.const 45))
            (local.set $v (f64.neg (local.get $v)))))
    (local.set $ip (f64.floor (local.get $v)))
    (call $printl (i64.trunc_f64_s (local.get $ip)))
    (local.set $frac (f64.sub (local.get $v) (local.get $ip)))
    (if (f64.gt (local.get $frac) (f64.const 0))
      (then
        (call $putc (i32.const 46))
        (block $done
          (loop $go
            (br_if $done (i32.ge_s (local.get $k) (i32.const 15)))
            (local.set $frac (f64.mul (local.get $frac) (f64.const 10)))
            (local.set $d (i32.trunc_f64_s (f64.floor (local.get $frac))))
            (call $putc (i32.add (i32.const 48) (local.get $d)))
            (local.set $frac (f64.sub (local.get $frac) (f64.floor (local.get $frac))))
            (br_if $done (f64.eq (local.get $frac) (f64.const 0)))
            (local.set $k (i32.add (local.get $k) (i32.const 1)))
            (br $go))))))
  (func $ofi (param $n i32) (result anyref)
    (if (result anyref) (i32.eq (local.get $n) (i32.shr_s (i32.shl (local.get $n) (i32.const 1)) (i32.const 1)))
      (then (ref.i31 (local.get $n)))
      (else (struct.new $boxi (local.get $n)))))
  (func $toi (param $v anyref) (result i32)
    (if (result i32) (ref.test (ref i31) (local.get $v))
      (then (i31.get_s (ref.cast (ref i31) (local.get $v))))
      (else (struct.get $boxi 0 (ref.cast (ref $boxi) (local.get $v))))))
  (func $applyc (param $f anyref) (param $a anyref) (result anyref)
    (call_ref $u1 (local.get $a)
      (struct.get $clo 1 (ref.cast (ref $clo) (local.get $f)))
      (struct.get $clo 0 (ref.cast (ref $clo) (local.get $f)))))"""

    // top-level functions and value initializers
    let initFuncs = vecNew<string> ()
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, body)) ->
            let fname = (dictTryFind topName (v.Path, v.Offset)).Value
            let pks, rk =
                match dictTryFind sigKinds (v.Path, v.Offset) with
                | Some (pk, r) -> pk, r
                | None -> List.replicate ps.Length "u", "u"
            let locals = dictNew<string * int, string> ()
            ps |> List.iteri (fun i (pv, _) ->
                dictSet locals (pv.Path, pv.Offset) ("$a" + string i)
                dictSet localKinds (pv.Path, pv.Offset) (List.item i pks))
            let extra = vecNew<string * string> ()
            let bodyRaw = compileExpr locals extra (dictNew ()) (rk = "u") body
            let bodyW = if rk = "u" then bodyRaw else unboxK rk bodyRaw
            let ps' =
                ps |> List.mapi (fun i _ -> "(param $a" + string i + " " + wasmTyOf (List.item i pks) + ")")
                |> String.concat " "
            let resTy = wasmTyOf rk
            let localDecls = vecToList extra |> List.map (fun (l, ty) -> "(local " + l + " " + ty + ")") |> String.concat " "
            line ("  (func " + fname + " " + ps' + " (result " + resTy + ") " + localDecls + " " + bodyW + ")")
        | DLet (_, v, _, rhs) ->
            let gname = (dictTryFind topName (v.Path, v.Offset)).Value
            line ("  (global " + gname + " (mut anyref) (ref.null any))")
            let locals = dictNew<string * int, string> ()
            let extra = vecNew<string * string> ()
            let w = compileExpr locals extra (dictNew ()) false rhs
            let localDecls = vecToList extra |> List.map (fun (l, ty) -> "(local " + l + " " + ty + ")") |> String.concat " "
            let initName = "$init" + string (vecLen initFuncs)
            line ("  (func " + initName + " " + localDecls + " (global.set " + gname + " " + w + "))")
            vecAdd initFuncs initName
        | _ -> ()

    // curry wrappers for functions used as values / partially applied
    for fname, arity in vecToList wrappers do
        for k in 0 .. arity - 1 do
            let wk = fname + ".w" + string k
            if k = arity - 1 then
                // env holds k earlier args, latest first
                let argAt (j : int) : string =
                    // arg j (0-based) is car(cdr^(k-1-j) env)
                    let mutable w = "(local.get $env)"
                    for _ in 1 .. (k - 1 - j) do
                        w <- "(struct.get $cons 1 (ref.cast (ref $cons) " + w + "))"
                    "(struct.get $cons 0 (ref.cast (ref $cons) " + w + "))"
                let args =
                    [ for j in 0 .. arity - 1 ->
                        if j = k then "(local.get $a)" else argAt j ]
                line ("  (func " + wk + " (type $u1) (param $a anyref) (param $env anyref) (result anyref) (call " + fname + " " + String.concat " " args + "))")
            else
                line ("  (func " + wk + " (type $u1) (param $a anyref) (param $env anyref) (result anyref) (struct.new $clo (ref.func " + fname + ".w" + string (k + 1) + ") (struct.new $cons (local.get $a) (local.get $env))))")

    // lifted lambdas
    for f in vecToList lifted do line ("  " + f)

    // string data segments (escape as \xx hex where needed)
    let hexEscape (bytes : byte[]) : string =
        let out = System.Text.StringBuilder()
        for b in bytes do
            let c = char b
            if b >= 32uy && b < 127uy && c <> '"' && c <> '\\' then out.Append c |> ignore
            else out.Append("\\" + (sprintf "%02x" b)) |> ignore
        out.ToString()
    vecToList strings
    |> List.iteri (fun i sdata ->
        line ("  (data $d" + string i + " \"" + hexEscape (System.Text.Encoding.UTF8.GetBytes sdata) + "\")"))

    // string accessors for host glue (JS reads/builds $str through these)
    line """  (func (export "str_len") (param $s anyref) (result i32)
    (array.len (ref.cast (ref $str) (local.get $s))))
  (func (export "str_get") (param $s anyref) (param $i i32) (result i32)
    (array.get_u $str (ref.cast (ref $str) (local.get $s)) (local.get $i)))
  (func (export "str_new") (param $n i32) (result anyref)
    (array.new_default $str (local.get $n)))
  (func (export "str_set") (param $s anyref) (param $i i32) (param $b i32)
    (array.set $str (ref.cast (ref $str) (local.get $s)) (local.get $i) (local.get $b)))"""

    // declare every function that appears in ref.func
    let declared = vecNew<string> ()
    for f, arity in vecToList wrappers do
        for k in 0 .. arity - 1 do vecAdd declared (f + ".w" + string k)
    for i in 1 .. liftCount do vecAdd declared ("$lam" + string i)
    if vecLen declared > 0 then
        line ("  (elem declare func " + String.concat " " (vecToList declared) + ")")

    // entry point: run initializers in declaration order
    let calls = vecToList initFuncs |> List.map (fun f -> "(call " + f + ")") |> String.concat " "
    line ("  (func $_start (export \"_start\") " + calls + ")")
    line ")"

    // ---- peephole: cancel box/unbox round-trips ((call $tof (call $off X)) -> X etc.)
    let peephole (text : string) : string =
        let pairs =
            [ "(call $tof ", "(call $off "
              "(call $off ", "(call $tof "
              "(call $tos ", "(call $oss "
              "(call $oss ", "(call $tos "
              "(call $tol ", "(call $ofl "
              "(call $ofl ", "(call $tol "
              "(call $toi ", "(call $ofi "
              "(call $ofi ", "(call $toi " ]
        let mutable t = text
        let mutable changed = true
        while changed do
            changed <- false
            for outer, inner in pairs do
                let pat = outer + inner
                let mutable idx = t.IndexOf pat
                while idx >= 0 do
                    // inner sexp starts right after `outer`
                    let innerStart = idx + outer.Length
                    let mutable depth = 0
                    let mutable j = innerStart
                    let mutable innerEnd = -1
                    while innerEnd < 0 && j < t.Length do
                        if t.[j] = '(' then depth <- depth + 1
                        elif t.[j] = ')' then
                            depth <- depth - 1
                            if depth = 0 then innerEnd <- j
                        j <- j + 1
                    // outer must close immediately after inner
                    if innerEnd > 0 && innerEnd + 1 < t.Length && t.[innerEnd + 1] = ')' then
                        let arg = t.Substring (innerStart + inner.Length, innerEnd - (innerStart + inner.Length))
                        t <- t.Substring (0, idx) + arg + t.Substring (innerEnd + 2)
                        changed <- true
                        idx <- t.IndexOf pat
                    else
                        idx <- t.IndexOf (pat, idx + 1)
        t

    { Wat = peephole (sb.ToString ()); Errors = vecToList errors }
