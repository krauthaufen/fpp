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
    for un, cs in unions do
        for cn, a in cs do
            dictSet caseArity cn a
            dictSet caseOwner cn un

    let topArity = dictNew<string * int, int> ()   // (path,offset) -> arity of top-level fn
    let topName = dictNew<string * int, string> ()
    let mangle (v : VarId) = "$g" + string (abs (hash v.Path % 1000)) + "_" + string v.Offset + "_" + (v.Name |> String.map (fun c -> if System.Char.IsLetterOrDigit c then c else '_'))
    // extern signatures: param/result kinds derived from the scheme.
    // "i" = int (i32 ABI, wrapped), "r" = reference/other (opaque anyref)
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
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, _)) ->
            dictSet topArity (v.Path, v.Offset) ps.Length
            dictSet topName (v.Path, v.Offset) (mangle v)
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

    /// Compile one function body. `locals` maps (path,offset) to wasm local
    /// names; `extraLocals` collects locals to declare.
    let rec compileExpr (locals : Dict<string * int, string>) (extraLocals : Vec<string>)
                        (freeEnv : Dict<string * int, int>) (tail : bool) (e : Expr) : string =
        let recur = compileExpr locals extraLocals freeEnv false
        let recurT = compileExpr locals extraLocals freeEnv tail
        let newLocal (base_ : string) : string =
            let n = "$l" + string (vecLen extraLocals) + "_" + base_
            vecAdd extraLocals n
            n
        match e with
        | ELit (LInt s) ->
            let digits = s |> String.filter (fun c -> isDigit c || c = '-')
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
             | Some l -> "(local.get " + l + ")"
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
        | EApp (EUnknown "print", [ a ]) ->
            "(block (result anyref) (call $printval " + recur a + ") (call $putc (i32.const 10)) (ref.i31 (i32.const 0)))"
        | EApp (EUnknown "ignore", [ a ]) ->
            "(block (result anyref) (drop " + recur a + ") (ref.i31 (i32.const 0)))"
        | EApp (EUnknown "failwith", [ a ]) ->
            (match dictTryFind caseArity "Failure" with
             | Some _ -> "(block (result anyref) (throw $fppexn (struct.new $u_Failure " + recur a + ")) (ref.i31 (i32.const 0)))"
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
            "(" + op + " " + fname + " " + String.concat " " (List.map recur args) + ")")
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
            let l = newLocal (v.Name |> String.map (fun c -> if System.Char.IsLetterOrDigit c then c else '_'))
            let r = recur rhs
            dictSet locals (v.Path, v.Offset) l
            "(block (result anyref) (local.set " + l + " " + r + ") " + recurT body + ")"
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
                 "(struct.new $u_" + name + " " + String.concat " " (List.map recur args) + ")"
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
             | Some l -> "(block (result anyref) (local.set " + l + " " + recur e + ") (ref.i31 (i32.const 0)))"
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
        | EArrayLen (nm, a) ->
            let pk = primKindOf nm
            if nm = "string" then
                "(call $ofi (array.len (ref.cast (ref $str) " + recur a + ")))"
            elif pk <> "" then
                "(call $ofi (array.len (ref.cast (ref " + parrOf pk + ") " + recur a + ")))"
            elif isStructName nm then
                "(call $ofi (array.len (struct.get $sarr_" + nm + " 0 (ref.cast (ref $sarr_" + nm + ") " + recur a + "))))"
            else
                vecAdd errors "length needs a statically known element type"
                "(ref.i31 (i32.const 0))"
        | EArrayCreate (nm, n, v) ->
            let pk = primKindOf nm
            if pk <> "" then
                "(array.new " + parrOf pk + " (call " + unboxOfKind pk + " " + recur v + ") " + unwrapI32 (recur n) + ")"
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
            vecAdd extraLocals n
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
            let digits = s |> String.filter (fun c -> isDigit c || c = '-')
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
             | Some 0 -> app ("(br_if " + failLbl + " (i32.eqz (ref.test (ref $u_" + name + ") " + v + ")))")
             | Some _ ->
                 app ("(br_if " + failLbl + " (i32.eqz (ref.test (ref $u_" + name + ") " + v + ")))")
                 args |> List.iteri (fun i a ->
                     let field = "(struct.get $u_" + name + " " + string i + " (ref.cast (ref $u_" + name + ") " + v + "))"
                     compilePat locals extraLocals freeEnv out failLbl field a)
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
        let innerExtra = vecNew<string> ()
        let bodyW = compileExpr innerLocals innerExtra innerFree true body
        let localDecls = vecToList innerExtra |> List.map (fun l -> "(local " + l + " anyref)") |> String.concat " "
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
    line "  (memory (export \"memory\") 1)"
    line "  (tag $fppexn (param anyref))"

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
        let fa (k : string) =
            match k with
            | "f" | "s" | "l" | "i" -> "(field (ref " + parrOf k + "))"
            | _ -> "(field (ref $arr))"
        line ("  (type $sarr_" + rn + " (struct " + (fs |> List.map (fun (_, k) -> fa k) |> String.concat " ") + "))")
    for _, cs in unions do
        for cn, a in cs do
            let fields = List.replicate (max a 0) "(field anyref)" |> String.concat " "
            line ("  (type $u_" + cn + " (struct " + fields + "))")
    for n in vecToList tupleArities do
        let fields = List.replicate n "(field anyref)" |> String.concat " "
        line ("  (type $tup" + string n + " (struct " + fields + "))")

    // nullary case singletons
    for _, cs in unions do
        for cn, a in cs do
            if a = 0 then
                line ("  (global $c_" + cn + " (ref $u_" + cn + ") (struct.new $u_" + cn + "))")

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
            let locals = dictNew<string * int, string> ()
            ps |> List.iteri (fun i (pv, _) -> dictSet locals (pv.Path, pv.Offset) ("$a" + string i))
            let extra = vecNew<string> ()
            let bodyW = compileExpr locals extra (dictNew ()) true body
            let ps' = ps |> List.mapi (fun i _ -> "(param $a" + string i + " anyref)") |> String.concat " "
            let localDecls = vecToList extra |> List.map (fun l -> "(local " + l + " anyref)") |> String.concat " "
            line ("  (func " + fname + " " + ps' + " (result anyref) " + localDecls + " " + bodyW + ")")
        | DLet (_, v, _, rhs) ->
            let gname = (dictTryFind topName (v.Path, v.Offset)).Value
            line ("  (global " + gname + " (mut anyref) (ref.null any))")
            let locals = dictNew<string * int, string> ()
            let extra = vecNew<string> ()
            let w = compileExpr locals extra (dictNew ()) false rhs
            let localDecls = vecToList extra |> List.map (fun l -> "(local " + l + " anyref)") |> String.concat " "
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

    { Wat = sb.ToString (); Errors = vecToList errors }
