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
    let records = decls |> List.choose (fun d -> match d with DRecord (n, _, fs) -> Some (n, fs) | _ -> None)

    // field name -> (record, index); F# shadowing: last declaration wins
    let fieldIndex = dictNew<string, string * int> ()
    for rn, fs in records do
        fs |> List.iteri (fun i f -> dictSet fieldIndex f (rn, i))
    let recordArity = dictNew<string, int> ()
    for rn, fs in records do dictSet recordArity rn fs.Length
    let recordOrder = dictNew<string, string list> ()
    for rn, fs in records do dictSet recordOrder rn fs

    let caseArity = dictNew<string, int> ()
    let caseOwner = dictNew<string, string> ()
    for un, cs in unions do
        for cn, a in cs do
            dictSet caseArity cn a
            dictSet caseOwner cn un

    let topArity = dictNew<string * int, int> ()   // (path,offset) -> arity of top-level fn
    let topName = dictNew<string * int, string> ()
    let mangle (v : VarId) = "$g" + string (abs (hash v.Path % 1000)) + "_" + string v.Offset + "_" + (v.Name |> String.map (fun c -> if System.Char.IsLetterOrDigit c then c else '_'))
    let externs = dictNew<string * int, int> ()   // key -> arity
    let rec arrowArity (t : Fpp.Analysis.Types.Type) : int =
        match Fpp.Analysis.Types.prune t with
        | Fpp.Analysis.Types.TFun (_, b) -> 1 + arrowArity b
        | _ -> 0
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
            dictSet externs (v.Path, v.Offset) ar
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
            let v = if digits = "" then 0 else int digits
            "(call $ofi (i32.const " + string v + "))"
        | ELit (LBool b) -> "(ref.i31 (i32.const " + (if b then "1" else "0") + "))"
        | ELit LUnit -> "(ref.i31 (i32.const 0))"
        | ELit (LChar raw) -> "(ref.i31 (i32.const " + string (charCode raw) + "))"
        | ELit (LFloat s) -> "(struct.new $boxf (f64.const " + (s |> String.filter (fun c -> isDigit c || c = '.' || c = '-' || c = 'e')) + "))"
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
        | EApp (EUnknown "print", [ a ]) ->
            "(block (result anyref) (call $printval " + recur a + ") (call $putc (i32.const 10)) (ref.i31 (i32.const 0)))"
        | EApp (EUnknown "ignore", [ a ]) ->
            "(block (result anyref) (drop " + recur a + ") (ref.i31 (i32.const 0)))"
        | EApp (EUnknown "failwith", [ _ ]) -> "(unreachable)"
        | EApp (EVar (v, _), args) when (dictTryFind topArity (v.Path, v.Offset)) = Some args.Length ->
            // known full-arity call: direct (tail position -> return_call)
            let fname = (dictTryFind topName (v.Path, v.Offset)).Value
            if (dictTryFind externs (v.Path, v.Offset)).IsSome then
                // C-ABI boundary: unwrap ints in, wrap the i32 result out
                "(call $ofi (call " + fname + " "
                + String.concat " " (args |> List.map (fun a -> unwrapI32 (recur a))) + "))"
            else
            let op = if tail then "return_call" else "call"
            "(" + op + " " + fname + " " + String.concat " " (List.map recur args) + ")"
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
             | Some (rn, _) ->
                 let order = (dictTryFind recordOrder rn).Value
                 let vals =
                     order
                     |> List.map (fun fname ->
                         match fields |> List.tryFind (fun (f, _) -> f = fname) with
                         | Some (_, v) -> recur v
                         | None ->
                             vecAdd errors ("missing field " + fname + " in " + rn)
                             "(ref.i31 (i32.const 0))")
                 "(struct.new $r_" + rn + " " + String.concat " " vals + ")"
             | None ->
                 vecAdd errors "record with unknown type"
                 "(ref.i31 (i32.const 0))")
        | EField (r, fname) ->
            (match dictTryFind fieldIndex fname with
             | Some (rn, idx) ->
                 "(struct.get $r_" + rn + " " + string idx + " (ref.cast (ref $r_" + rn + ") " + recur r + "))"
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
    line "  (import \"wasi_snapshot_preview1\" \"fd_write\" (func $fd_write (param i32 i32 i32 i32) (result i32)))"
    for d in decls do
        match d with
        | DExtern (v, sch) ->
            let ar = arrowArity sch.Body
            let ps = List.replicate ar "(param i32)" |> String.concat " "
            line ("  (import \"env\" \"" + v.Name + "\" (func " + mangle v + " " + ps + " (result i32)))")
        | _ -> ()
    line "  (memory (export \"memory\") 1)"

    // program-declared types
    for rn, fs in records do
        let fields = fs |> List.map (fun _ -> "(field anyref)") |> String.concat " "
        line ("  (type $r_" + rn + " (struct " + fields + "))")
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
    (if (ref.test (ref $boxf) (local.get $v))
      (then (call $printi (i32.trunc_f64_s (struct.get $boxf 0 (ref.cast (ref $boxf) (local.get $v))))) (return)))
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
