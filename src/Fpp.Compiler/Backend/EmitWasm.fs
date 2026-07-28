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
    // which top-level function is being emitted, so errors can say WHERE
    let mutable currentFn = ""
    let emitError (msg : string) =
        vecAdd errors (if currentFn = "" then msg else msg + " [in " + currentFn + "]")
    let sb = System.Text.StringBuilder()
    let line (s : string) = sb.AppendLine s |> ignore

    // ---- program shape ----------------------------------------------------

    let unions = decls |> List.choose (fun d -> match d with DUnion (n, _, cs) -> Some (n, cs) | _ -> None)
    // ---- object model -----------------------------------------------
    // A class instance carries a hidden first field pointing at its class
    // descriptor: {classId, vtable}. That is what makes interface dispatch
    // and checked downcasts possible without knowing the concrete type.
    let classDecls = decls |> List.choose (fun d -> match d with DClass (n, b, own, impls) -> Some (n, b, own, impls) | _ -> None)
    let classImpls = classDecls |> List.map (fun (n, _, _, impls) -> n, impls)
    let isClassName (n : string) = classDecls |> List.exists (fun (cn, _, _, _) -> cn = n)
    let classId (n : string) = classDecls |> List.findIndex (fun (cn, _, _, _) -> cn = n)
    let baseOf (n : string) = classDecls |> List.tryPick (fun (cn, b, _, _) -> if cn = n then b else None)
    let ownMembersOf (n : string) = classDecls |> List.tryPick (fun (cn, _, own, _) -> if cn = n then Some own else None)
    /// a class and every ancestor, nearest first
    let rec chainOf (n : string) : string list =
        match baseOf n with
        | Some b when b <> n -> n :: chainOf b
        | _ -> [ n ]
    /// every class that is `n` or derives from it — what a downcast accepts
    let subclassesOf (n : string) =
        // a plain record has no hierarchy: it is only itself
        let derived =
            classDecls |> List.filter (fun (cn, _, _, _) -> List.contains n (chainOf cn)) |> List.map (fun (cn, _, _, _) -> cn)
        if List.isEmpty derived then [ n ] else derived
    let interfaceDecls = decls |> List.choose (fun d -> match d with DInterface (n, ms) -> Some (n, ms) | _ -> None)
    // one global slot per (interface, method), so every vtable agrees
    let vtableSlots =
        ((interfaceDecls |> List.collect (fun (i, ms) -> ms |> List.map (fun (m, _) -> i, m)))
         @ (classImpls |> List.collect (fun (_, impls) -> impls |> List.collect (fun (i, ms) -> ms |> List.map (fun (m, _) -> i, m)))))
        |> List.distinct
        |> List.sort
    /// The function filling slot (owner, method) for class `cn`: the nearest
    /// definition walking up its chain — an override shadows what it overrides.
    let slotImpl (cn : string) (owner : string) (m : string) : VarId option =
        let fromIface =
            chainOf cn
            |> List.tryPick (fun c ->
                classDecls
                |> List.tryPick (fun (n2, _, _, impls) ->
                    if n2 <> c then None
                    else impls |> List.tryPick (fun (i, ms) -> if i = owner then ms |> List.tryPick (fun (mm, v) -> if mm = m then Some v else None) else None)))
        match fromIface with
        | Some v -> Some v
        | None ->
            // a virtual method declared on a base class: nearest override wins
            if List.contains owner (chainOf cn) then
                chainOf cn
                |> List.tryPick (fun c ->
                    ownMembersOf c |> Option.bind (fun own -> own |> List.tryPick (fun (mm, v) -> if mm = m then Some v else None)))
            else None
    /// Slots 0 and 1 of every vtable are equals and hash. The contract is
    /// total, so every reference type fills them; interface methods follow.
    let identitySlots = 2
    let slotOf (iface : string) (m : string) =
        vtableSlots |> List.tryFindIndex (fun (i, mm) -> i = iface && mm = m)
        |> Option.map (fun i -> i + identitySlots)
    // functions reachable through a vtable keep the canonical all-anyref
    // signature — that IS the dispatch contract, so no specialization
    /// The function filling an identity slot: a user override if the type
    /// declares one, otherwise the generated function.
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
    let ifaceImplKeys =
        (classImpls |> List.collect (fun (_, impls) -> impls |> List.collect (fun (_, ms) -> ms |> List.map (fun (_, v) -> v.Path, v.Offset))))
        @ (classDecls
           |> List.collect (fun (cn, _, _, _) ->
                vtableSlots |> List.choose (fun (i, m) -> slotImpl cn i m |> Option.map (fun v -> v.Path, v.Offset))))
        // an identity override is reached through a vtable too, so it keeps
        // the canonical all-anyref signature
        @ (declaredMembers
           |> List.collect (fun (_, own) ->
                own |> List.choose (fun (m, v) -> if m = "Equals" || m = "GetHashCode" then Some (v.Path, v.Offset) else None)))
    let isIfaceImpl (key : string * int) = List.contains key ifaceImplKeys

    let rawRecords = decls |> List.choose (fun d -> match d with DRecord (n, _, fs, st) -> Some (n, fs, st) | _ -> None)
    // prefix layout: a derived class starts with exactly its base's fields,
    // which is what makes an upcast free and a base method work unchanged
    let rec expandedFields (n : string) : (string * string) list =
        match rawRecords |> List.tryPick (fun (rn, fs, _) -> if rn = n then Some fs else None) with
        | None -> []
        | Some fs ->
            match baseOf n with
            | Some b when b <> n -> expandedFields b @ fs
            | _ -> fs
    // EVERY reference type carries a descriptor: it is what lets equality,
    // hashing and casts work on a value whose type is not statically known.
    // Value types never need one — they are known statically.
    let isObjRecord (n : string) =
        rawRecords |> List.exists (fun (rn, _, st) -> rn = n && not st)
    let objRecordNames = rawRecords |> List.filter (fun (_, _, st) -> not st) |> List.map (fun (n, _, _) -> n)
    let descId (n : string) = objRecordNames |> List.findIndex (fun rn -> rn = n)
    let records =
        rawRecords
        |> List.map (fun (n, fs, st) ->
            if st then n, fs, st
            // a class is reference-equal, so it needs a per-OBJECT identity
            // number; a record is structural and never does
            elif isClassName n then n, ("__desc", "r") :: ("__idhash", "int") :: expandedFields n, st
            else n, ("__desc", "r") :: fs, st)

    // A field declaration carries a TYPE; the representation is derived
    // here, once, from that type. A struct stores its fields unboxed where
    // the type allows; a reference type keeps everything uniform.
    let kindOfType (structNamesOf : string list) (tyName : string) : string =
        match tyName with
        | "float" -> "f"
        | "float32" -> "s"
        | "int64" -> "l"
        // a half is carried as its bit pattern, so it stores like an int
        | "int" | "bool" | "char" | "float16" -> "i"
        | n when List.contains n structNamesOf -> "S:" + n
        | _ -> "r"
    let mutable structNameList : string list = []
    let kindOfField (isStruct : bool) (k : string) =
        if isStruct then kindOfType structNameList k else "r"
    /// as above, but the synthetic identity word is a raw i32
    let fieldKindOf (isStruct : bool) (fname : string) (k : string) =
        if fname = "__idhash" then "i" else kindOfField isStruct k
    // flat-array element classification: primitive kind or a struct name
    let primKindOf (tyName : string) : string =
        match tyName with
        | "int" | "bool" | "char" -> "i"
        // an ARRAY of halves is packed: wasm-GC has i16 element storage,
        // and 2 bytes per element is the reason the type exists. (A half
        // FIELD still stores as i32 — packing it would touch every
        // struct.get site for a per-field saving that does not matter.)
        | "float16" -> "h"
        | "float" -> "f"
        | "float32" -> "s"
        | "int64" -> "l"
        | _ -> ""
    // struct layout works in representations, so convert the declared field
    // types to kinds once, here at the boundary
    let structRecordsDecl = decls |> List.choose (fun d -> match d with DRecord (n, _, fs, true) -> Some (n, fs) | _ -> None)
    structNameList <- structRecordsDecl |> List.map fst
    let structRecords =
        structRecordsDecl
        |> List.map (fun (n, fs) -> n, fs |> List.map (fun (f, t) -> f, kindOfType structNameList t))
    let isStructName (n : string) = structRecords |> List.exists (fun (rn, _) -> rn = n)
    let parrOf (k : string) = "$parr_" + k
    // ---- C ABI layout for POD structs (clang natural alignment) ----------
    // fields: (name, kind, byteOffset); sizeof rounded to max align;
    // storage = shared GC (array (mut i64)), strideWords per element
    // C layout, recursive: nested struct fields (kind "S:Name") inline at
    // their C offsets; `placed` lists LEAVES with dotted paths
    let podLayout = dictNew<string, (string * string * int) list * int * int> ()
    let structKindName (k : string) = if k.StartsWith "S:" then k.Substring 2 else ""
    let scalarSize (k : string) = if k = "i" || k = "s" then 4 else 8
    let rec computeLayout (rn : string) : bool =
        if (dictTryFind podLayout rn).IsSome then true
        else
            match structRecords |> List.tryFind (fun (n, _) -> n = rn) with
            | None -> false
            | Some (_, fs) ->
                // nested structs must resolve first
                let ok =
                    fs |> List.forall (fun (_, k) ->
                        if k = "i" || k = "f" || k = "s" || k = "l" then true
                        else
                            let sn = structKindName k
                            sn <> "" && sn <> rn && computeLayout sn)
                if not ok then false
                else
                    let mutable off = 0
                    let mutable maxA = 1
                    let leaves = vecNew<string * string * int> ()
                    for fn, k in fs do
                        if k = "i" || k = "f" || k = "s" || k = "l" then
                            let sz = scalarSize k
                            off <- ((off + sz - 1) / sz) * sz
                            vecAdd leaves (fn, k, off)
                            off <- off + sz
                            if sz > maxA then maxA <- sz
                        else
                            let sn = structKindName k
                            let nl, nsz, _ = (dictTryFind podLayout sn).Value
                            let na = nl |> List.map (fun (_, k2, _) -> scalarSize k2) |> List.max
                            off <- ((off + na - 1) / na) * na
                            for np, nk, noff in nl do
                                vecAdd leaves (fn + "." + np, nk, off + noff)
                            off <- off + nsz
                            if na > maxA then maxA <- na
                    let sizeof_ = ((off + maxA - 1) / maxA) * maxA
                    dictSet podLayout rn (vecToList leaves, sizeof_, (sizeof_ + 7) / 8)
                    true
    for rn, _ in structRecords do computeLayout rn |> ignore
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
    /// read a dotted leaf path out of a GC struct expression
    let rec leafGet (rn : string) (structExpr : string) (path : string) : string =
        let i = path.IndexOf '.'
        let head = if i < 0 then path else path.Substring (0, i)
        let fs = structRecords |> List.pick (fun (n, f) -> if n = rn then Some f else None)
        let idx = fs |> List.findIndex (fun (fn, _) -> fn = head)
        let _, k = fs |> List.item idx
        let get = "(struct.get $r_" + rn + " " + string idx + " (ref.cast (ref $r_" + rn + ") " + structExpr + "))"
        if i < 0 then get
        else leafGet (structKindName k) get (path.Substring (i + 1))

    /// build a struct value of `rn` from leaf expressions (by dotted path)
    let rec structFromLeaves (rn : string) (leafOf : string -> string) (prefix : string) : string =
        let fs = structRecords |> List.pick (fun (n, f) -> if n = rn then Some f else None)
        let parts =
            fs |> List.map (fun (fn, k) ->
                let full = if prefix = "" then fn else prefix + "." + fn
                if k.StartsWith "S:" then structFromLeaves (structKindName k) leafOf full
                else leafOf full)
        "(struct.new $r_" + rn + " " + String.concat " " parts + ")"

    /// i64 word w built from a struct value in local `vl`
    let wordFromStruct (rn : string) (vl : string) (w : int) : string =
        let placed, _, _ = (dictTryFind podLayout rn).Value
        let parts =
            placed
            |> List.filter (fun (_, _, off) -> off / 8 = w)
            |> List.map (fun (fn, k, off) ->
                let fv = leafGet rn ("(local.get " + vl + ")") fn
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
        fs |> List.iteri (fun i (f, k) -> dictSet fieldIndex f (rn, i, fieldKindOf st f k))
    /// Field slot lookup. With a known owner the record is exact; without
    /// one we fall back to the bare name (F# shadowing: last declaration
    /// wins), which is what unowned core from plugins/tests carries.
    let fieldSlot (owner : string) (fname : string) : (string * int * string) option =
        let byOwner =
            if owner = "" then None
            else
                records
                |> List.tryPick (fun (rn, fs, st) ->
                    if rn <> owner then None
                    else
                        fs |> List.mapi (fun i (f, k) -> f, i, k)
                           |> List.tryPick (fun (f, i, k) ->
                                if f = fname then Some (rn, i, fieldKindOf st f k) else None))
        match byOwner with
        | Some x -> Some x
        | None -> dictTryFind fieldIndex fname
    let recordOrder = dictNew<string, (string * string) list> ()
    for rn, fs, st in records do
        dictSet recordOrder rn (fs |> List.map (fun (f, k) -> f, fieldKindOf st f k))

    // enum cases are integer constants, never allocated cases
    let enumConst = dictNew<string, int> ()
    for d in decls do
        match d with
        | DEnum (_, cs) -> for c, v in cs do dictSet enumConst c v
        | _ -> ()
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
    // POD-struct positions in a signature: (paramStructs, resultStruct)
    let sigStructs = dictNew<string * int, string option list * string option> ()
    let structNameOfTy (t : Fpp.Analysis.Types.Type) : string option =
        match Fpp.Analysis.Types.prune t with
        | Fpp.Analysis.Types.TCon (n, []) -> (if isPod n then Some n else None)
        | _ -> None
    let rec splitArrowTys (n : int) (t : Fpp.Analysis.Types.Type) =
        if n = 0 then [], t
        else
            match Fpp.Analysis.Types.prune t with
            | Fpp.Analysis.Types.TFun (a, b) ->
                let ps, r = splitArrowTys (n - 1) b
                a :: ps, r
            | other -> [], other
    let leavesOf (rn : string) =
        let placed, _, _ = (dictTryFind podLayout rn).Value
        placed
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
            if not (isIfaceImpl (v.Path, v.Offset))
               && pk.Length = ps.Length && (rk <> "u" || List.exists (fun k -> k <> "u") pk) then
                dictSet sigKinds (v.Path, v.Offset) (pk, rk)
            let ptys, rty = splitArrowTys ps.Length sch.Body
            if not (isIfaceImpl (v.Path, v.Offset)) && ptys.Length = ps.Length then
                let pss = ptys |> List.map structNameOfTy
                let rs = structNameOfTy rty
                if List.exists Option.isSome pss || rs.IsSome then
                    dictSet sigStructs (v.Path, v.Offset) (pss, rs)
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
        | EVarI (_, _, _) -> ()
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
        | EField (r, _, _) -> scanExpr r
        | EFieldSet (r, _, _, v) -> scanExpr r; scanExpr v
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

    // single-payload constructors used as first-class functions
    let ctorAsFn = vecNew<string> ()

    // Mutable locals that a closure captures. Capture copies the environment
    // BY VALUE, so a mutable the closure writes to has to be a shared box:
    // the local holds a one-field cell, reads dereference it, and the copy
    // that lands in the closure's env is a copy of the reference.
    let cellVars = dictNew<string * int, bool> ()
    let cellRead (w : string) = "(struct.get $cell 0 (ref.cast (ref $cell) " + w + "))"

    // A local becomes a cell when it is let-bound, assigned somewhere, and
    // mentioned inside a lambda. The test is per BINDING, so every read and
    // write of it agrees on the representation; a variable bound inside the
    // lambda that mentions it costs one needless allocation and nothing else.
    let cellScan () =
        let letBound = dictNew<string * int, bool> ()
        let assigned = dictNew<string * int, bool> ()
        let inLambda = dictNew<string * int, bool> ()
        let rec go (depth : int) (e : Expr) =
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
            | EApp (f, args) -> g f; List.iter g args
            | EIf (a, b, c) -> g a; g b; g c
            | EMatch (s, cs) ->
                g s
                for _, gd, b in cs do
                    (match gd with Some gd -> g gd | None -> ())
                    g b
            | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) -> List.iter g xs
            | ECtor (_, _, xs) -> List.iter g xs
            | ERecord (_, fs) -> for _, v in fs do g v
            | EField (r, _, _) -> g r
            | EFieldSet (r, _, _, v) -> g r; g v
            | EWhile (c, b) -> g c; g b
            | EArray (_, xs) -> List.iter g xs
            | EIndex (_, a, i) -> g a; g i
            | EIndexSet (_, a, i, v) -> g a; g i; g v
            | EArrayLen (_, a) -> g a
            | EArrayCreate (_, n, v) -> g n; g v
            | EArrayPin (_, a) -> g a
            | EArrayUnpin (_, a) -> g a
            | ETry (b, cs) ->
                g b
                for _, gd, x in cs do
                    (match gd with Some gd -> g gd | None -> ())
                    g x
            | _ -> ()
        // a top-level function's own parameter lambdas ARE the function, not
        // a capture boundary — its body compiles into a wasm function whose
        // locals are locals
        let rec skipParams (e : Expr) =
            match e with
            | ELam (_, b) -> skipParams b
            | _ -> e
        for d in decls do
            match d with
            | DLet (_, _, _, e) -> go 0 (skipParams e)
            | _ -> ()
        for k, _ in dictPairs assigned do
            if (dictTryFind letBound k).IsSome && (dictTryFind inLambda k).IsSome then
                dictSet cellVars k true
    cellScan ()

    /// The maximal run of adjacent recursive lambda bindings at the head of
    /// `e` — what Lower emits for a `let rec f ... and g ...` group — with
    /// the body that follows them. Grouping bindings that are NOT mutually
    /// recursive is harmless: their markers are simply never captured.
    let rec recGroupOf (e : Expr) : (VarId * Expr) list * Expr =
        match e with
        | ELet (true, v, _, (ELam (_, _) as lam), rest) ->
            let ms, body = recGroupOf rest
            (v, lam) :: ms, body
        | _ -> [], e

    let boolWat (w : string) = "(ref.i31 " + w + ")"
    let unwrapI32 (w : string) = "(call $toi " + w + ")"
    let intWat (w : string) = "(call $ofi " + w + ")"

    // ---- scalar kind analysis: "f" f64, "s" f32, "l" i64, "u" uniform ----
    // (ints stay uniform: i31 immediates are allocation-free already)
    let localKinds = dictNew<string * int, string> ()
    // scalarized params: var -> (structName, leafPath -> local name)
    let paramLeaves = dictNew<string * int, string * Dict<string, string>> ()
    let suffixedOps = [ "+"; "-"; "*"; "/"; "%" ]
    let rec kindOf (e : Expr) : string =
        match e with
        | ELit (LFloat t) ->
            // a half is an i31 bit pattern, so it is uniform like an int
            if t.EndsWith "h" || t.EndsWith "H" then "u"
            elif t.EndsWith "f" || t.EndsWith "F" then "s"
            else "f"
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
        | EField (_, fname, owner) ->
            (match fieldSlot owner fname with
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
    let newTypedLocalOuter (v : Vec<string * string>) (base_ : string) (ty : string) : string =
        let n = "$x" + string (vecLen v) + "_" + base_
        vecAdd v (n, ty)
        n
    let wasmTyOf2 (k : string) =
        match k with
        | "f" -> "f64" | "s" -> "f32" | "l" -> "i64" | _ -> "i32"
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
    // Emission MEMO, per node identity and tail flag. Twenty cases in the
    // emitter mention `recur x` more than once (an operand read in several
    // branches of one instruction sequence), and each mention re-walked the
    // whole subtree — the cost multiplied through nesting, so emitting the
    // compiler's own emitter took ~110M walks and tens of GB. The
    // environment objects are the same for the whole function, so the same
    // node at the same tail position has the same text by construction.
    // keyed by REFERENCE identity (the duplicate mentions pass the very same
    // node object) — structural hashing would re-walk the tree per lookup
    // and reintroduce the cost it exists to remove. Cleared per function,
    // because `locals` is per-function state.
    // keyed by the LOCALS dictionary as well as the node: a lambda body is
    // emitted against a fresh locals map, and text produced in one
    // environment must never be reused in another
    let ceMemos =
        System.Collections.Generic.Dictionary<Dict<string * int, string>,
                                              System.Collections.Generic.Dictionary<Expr, string>
                                              * System.Collections.Generic.Dictionary<Expr, string>>
            (HashIdentity.Reference)
    let rec compileExpr (locals : Dict<string * int, string>) (extraLocals : Vec<string * string>)
                        (freeEnv : Dict<string * int, int>) (tail : bool) (e : Expr) : string =
        let plain, tailed =
            match ceMemos.TryGetValue locals with
            | true, pair -> pair
            | _ ->
                let pair =
                    System.Collections.Generic.Dictionary<Expr, string> (HashIdentity.Reference),
                    System.Collections.Generic.Dictionary<Expr, string> (HashIdentity.Reference)
                ceMemos.[locals] <- pair
                pair
        let memo = if tail then tailed else plain
        match memo.TryGetValue e with
        | true, cached -> cached
        | _ ->
            let r0 = compileExprInner locals extraLocals freeEnv tail e
            // `memo.[e] <- r0` lowers as an ARRAY index-set (F++ models no
            // dict-index form), so the seam call is what self-compiles
            memo.Add (e, r0)
            r0

    and compileExprInner (locals : Dict<string * int, string>) (extraLocals : Vec<string * string>)
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
            // an unsigned literal keeps its bit pattern: 4000000000u is the
            // i32 whose unsigned reading is that value
            let isHex = s.StartsWith "0x" || s.StartsWith "0X"
            let isUnsigned = s.EndsWith "u" || s.EndsWith "U"
            if s.EndsWith "L" then
                let digits =
                    if isHex then string (System.Convert.ToInt64 (s.Substring(2).TrimEnd ([| 'L' |]), 16))
                    else s |> String.filter (fun c -> isDigit c || c = '-')
                "(call $ofl (i64.const " + (if digits = "" then "0" else digits) + "))"
            else
                // both int and uint32 are one i32; an unsigned literal is the
                // i32 with that bit pattern
                let v =
                    if isHex then int (System.Convert.ToUInt32 (s.Substring(2).TrimEnd ([| 'u'; 'U' |]), 16))
                    else
                        let digits = s |> String.filter (fun c -> isDigit c || c = '-')
                        if digits = "" then 0
                        elif isUnsigned then int (System.UInt32.Parse digits)
                        else int digits
                "(call $ofi (i32.const " + string v + "))"
        | ELit (LBool b) -> "(ref.i31 (i32.const " + (if b then "1" else "0") + "))"
        | ELit LNull -> "(ref.null any)"
        | ELit LUnit -> "(ref.i31 (i32.const 0))"
        | ELit (LChar raw) -> "(ref.i31 (i32.const " + string (charCode raw) + "))"
        | ELit (LFloat s) ->
            // keep everything a wasm float constant may contain, and drop
            // only the F++ width suffix. `E` and `e+` were being filtered
            // out, which silently produced `1.0E5` -> `1.05`.
            let num = s |> String.filter (fun c -> isDigit c || c = '.' || c = '-' || c = '+' || c = 'e' || c = 'E')
            if s.EndsWith "h" || s.EndsWith "H" then
                // a half literal is rounded ONCE, here, and emitted as the
                // bit pattern it becomes — no runtime conversion
                let v = System.Double.Parse (num, System.Globalization.CultureInfo.InvariantCulture)
                let bits =
                    int (System.BitConverter.HalfToInt16Bits (System.Half.op_Explicit v)) &&& 0xffff
                "(ref.i31 (i32.const " + string bits + "))"
            elif s.EndsWith "f" || s.EndsWith "F" then
                "(struct.new $boxs (f32.const " + num + "))"
            else
                "(struct.new $boxf (f64.const " + num + "))"
        | ELit (LString raw) ->
            let bytes = unescape raw
            let id = internString bytes
            "(array.new_data $str $d" + string id + " (i32.const 0) (i32.const " + string (System.Text.Encoding.UTF8.GetByteCount bytes) + "))"
        | EVarI (v, sch, _) -> recur (EVar (v, sch))
        | EVar (v, _) when (dictTryFind paramLeaves (v.Path, v.Offset)).IsSome ->
            let rn, m = (dictTryFind paramLeaves (v.Path, v.Offset)).Value
            structFromLeaves rn (fun lp -> "(local.get " + (dictTryFind m lp).Value + ")") ""
        | EVar (v, _) ->
            let key = (v.Path, v.Offset)
            (match dictTryFind locals key with
             | Some l ->
                 // a captured mutable lives in a cell: the local holds the
                 // cell, and reading it is a dereference
                 if (dictTryFind cellVars key).IsSome then cellRead ("(local.get " + l + ")")
                 else
                 (match dictTryFind localKinds key with
                  | Some k when k <> "u" -> boxK k ("(local.get " + l + ")")
                  | _ -> "(local.get " + l + ")")
             | None ->
                 match dictTryFind freeEnv key with
                 | Some idx ->
                     // FLAT env: one indexed read (see the build site)
                     let slot = "(array.get $arr (ref.cast (ref $arr) (local.get $env)) (i32.const " + string idx + "))"
                     // the env slot holds the CELL, shared with the frame
                     // that owns it — that sharing is the whole point
                     if (dictTryFind cellVars key).IsSome then cellRead slot else slot
                 | None ->
                     match dictTryFind topArity key, dictTryFind topName key with
                     | Some arity, Some fname ->
                         // function as a value: curried closure chain
                         requestWrappers fname arity
                         "(struct.new $clo (ref.func " + fname + ".w0) (ref.null any))"
                     | None, Some gname ->
                         "(global.get " + gname + ")"
                     | _ ->
                         emitError ("unbound variable " + v.Name)
                         "(ref.i31 (i32.const 0))")
        | EUnknown n ->
            emitError ("unknown name reaches emission: " + n)
            "(ref.i31 (i32.const 0))"
        | EApp (EField (EUnknown "Array", "create", _), [ _; _ ]) ->
            vecAdd errors "Array.create needs a statically known element type"
            "(ref.i31 (i32.const 0))"
        | EApp (EField (EUnknown "Array", "length", _), [ a ]) ->
            "(call $lenv " + recur a + ")"
        // builtin members on `string`, registered in inference under
        // "string.X" and reaching here as $str.X (with the overload ordinal)
        | EApp (EUnknown "$str.Substring", [ s; start ]) ->
            let sw = "(ref.cast (ref $str) " + recur s + ")"
            let sl = newTypedLocal "sbs" "i32"
            "(block (result anyref) (local.set " + sl + " " + unwrapI32 (recur start) + ") "
            + "(call $strsub " + sw + " (local.get " + sl + ") "
            + "(i32.sub (array.len " + sw + ") (local.get " + sl + "))))"
        | EApp (EUnknown "$str.Substring#2", [ s; start; len ]) ->
            "(call $strsub (ref.cast (ref $str) " + recur s + ") " + unwrapI32 (recur start)
            + " " + unwrapI32 (recur len) + ")"
        | EApp (EUnknown "$str.StartsWith", [ s; p ]) ->
            boolWat ("(call $strStarts (ref.cast (ref $str) " + recur s + ") (ref.cast (ref $str) " + recur p + "))")
        | EApp (EUnknown "$str.EndsWith", [ s; p ]) ->
            boolWat ("(call $strEnds (ref.cast (ref $str) " + recur s + ") (ref.cast (ref $str) " + recur p + "))")
        | EApp (EUnknown "$str.Contains", [ s; p ]) ->
            boolWat ("(i32.ge_s (call $strFind (ref.cast (ref $str) " + recur s + ") (ref.cast (ref $str) "
                     + recur p + ") (i32.const 0)) (i32.const 0))")
        | EApp (EUnknown "$str.IndexOf", [ s; p ]) ->
            intWat ("(call $strFind (ref.cast (ref $str) " + recur s + ") (ref.cast (ref $str) "
                    + recur p + ") (i32.const 0))")
        | EApp (EUnknown "$str.IndexOf#2", [ s; c ]) ->
            intWat ("(call $strFindChar (ref.cast (ref $str) " + recur s + ") " + unwrapI32 (recur c) + ")")
        | EApp (EUnknown "$str.IndexOf#3", [ s; p; from ]) ->
            intWat ("(call $strFind (ref.cast (ref $str) " + recur s + ") (ref.cast (ref $str) "
                    + recur p + ") " + unwrapI32 (recur from) + ")")
        | EApp (EUnknown "$str.LastIndexOf", [ s; c ]) ->
            intWat ("(call $strLastFindChar (ref.cast (ref $str) " + recur s + ") " + unwrapI32 (recur c) + ")")
        | EApp (EUnknown "$str.Split", [ s; c ]) ->
            "(call $strSplitChar (ref.cast (ref $str) " + recur s + ") " + unwrapI32 (recur c) + ")"
        | EApp (EUnknown "$str.Replace", [ s; a; b ]) ->
            "(call $strReplace (ref.cast (ref $str) " + recur s + ") (ref.cast (ref $str) " + recur a
            + ") (ref.cast (ref $str) " + recur b + "))"
        | EApp (EUnknown "$str.Trim", [ s ]) ->
            "(call $strTrim (ref.cast (ref $str) " + recur s + "))"
        | EApp (EUnknown "$str.TrimEnd", [ s; cs ]) ->
            "(call $strTrimEndChars (ref.cast (ref $str) " + recur s + ") " + recur cs + ")"
        | EApp (EUnknown "strsub", [ s; start; len ]) ->
            "(call $strsub (ref.cast (ref $str) " + recur s + ") " + unwrapI32 (recur start)
            + " " + unwrapI32 (recur len) + ")"
        | EApp (EUnknown "memLoadF64", [ a ]) ->
            "(call $off (f64.load (call $toi " + recur a + ")))"
        | EApp (EUnknown "memStoreF32", [ a; v ]) ->
            // raw linear-memory store: the zero-copy bridge to JS/WebGPU
            "(block (result anyref) (f32.store (call $toi " + recur a + ") (f32.demote_f64 (call $tof " + recur v + "))) (ref.i31 (i32.const 0)))"
        | EApp (EUnknown "compare", [ a; b ]) ->
            "(call $ofi (call $cmpv " + recur a + " " + recur b + "))"
        | EApp (EUnknown "hash", [ a ]) ->
            "(call $ofi (call $hashv " + recur a + "))"
        | EApp (EUnknown "refEq", [ a; b ]) ->
            boolWat ("(ref.eq (ref.cast (ref null eq) " + recur a + ") (ref.cast (ref null eq) " + recur b + "))")
        // int/uint32 conversions: same 32-bit payload, different reading;
        // from a wider or floating type they narrow explicitly
        // conversions whose source type inference resolved
        | EApp (EUnknown pd, [ a ]) when
            (pd.StartsWith "pad0#" || pd.StartsWith "padl#" || pd.StartsWith "padr#") ->
            let width = pd.Substring 5
            let ch = if pd.StartsWith "pad0#" then "48" else "32"
            let left = if pd.StartsWith "padl#" then "1" else "0"
            "(call $strPad (ref.cast (ref $str) " + recur a + ") (i32.const " + width
            + ") (i32.const " + ch + ") (i32.const " + left + "))"
        | EApp (EUnknown n, [ a ]) when n.Contains "#" ->
            let target = n.Substring (0, n.IndexOf "#")
            let src = n.Substring (n.IndexOf "#" + 1)
            let raw =
                match src with
                | "l" -> "(call $tol " + recur a + ")"
                | "f" -> "(call $tof " + recur a + ")"
                | "s" -> "(call $tos " + recur a + ")"
                | _ -> unwrapI32 (recur a)
            (match target, src with
             | "string", "t" -> recur a
             | "string", "f" -> "(call $ftoa " + raw + ")"
             | "string", "s" -> "(call $ftoa (f64.promote_f32 " + raw + "))"
             | "string", "l" -> "(call $ltoa " + raw + ")"
             | "string", "w" -> "(call $ultoa (i64.extend_i32_u " + raw + "))"
             | "string", "h" -> "(call $ftoa (f64.promote_f32 (call $h2f " + raw + ")))"
             // .NET Boolean.ToString: "True"/"False", capital first
             | "string", "b" ->
                 "(if (result anyref) (i32.eqz " + raw + ")"
                 + " (then (array.new_fixed $str 5 (i32.const 70) (i32.const 97) (i32.const 108) (i32.const 115) (i32.const 101)))"
                 + " (else (array.new_fixed $str 4 (i32.const 84) (i32.const 114) (i32.const 117) (i32.const 101))))"
             | "string", "c" -> "(array.new $str " + raw + " (i32.const 1))"
             | "string", _ -> "(call $itoa " + raw + ")"
             // a half is its bit pattern, so every conversion goes through
             // f32 — the one format that holds every f16 value exactly
             | "float16", "h" -> recur a
             | "float16", "f" -> intWat ("(call $f2h64 " + raw + ")")
             | "float16", "s" -> intWat ("(call $f2h " + raw + ")")
             | "float16", "l" -> intWat ("(call $f2h (f32.convert_i64_s " + raw + "))")
             | "float16", _ -> intWat ("(call $f2h (f32.convert_i32_s " + raw + "))")
             | "float", "h" -> "(call $off (f64.promote_f32 (call $h2f " + raw + ")))"
             | "float32", "h" -> "(call $oss (call $h2f " + raw + "))"
             | "int64", "h" -> "(call $ofl (i64.trunc_f32_s (call $h2f " + raw + ")))"
             | _, "h" -> "(call $ofi (i32.trunc_f32_s (call $h2f " + raw + ")))"
             | "float", "f" -> recur a
             | "float", "s" -> "(call $off (f64.promote_f32 " + raw + "))"
             | "float", "l" -> "(call $off (f64.convert_i64_s " + raw + "))"
             | "float", _ -> "(call $off (f64.convert_i32_s " + raw + "))"
             | "float32", "s" -> recur a
             | "float32", "f" -> "(call $oss (f32.demote_f64 " + raw + "))"
             | "float32", "l" -> "(call $oss (f32.convert_i64_s " + raw + "))"
             | "float32", _ -> "(call $oss (f32.convert_i32_s " + raw + "))"
             | "int64", "l" -> recur a
             | "int64", ("f" | "s") -> "(call $ofl (i64.trunc_f" + (if src = "f" then "64" else "32") + "_s " + raw + "))"
             | "int64", _ -> "(call $ofl (i64.extend_i32_s " + raw + "))"
             | _, "l" -> "(call $ofi (i32.wrap_i64 " + raw + "))"
             | _, "f" -> "(call $ofi (i32.trunc_f64_s " + raw + "))"
             | _, "s" -> "(call $ofi (i32.trunc_f32_s " + raw + "))"
             | _, _ -> recur a)
        | EApp (EUnknown "int64", [ a ]) ->
            (match kindOf a with
             | "l" -> recur a
             | "f" -> "(call $ofl (i64.trunc_f64_s (call $tof " + recur a + ")))"
             | "s" -> "(call $ofl (i64.trunc_f32_s (call $tos " + recur a + ")))"
             | _ -> "(call $ofl (i64.extend_i32_s " + unwrapI32 (recur a) + "))")
        | EApp (EUnknown ("uint32" | "int"), [ a ]) ->
            (match kindOf a with
             | "f" -> "(call $ofi (i32.trunc_f64_s (call $tof " + recur a + ")))"
             | "s" -> "(call $ofi (i32.trunc_f32_s (call $tos " + recur a + ")))"
             | "l" -> "(call $ofi (i32.wrap_i64 (call $tol " + recur a + ")))"
             | _ -> recur a)
        | EApp (EUnknown "string", [ a ]) ->
            (match kindOf a with
             | "f" -> "(call $ftoa (call $tof " + recur a + "))"
             | "s" -> "(call $ftoa (f64.promote_f32 (call $tos " + recur a + ")))"
             | "l" -> "(call $ltoa (call $tol " + recur a + "))"
             | _ -> "(call $itoa " + unwrapI32 (recur a) + ")")
        | EApp (EUnknown "isNull", [ a ]) -> boolWat ("(ref.is_null " + recur a + ")")
        | EApp (EUnknown "prints", [ a ]) ->
            "(block (result anyref) (call $prints (ref.cast (ref $str) " + recur a + ")) (ref.i31 (i32.const 0)))"
        | EApp (EUnknown "showv", [ a ]) -> "(call $showv " + recur a + ")"

        | EApp (EUnknown "hexlower", [ a ]) ->
            "(call $itobase " + unwrapI32 (recur a) + " (i32.const 16) (i32.const 0))"
        | EApp (EUnknown "hexupper", [ a ]) ->
            "(call $itobase " + unwrapI32 (recur a) + " (i32.const 16) (i32.const 1))"
        | EApp (EUnknown "octal", [ a ]) ->
            "(call $itobase " + unwrapI32 (recur a) + " (i32.const 8) (i32.const 0))"
        | EApp (EUnknown fn, [ a ]) when fn = "hexlower64" || fn = "hexupper64" || fn = "octal64" ->
            let base_ = if fn = "octal64" then "8" else "16"
            let upper = if fn = "hexupper64" then "1" else "0"
            "(call $ltobase (call $tol " + recur a + ") (i64.const " + base_ + ") (i32.const " + upper + "))"
        | EApp (EUnknown "fixed6", [ a ]) ->
            "(call $ftoa6 (call $tof " + recur a + "))"
        | EApp (EUnknown "printb", [ a ]) ->
            // print goes through %O in the oracle prelude, and .NET spells
            // Boolean.ToString with a capital
            "(block (result anyref) (if (i32.eqz " + unwrapI32 (recur a) + ")"
            + " (then (call $prints (array.new_fixed $str 5 (i32.const 70) (i32.const 97) (i32.const 108) (i32.const 115) (i32.const 101))))"
            + " (else (call $prints (array.new_fixed $str 4 (i32.const 84) (i32.const 114) (i32.const 117) (i32.const 101)))))"
            + " (call $putc (i32.const 10)) (ref.i31 (i32.const 0)))"
        | EApp (EUnknown "printc", [ a ]) ->
            "(block (result anyref) (call $putc " + unwrapI32 (recur a) + ")"
            + " (call $putc (i32.const 10)) (ref.i31 (i32.const 0)))"
        | EApp (EUnknown "printh", [ a ]) ->
            // a half is an i31 at runtime, so printing needs the STATIC type
            // to know it is not an integer
            "(block (result anyref) (call $printval (call $oss (call $h2f " + unwrapI32 (recur a) + ")))"
            + " (call $putc (i32.const 10)) (ref.i31 (i32.const 0)))"
        | EApp (EUnknown "printu", [ a ]) ->
            "(block (result anyref) (call $printu " + recur a + ") (call $putc (i32.const 10)) (ref.i31 (i32.const 0)))"
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
            match dictTryFind sigStructs (v.Path, v.Offset) with
            | Some (_, rs) ->
                let call = compileCall locals extraLocals freeEnv v args
                (match rs with
                 | Some srn ->
                     // materialize the returned leaves for a uniform consumer
                     let leaves = leavesOf srn
                     let locs = leaves |> List.map (fun (_, k, _) -> newTypedLocal "rl" (wasmTyOf2 k))
                     let sets = List.rev locs |> List.map (fun l -> "(local.set " + l + ")")
                     let leafOf (path : string) =
                         let idx = leaves |> List.findIndex (fun (lp, _, _) -> lp = path)
                         "(local.get " + List.item idx locs + ")"
                     "(block (result anyref) " + call + " " + String.concat " " sets + " "
                     + structFromLeaves srn leafOf "" + ")"
                 | None ->
                     // scalar result: box for uniform consumers (peephole cancels)
                     let rk2 =
                         match dictTryFind sigKinds (v.Path, v.Offset) with
                         | Some (_, r) -> r
                         | None -> "u"
                     if rk2 = "u" then call else boxK rk2 call)
            | None ->
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
        | ELet (true, _, _, ELam _, _) when List.length (fst (recGroupOf e)) > 1 ->
            // a `let rec f ... and g ...` group of local functions. Each
            // member captures the OTHERS, so no member can be built until
            // every name has a slot: give each one a freshly allocated marker
            // (distinct identity, so ref.eq tells them apart), build every
            // closure over those markers, then replace each marker with the
            // closure it stood for. Same trick as the single-binding case,
            // one marker per binding instead of the shared global.
            let members, groupBody = recGroupOf e
            let clean (nm : string) = nm |> String.map (fun c -> if System.Char.IsLetterOrDigit c then c else '_')
            let slots =
                members
                |> List.map (fun (v, lam) ->
                    v, lam, newLocal (clean v.Name), newLocal ("mk_" + clean v.Name), newLocal ("cl_" + clean v.Name))
            // every name is in scope for every body, so bind the slots first
            for v, _, l, _, _ in slots do dictSet locals (v.Path, v.Offset) l
            let markers =
                slots
                |> List.map (fun (_, _, l, m, _) ->
                    "(local.set " + m + " (struct.new $du0 (i32.const -999))) (local.set " + l + " (local.get " + m + "))")
            let builds =
                slots |> List.map (fun (_, lam, _, _, c) -> "(local.set " + c + " " + recur lam + ")")
            let installs =
                slots |> List.map (fun (_, _, l, _, c) -> "(local.set " + l + " (local.get " + c + "))")
            let patches =
                slots
                |> List.collect (fun (_, _, _, _, c) ->
                    slots
                    |> List.map (fun (_, _, _, m2, c2) ->
                        "(call $patchmark (local.get " + c + ") (local.get " + m2 + ") (local.get " + c2 + "))"))
            "(block (result anyref) "
            + String.concat " " (markers @ builds @ installs @ patches)
            + " " + recurT groupBody + ")"
        | ELet (true, v, _, ELam (ps, lbody), body) ->
            // recursive local function: lambda-lift via a self-slot that is
            // patched after construction (env cells are mutable)
            let l = newLocal (v.Name |> String.map (fun c -> if System.Char.IsLetterOrDigit c then c else '_'))
            dictSet locals (v.Path, v.Offset) l
            // the closure captures a unique marker for itself; after the
            // closure exists, every env slot holding the marker is patched
            let cloW = recur (ELam (ps, lbody))
            "(block (result anyref) (local.set " + l + " (global.get $selfmark)) "
            + "(local.set " + l + " " + cloW + ") "
            + "(call $patchself (local.get " + l + ")) " + recurT body + ")"
        | ELet (_, _, _, _, _) ->
            // ITERATIVE over the let-SPINE. Recursing per link concatenated
            // the whole remaining body at every level — O(depth * size) in
            // emitted text, which is tens of GB on a several-thousand-let
            // body like the emitter's own. Same bytes out, built once.
            let spine = System.Text.StringBuilder ()
            let mutable closes = 0
            let mutable cur = e
            let mutable walking = true
            while walking do
                match cur with
                // rec-lambda and letrec-group forms have their own cases
                // above; the spine stops and recurT re-dispatches to them
                | ELet (true, _, _, ELam _, _) -> walking <- false
                | ELet (_, v, _, rhs, body) when (dictTryFind cellVars (v.Path, v.Offset)).IsSome ->
                    // captured mutable: the frame holds the cell, not the value
                    let l = newLocal (v.Name |> String.map (fun c -> if System.Char.IsLetterOrDigit c then c else '_'))
                    let r = recur rhs
                    dictSet locals (v.Path, v.Offset) l
                    spine.Append("(block (result anyref) (local.set " + l + " (struct.new $cell " + r + ")) ") |> ignore
                    closes <- closes + 1
                    cur <- body
                | ELet (_, v, _, rhs, body) ->
                    let k = kindOf rhs
                    let l = newTypedLocal (v.Name |> String.map (fun c -> if System.Char.IsLetterOrDigit c then c else '_')) (wasmTyOf k)
                    let r = recur rhs
                    dictSet locals (v.Path, v.Offset) l
                    dictSet localKinds (v.Path, v.Offset) k
                    let stored = if k = "u" then r else unboxK k r
                    spine.Append("(block (result anyref) (local.set " + l + " " + stored + ") ") |> ignore
                    closes <- closes + 1
                    cur <- body
                | _ -> walking <- false
            spine.Append (recurT cur) |> ignore
            spine.Append (String.replicate closes ")") |> ignore
            spine.ToString ()
        | EIf (c, t, f) ->
            "(if (result anyref) (i32.ne (i32.const 0) " + unwrapI32 (recur c) + ") (then "
            + recurT t + ") (else " + recurT f + "))"
        // int64 bitwise and shifts. The suffixed-arithmetic path covers
        // + - * / % and the comparisons but not these; a shift count is an
        // int in F#, so it is widened to match the value being shifted.
        | EPrim (op, [ a; b ]) when
                op.EndsWith "l" && op.Length > 1
                && List.contains (op.Substring (0, op.Length - 1)) [ "&&&"; "|||"; "^^^"; "<<<"; ">>>" ] ->
            let ia = "(call $tol " + recur a + ")"
            let ib = "(call $tol " + recur b + ")"
            let shift = "(i64.extend_i32_s " + unwrapI32 (recur b) + ")"
            (match op.Substring (0, op.Length - 1) with
             | "&&&" -> "(call $ofl (i64.and " + ia + " " + ib + "))"
             | "|||" -> "(call $ofl (i64.or " + ia + " " + ib + "))"
             | "^^^" -> "(call $ofl (i64.xor " + ia + " " + ib + "))"
             | "<<<" -> "(call $ofl (i64.shl " + ia + " " + shift + "))"
             | _ -> "(call $ofl (i64.shr_s " + ia + " " + shift + "))")
        | EPrim (op, [ a; b ]) when op.EndsWith "w" && op.Length > 1 ->
            // computed ONCE: these are used up to 14 times per case, and a
            // thunk re-ran the whole recursive walk on each use — the cost
            // multiplied through nesting (13^depth), which is what made
            // emitting the compiler's own emitter take 110M walks
            let iaW = unwrapI32 (recur a)
            let ibW = unwrapI32 (recur b)
            let ia = fun () -> iaW
            let ib = fun () -> ibW
            (match op.Substring (0, op.Length - 1) with
             | "+" -> intWat ("(i32.add " + ia () + " " + ib () + ")")
             | "-" -> intWat ("(i32.sub " + ia () + " " + ib () + ")")
             | "*" -> intWat ("(i32.mul " + ia () + " " + ib () + ")")
             | "/" -> intWat ("(i32.div_u " + ia () + " " + ib () + ")")
             | "%" -> intWat ("(i32.rem_u " + ia () + " " + ib () + ")")
             | "<" -> boolWat ("(i32.lt_u " + ia () + " " + ib () + ")")
             | ">" -> boolWat ("(i32.gt_u " + ia () + " " + ib () + ")")
             | "<=" -> boolWat ("(i32.le_u " + ia () + " " + ib () + ")")
             | ">=" -> boolWat ("(i32.ge_u " + ia () + " " + ib () + ")")
             | "&&&" -> intWat ("(i32.and " + ia () + " " + ib () + ")")
             | "|||" -> intWat ("(i32.or " + ia () + " " + ib () + ")")
             | "^^^" -> intWat ("(i32.xor " + ia () + " " + ib () + ")")
             | "<<<" -> intWat ("(i32.shl " + ia () + " " + ib () + ")")
             | ">>>" -> intWat ("(i32.shr_u " + ia () + " " + ib () + ")")
             | other ->
                 vecAdd errors ("unsupported unsigned operator " + other)
                 "(ref.i31 (i32.const 0))")
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
                // `+` concatenates; ordering is a byte-wise compare, which is
                // ordinal — the same thing F#'s `<` on strings does
                let cmp =
                    "(call $strcmp (ref.cast (ref $str) " + recur a + ") (ref.cast (ref $str) " + recur b + "))"
                (match baseOp with
                 | "+" -> "(call $strcat (ref.cast (ref $str) " + recur a + ") (ref.cast (ref $str) " + recur b + "))"
                 | "<" -> boolWat ("(i32.lt_s " + cmp + " (i32.const 0))")
                 | ">" -> boolWat ("(i32.gt_s " + cmp + " (i32.const 0))")
                 | "<=" -> boolWat ("(i32.le_s " + cmp + " (i32.const 0))")
                 | ">=" -> boolWat ("(i32.ge_s " + cmp + " (i32.const 0))")
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
        // float16: widen, operate in f32, round back. One rounding, and
        // therefore the correctly-rounded f16 answer.
        | EPrim (op, [ a; b ]) when
            op.EndsWith "h" && op.Length > 1
            && List.contains (op.Substring (0, op.Length - 1)) [ "+"; "-"; "*"; "/"; "<"; ">"; "<="; ">="; "="; "<>" ] ->
            let baseOp = op.Substring (0, op.Length - 1)
            let wa = "(call $h2f " + unwrapI32 (recur a) + ")"
            let wb = "(call $h2f " + unwrapI32 (recur b) + ")"
            (match baseOp with
             | "+" -> intWat ("(call $f2h (f32.add " + wa + " " + wb + "))")
             | "-" -> intWat ("(call $f2h (f32.sub " + wa + " " + wb + "))")
             | "*" -> intWat ("(call $f2h (f32.mul " + wa + " " + wb + "))")
             | "/" -> intWat ("(call $f2h (f32.div " + wa + " " + wb + "))")
             | "<" -> boolWat ("(f32.lt " + wa + " " + wb + ")")
             | ">" -> boolWat ("(f32.gt " + wa + " " + wb + ")")
             | "<=" -> boolWat ("(f32.le " + wa + " " + wb + ")")
             // IEEE equality, not the bit pattern: -0.0h equals 0.0h,
             // and a NaN half equals nothing — not even itself
             | "=" -> boolWat ("(f32.eq " + wa + " " + wb + ")")
             | "<>" -> boolWat ("(f32.ne " + wa + " " + wb + ")")
             | _ -> boolWat ("(f32.ge " + wa + " " + wb + ")"))
        | EPrim (("sqrth" | "absh" | "truncateh" | "u-h") as op, [ a ]) ->
            let w = "(call $h2f " + unwrapI32 (recur a) + ")"
            let instr =
                match op with
                | "sqrth" -> "f32.sqrt"
                | "absh" -> "f32.abs"
                | "truncateh" -> "f32.trunc"
                | _ -> "f32.neg"
            intWat ("(call $f2h (" + instr + " " + w + "))")
        // unary machine instructions the numeric classes expose by name.
        // `abs` is the INSTRUCTION rather than `if x < 0 then -x`, because
        // that form gets -0.0 and NaN wrong.
        | EPrim (("sqrtf" | "sqrts" | "absf" | "abss" | "truncatef" | "truncates") as op, [ a ]) ->
            let f32 = op.EndsWith "s"
            let ty = if f32 then "f32" else "f64"
            let un = if f32 then "$tos" else "$tof"
            let box_ = if f32 then "$oss" else "$off"
            let instr =
                if op.StartsWith "sqrt" then ".sqrt"
                elif op.StartsWith "abs" then ".abs"
                else ".trunc"
            "(call " + box_ + " (" + ty + instr + " (call " + un + " " + recur a + ")))"
        | EPrim ("abs", [ a ]) ->
            let x = unwrapI32 (recur a)
            intWat ("(select (i32.sub (i32.const 0) " + x + ") " + x
                    + " (i32.lt_s " + x + " (i32.const 0)))")
        | EPrim ("absl", [ a ]) ->
            let x = "(call $tol " + recur a + ")"
            "(call $ofl (select (i64.sub (i64.const 0) " + x + ") " + x
            + " (i64.lt_s " + x + " (i64.const 0))))"
        | EPrim ("u-f", [ a ]) -> "(call $off (f64.neg (call $tof " + recur a + ")))"
        | EPrim ("u-s", [ a ]) -> "(call $oss (f32.neg (call $tos " + recur a + ")))"
        | EPrim ("u-l", [ a ]) -> "(call $ofl (i64.sub (i64.const 0) (call $tol " + recur a + ")))"
        | EPrim ("u~~~", [ a ]) -> intWat ("(i32.xor " + unwrapI32 (recur a) + " (i32.const -1))")
        | EPrim (op, [ a; b ]) ->
            // computed ONCE: these are used up to 14 times per case, and a
            // thunk re-ran the whole recursive walk on each use — the cost
            // multiplied through nesting (13^depth), which is what made
            // emitting the compiler's own emitter take 110M walks
            let iaW = unwrapI32 (recur a)
            let ibW = unwrapI32 (recur b)
            let ia = fun () -> iaW
            let ib = fun () -> ibW
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
        // uint32: the payload is the same i32, only the operations differ
        | EPrim ("unot", [ a ]) -> boolWat ("(i32.eqz " + unwrapI32 (recur a) + ")")
        | EPrim ("u-", [ a ]) -> intWat ("(i32.sub (i32.const 0) " + unwrapI32 (recur a) + ")")
        | EPrim (op, _) ->
            vecAdd errors ("unsupported operator " + op)
            "(ref.i31 (i32.const 0))"
        | ETuple xs ->
            "(struct.new $tup" + string xs.Length + " " + String.concat " " (List.map recur xs) + ")"
        | EListLit xs ->
            List.foldBack (fun x acc -> "(struct.new $cons " + recur x + " " + acc + ")") xs "(ref.null any)"
        | ECtor (name, _, _) when (dictTryFind enumConst name).IsSome ->
            "(call $ofi (i32.const " + string (dictTryFind enumConst name).Value + "))"
        | ECtor (name, _, args) ->
            (match dictTryFind caseArity name with
             | Some 0 -> "(global.get $c_" + name + ")"
             | Some _ when not (List.isEmpty args) ->
                 "(struct.new $du1 (i32.const " + string (dictTryFind caseTag name).Value + ") " + String.concat " " (List.map recur args) + ")"
             | Some 1 ->
                 // the constructor as a VALUE (`|> Some`, `>> ValueSome`):
                 // a closure whose function builds the case
                 if not (List.contains name (vecToList ctorAsFn)) then vecAdd ctorAsFn name
                 "(struct.new $clo (ref.func $ctorfn_" + name + ") (ref.null any))"
             | Some _ ->
                 // multi-payload ctor referenced unapplied
                 vecAdd errors ("unapplied constructor " + name)
                 "(ref.i31 (i32.const 0))"
             | None ->
                 vecAdd errors ("unknown constructor " + name)
                 "(ref.i31 (i32.const 0))")
        | ERecordExt (rn, baseExpr, fields) ->
            // a derived instance IS its base's layout plus its own fields, so
            // the base part is copied slot-for-slot out of a base instance
            (match dictTryFind recordOrder rn, baseOf rn with
             | Some order, Some bn ->
                 let baseOrder = match dictTryFind recordOrder bn with Some o -> o | None -> []
                 let b = newLocal "b"
                 let unboxBy (k : string) (w : string) =
                     match k with
                     | "f" -> "(call $tof " + w + ")" | "s" -> "(call $tos " + w + ")"
                     | "l" -> "(call $tol " + w + ")" | "i" -> "(call $toi " + w + ")"
                     | _ -> w
                 let vals =
                     order
                     |> List.mapi (fun i (fname, k) ->
                         if fname = "__idhash" then "(i32.const 0)"
                         elif fname = "__desc" then "(global.get $desc_" + rn + ")"
                         elif i < baseOrder.Length then
                             // same slot index in base and derived — prefix layout
                             "(struct.get $r_" + bn + " " + string i + " (ref.cast (ref $r_" + bn + ") (local.get " + b + ")))"
                         else
                             match fields |> List.tryFind (fun (f, _) -> f = fname) with
                             | Some (_, v) -> unboxBy k (recur v)
                             | None ->
                                 vecAdd errors ("missing field " + fname + " in " + rn)
                                 "(ref.i31 (i32.const 0))")
                 "(block (result anyref) (local.set " + b + " " + recur baseExpr + ") "
                 + "(struct.new $r_" + rn + " " + String.concat " " vals + "))"
             | _ ->
                 vecAdd errors ("cannot build " + rn + ": unknown base layout")
                 "(ref.i31 (i32.const 0))")
        | ERecord (tyName, fields) ->
            (match (if tyName <> "" && tyName <> "?" && (dictTryFind recordOrder tyName).IsSome
                    then Some (tyName, 0, "")
                    else fields |> List.tryPick (fun (f, _) -> dictTryFind fieldIndex f)) with
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
                         if fname = "__idhash" then "(i32.const 0)"
                         elif fname = "__desc" && isObjRecord rn then "(global.get $desc_" + rn + ")"
                         else
                         match fields |> List.tryFind (fun (f, _) -> f = fname) with
                         | Some (_, v) -> unboxBy k (recur v)
                         | None ->
                             emitError ("missing field " + fname + " in "
                                        + (if tyName = rn then rn else rn + " (asked for " + tyName + ")"))
                             "(ref.i31 (i32.const 0))")
                 "(struct.new $r_" + rn + " " + String.concat " " vals + ")"
             | None ->
                 vecAdd errors "record with unknown type"
                 "(ref.i31 (i32.const 0))")
        | EField (_, _, _) when
            (let rec pathOfVar (e : Expr) =
                match e with
                | EVar (v, _) -> (match dictTryFind paramLeaves (v.Path, v.Offset) with
                                  | Some (rn, m) -> Some (rn, m, "")
                                  | None -> None)
                | EField (b, f, _) ->
                    (match pathOfVar b with
                     | Some (rn, m, p) -> Some (rn, m, (if p = "" then f else p + "." + f))
                     | None -> None)
                | _ -> None
             match e with
             | EField (b, f, _) ->
                 (match pathOfVar b with
                  | Some (_, m, p) -> (dictTryFind m (if p = "" then f else p + "." + f)).IsSome
                  | None -> false)
             | _ -> false) ->
            let rec pathOfVar (x : Expr) =
                match x with
                | EVar (v, _) -> (match dictTryFind paramLeaves (v.Path, v.Offset) with
                                  | Some (rn, m) -> Some (rn, m, "")
                                  | None -> None)
                | EField (b, f, _) ->
                    (match pathOfVar b with
                     | Some (rn, m, p) -> Some (rn, m, (if p = "" then f else p + "." + f))
                     | None -> None)
                | _ -> None
            (match e with
             | EField (b, f, _) ->
                 let rn, m, p = (pathOfVar b).Value
                 let full = if p = "" then f else p + "." + f
                 let loc = (dictTryFind m full).Value
                 let _, k, _ = leavesOf rn |> List.find (fun (lp, _, _) -> lp = full)
                 (match k with
                  | "f" | "s" | "l" -> boxK k ("(local.get " + loc + ")")
                  | _ -> "(call $ofi (local.get " + loc + "))")
             | _ -> "(ref.i31 (i32.const 0))")
        | EField (inner, fname, _) when
            (let rec pathOf (e : Expr) =
                match e with
                | EIndex (nm2, a2, i2) -> (if isPod nm2 then Some (nm2, a2, i2, "") else None)
                | EField (b, f2, _) ->
                    (match pathOf b with
                     | Some (nm2, a2, i2, p) -> Some (nm2, a2, i2, (if p = "" then f2 else p + "." + f2))
                     | None -> None)
                | _ -> None
             match pathOf inner with
             | Some (nm2, _, _, p) ->
                 let full = if p = "" then fname else p + "." + fname
                 let placed, _, _ = (dictTryFind podLayout nm2).Value
                 placed |> List.exists (fun (lp, _, _) -> lp = full)
             | None -> false) ->
            // packed-array fusion: whole leaf path -> one word read
            let rec pathOf (e : Expr) =
                match e with
                | EIndex (nm2, a2, i2) -> (if isPod nm2 then Some (nm2, a2, i2, "") else None)
                | EField (b, f2, _) ->
                    (match pathOf b with
                     | Some (nm2, a2, i2, p) -> Some (nm2, a2, i2, (if p = "" then f2 else p + "." + f2))
                     | None -> None)
                | _ -> None
            let nm, a, i, p = (pathOf inner).Value
            let full = if p = "" then fname else p + "." + fname
            let placed, _, wd = (dictTryFind podLayout nm).Value
            let _, k, _ = placed |> List.find (fun (lp, _, _) -> lp = full)
            let baseW = "(i32.mul " + unwrapI32 (recur i) + " (i32.const " + string wd + "))"
            let raw = fieldFromWords nm (recur a) baseW full
            (match k with
             | "f" | "s" | "l" -> boxK k raw
             | "i" -> "(call $ofi " + raw + ")"
             | _ -> raw)
        | EField (EIndex (nm, a, i), fname, owner) when isStructName nm && not (isPod nm) && (fieldSlot owner fname).IsSome ->
            // fusion: pts.[i].X reads the SoA field array directly — no
            // temporary struct materialization
            let _, fi, k = (fieldSlot owner fname).Value
            let src = "(struct.get $sarr_" + nm + " " + string fi + " (ref.cast (ref $sarr_" + nm + ") " + recur a + "))"
            let raw =
                match k with
                | "f" | "s" | "l" | "i" -> "(array.get " + parrOf k + " " + src + " " + unwrapI32 (recur i) + ")"
                | _ -> "(array.get $arr " + src + " " + unwrapI32 (recur i) + ")"
            (match k with
             | "f" | "s" | "l" -> boxK k raw
             | "i" -> "(call $ofi " + raw + ")"
             | _ -> raw)
        | EField (r, "Length", _) when not (dictTryFind fieldIndex "Length").IsSome ->
            "(call $lenv " + recur r + ")"
        | EIfaceCall (iface, mname, recv, args) ->
            (match slotOf iface mname with
             | Some slot ->
                 let t = newLocal "d"
                 let arity = 1 + args.Length
                 let ft = "$v" + string arity
                 let dsc =
                     "(struct.get $desc 1 (ref.cast (ref $desc) (struct.get $obj 0 (ref.cast (ref $obj) (local.get " + t + ")))))"
                 let dispatch =
                     "(call_ref " + ft + " (local.get " + t + ") "
                     + String.concat " " (List.map recur args) + " "
                     + "(ref.cast (ref " + ft + ") (array.get $vt " + dsc + " (i32.const " + string slot + "))))"
                 // lists and arrays ARE seqs, but carry no vtable: the
                 // enumeration protocol pre-tests their representation and
                 // routes to the built-in iterators
                 if iface = "IEnumerable" && mname = "GetEnumerator" then
                     "(block (result anyref) (local.set " + t + " " + recur recv + ") "
                     + "(if (result anyref) (call $isBuiltinSeq (local.get " + t + "))"
                     + " (then (call $iterNew (local.get " + t + ")))"
                     + " (else " + dispatch + ")))"
                 elif iface = "IEnumerator" && (mname = "MoveNext" || mname = "Current") then
                     let builtin =
                         if mname = "MoveNext" then "(call $iterNext (local.get " + t + "))"
                         else "(call $iterCur (local.get " + t + "))"
                     "(block (result anyref) (local.set " + t + " " + recur recv + ") "
                     + "(if (result anyref) (ref.test (ref $iter) (local.get " + t + "))"
                     + " (then " + builtin + ")"
                     + " (else " + dispatch + ")))"
                 else
                     "(block (result anyref) (local.set " + t + " " + recur recv + ") " + dispatch + ")"
             | None ->
                 vecAdd errors ("no dispatch slot for " + iface + "." + mname)
                 "(ref.i31 (i32.const 0))")
        | ETypeTest (tn, e) ->
            // Which representations satisfy `x :? tn`?
            //   list/array/string -> a representation test (they carry no
            //     descriptor); an INTERFACE -> the classes implementing it;
            //     a class -> itself and its subclasses.
            // The class-id read is GUARDED: a non-object answers false, it
            // does not trap — `(box 5) :? HashSet` is a question, not a bug.
            let t = newLocal "q"
            let v = "(local.get " + t + ")"
            let wrap (test : string) =
                "(block (result anyref) (local.set " + t + " " + recur e + ") (call $ofi " + test + "))"
            let idOf =
                "(struct.get $desc 0 (ref.cast (ref $desc) (struct.get $obj 0 (ref.cast (ref $obj) " + v + "))))"
            let classIdTest (classes : string list) =
                let hit =
                    match classes |> List.filter isObjRecord
                          |> List.map (fun c -> "(i32.eq " + idOf + " (i32.const " + string (descId c) + "))") with
                    | [] -> "(i32.const 0)"
                    | [ one ] -> one
                    | many -> many |> List.reduce (fun a b -> "(i32.or " + a + " " + b + ")")
                "(if (result i32) (ref.test (ref $obj) " + v + ") (then " + hit + ") (else (i32.const 0)))"
            let implementorsOf (iface : string) =
                classImpls
                |> List.filter (fun (_, impls) -> impls |> List.exists (fun (i, _) -> i = iface))
                |> List.collect (fun (cn, _) -> subclassesOf cn)
                |> List.distinct
            if tn = "list" then
                // nil is a null reference, so null tests as the empty list
                // (recorded with the other representation decisions)
                wrap ("(i32.or (ref.is_null " + v + ") (ref.test (ref $cons) " + v + "))")
            elif tn = "array" then wrap ("(call $isArrayRep " + v + ")")
            elif tn = "string" then wrap ("(ref.test (ref $str) " + v + ")")
            elif isObjRecord tn then wrap (classIdTest (subclassesOf tn))
            elif interfaceDecls |> List.exists (fun (i, _) -> i = tn) then
                wrap (classIdTest (implementorsOf tn))
            else
                vecAdd errors ("cannot type-test against " + tn + ": not a class")
                "(ref.i31 (i32.const 0))"
        | ECast (_, e, false) ->
            // widening to an interface or base class: representation is
            // unchanged, so there is nothing to do at runtime
            recur e
        | ECast (tn, e, true) ->
            let interfaceTarget = interfaceDecls |> List.exists (fun (i, _) -> i = tn)
            let builtinTarget = tn = "list" || tn = "array" || tn = "string" || tn = "seq" || tn = "IEnumerable"
            if interfaceTarget || builtinTarget then
                // the representation is uniform, so a downcast to an
                // interface or builtin only CHECKS; lists/arrays/seqs accept
                // their representations (an interface target additionally
                // accepts them for the seq family, where they qualify)
                let t = newLocal "c"
                let v = "(local.get " + t + ")"
                let ok =
                    if tn = "list" then "(i32.or (ref.is_null " + v + ") (ref.test (ref $cons) " + v + "))"
                    elif tn = "array" then "(call $isArrayRep " + v + ")"
                    elif tn = "string" then "(ref.test (ref $str) " + v + ")"
                    elif tn = "seq" || tn = "IEnumerable" then
                        // anything enumerable: builtin reps or an object
                        "(i32.or (call $isBuiltinSeq " + v + ") (ref.test (ref $obj) " + v + "))"
                    else
                        let idOf =
                            "(struct.get $desc 0 (ref.cast (ref $desc) (struct.get $obj 0 (ref.cast (ref $obj) " + v + "))))"
                        let hits =
                            classImpls
                            |> List.filter (fun (_, impls) -> impls |> List.exists (fun (i, _) -> i = tn))
                            |> List.collect (fun (cn, _) -> subclassesOf cn)
                            |> List.distinct
                            |> List.filter isObjRecord
                            |> List.map (fun c -> "(i32.eq " + idOf + " (i32.const " + string (descId c) + "))")
                        let hit = match hits with [] -> "(i32.const 0)" | [ one ] -> one | many -> many |> List.reduce (fun a b -> "(i32.or " + a + " " + b + ")")
                        "(if (result i32) (ref.test (ref $obj) " + v + ") (then " + hit + ") (else (i32.const 0)))"
                // null casts to null, as it does everywhere: `x :?> T` on a
                // null reference is null, not an error
                "(block (result anyref) (local.set " + t + " " + recur e + ") "
                + "(if (result anyref) (i32.or (ref.is_null " + v + ") " + ok + ") "
                + "(then " + v + ") "
                + "(else (throw $fppexn (struct.new $du1 (i32.const " + string (dictTryFind caseTag "InvalidCast").Value
                + ") " + recur (ELit (LString ("\"invalid cast to " + tn + "\""))) + ")))))"
            elif not (isObjRecord tn) then
                vecAdd errors ("cannot downcast to " + tn + ": not a class")
                "(ref.i31 (i32.const 0))"
            else
                let t = newLocal "c"
                let idOf =
                    "(struct.get $desc 0 (ref.cast (ref $desc) (struct.get $obj 0 (ref.cast (ref $obj) (local.get " + t + ")))))"
                // a downcast succeeds for the target class OR any subclass.
                // The descriptor read is GUARDED and null passes through: a
                // null reference casts to null, and a non-object answers the
                // cast with InvalidCast rather than trapping.
                let castTest =
                    let hit =
                        match subclassesOf tn |> List.map (fun c -> "(i32.eq " + idOf + " (i32.const " + string (descId c) + "))") with
                        | [] -> "(i32.const 0)"
                        | [ one ] -> one
                        | many -> many |> List.reduce (fun a b -> "(i32.or " + a + " " + b + ")")
                    "(if (result i32) (ref.test (ref $obj) (local.get " + t + ")) (then " + hit + ") (else (i32.const 0)))"
                "(block (result anyref) (local.set " + t + " " + recur e + ") "
                + "(if (result anyref) (i32.or (ref.is_null (local.get " + t + ")) " + castTest + ") "
                + "(then (local.get " + t + ")) "
                + "(else (throw $fppexn (struct.new $du1 (i32.const " + string (dictTryFind caseTag "InvalidCast").Value
                + ") " + recur (ELit (LString ("\"invalid cast to " + tn + "\""))) + "))))) "
        | EFieldSet (r, fname, owner, v) ->
            (match fieldSlot owner fname with
             | Some (rn, idx, k) ->
                 let stored =
                     match k with
                     | "f" -> "(call $tof " + recur v + ")" | "s" -> "(call $tos " + recur v + ")"
                     | "l" -> "(call $tol " + recur v + ")" | "i" -> "(call $toi " + recur v + ")"
                     | _ -> recur v
                 "(block (result anyref) (struct.set $r_" + rn + " " + string idx
                 + " (ref.cast (ref $r_" + rn + ") " + recur r + ") " + stored + ") (ref.i31 (i32.const 0)))"
             | None ->
                 emitError ("unknown field " + fname)
                 "(ref.i31 (i32.const 0))")
        | EField (r, fname, owner) ->
            (match fieldSlot owner fname with
             | Some (rn, idx, k) ->
                 let raw = "(struct.get $r_" + rn + " " + string idx + " (ref.cast (ref $r_" + rn + ") " + recur r + "))"
                 (match k with
                  | "f" -> "(call $off " + raw + ")" | "s" -> "(call $oss " + raw + ")"
                  | "l" -> "(call $ofl " + raw + ")" | "i" -> "(call $ofi " + raw + ")"
                  | _ -> raw)
             | None ->
                 emitError ("unknown field " + fname)
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
        | EAssign (v, e) when (dictTryFind cellVars (v.Path, v.Offset)).IsSome ->
            // the cell may live in this frame or in the closure's env; both
            // reads yield the same cell, and the write goes through it
            let cell =
                match dictTryFind locals (v.Path, v.Offset) with
                | Some l -> "(local.get " + l + ")"
                | None ->
                    match dictTryFind freeEnv (v.Path, v.Offset) with
                    | Some idx ->
                        "(array.get $arr (ref.cast (ref $arr) (local.get $env)) (i32.const " + string idx + "))"
                    | None ->
                        emitError ("assignment to unknown " + v.Name)
                        "(ref.i31 (i32.const 0))"
            "(block (result anyref) (struct.set $cell 0 (ref.cast (ref $cell) " + cell + ") "
            + recur e + ") (ref.i31 (i32.const 0)))"
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
            if nm = "$ref" then
                // a uniform reference element (tuples, functions): plain $arr
                "(array.get $arr (ref.cast (ref $arr) " + recur a + ") " + unwrapI32 (recur i) + ")"
            elif nm = "$str" then
                // char access on a STRING receiver (the "$str" sentinel)
                "(ref.i31 (array.get_u $str (ref.cast (ref $str) " + recur a + ") " + unwrapI32 (recur i) + "))"
            elif pk <> "" then
                let getOp = if pk = "h" then "array.get_u " else "array.get "
                "(call " + boxOfKind pk + " (" + getOp + parrOf pk + " (ref.cast (ref " + parrOf pk + ") " + recur a + ") " + unwrapI32 (recur i) + "))"
            elif isPod nm then
                let placed, _, wd = (dictTryFind podLayout nm).Value
                let al = newLocal "pa"
                let bl = newTypedLocal "pb" "i32"
                let arrW = "(local.get " + al + ")"
                let leafOf (path : string) = fieldFromWords nm arrW ("(local.get " + bl + ")") path
                "(block (result anyref) (local.set " + al + " " + recur a + ") "
                + "(local.set " + bl + " (i32.mul " + unwrapI32 (recur i) + " (i32.const " + string wd + "))) "
                + structFromLeaves nm leafOf "" + ")"
                |> fun x -> ignore placed; x
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
            elif nm <> "" && not (nm.StartsWith "#") then
                // any other KNOWN element type is a boxed reference: string,
                // class, list, function — all live in a uniform $arr
                "(array.get $arr (ref.cast (ref $arr) " + recur a + ") " + unwrapI32 (recur i) + ")"
            else
                emitError ("array read needs a statically known element type (got '" + nm + "')")
                "(ref.i31 (i32.const 0))"
        | EIndexSet (nm, a, i, v) ->
            let pk = primKindOf nm
            if nm = "$ref" then
                "(block (result anyref) (array.set $arr (ref.cast (ref $arr) " + recur a + ") "
                + unwrapI32 (recur i) + " " + recur v + ") (ref.i31 (i32.const 0)))"
            elif pk <> "" then
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
            elif nm <> "" && not (nm.StartsWith "#") then
                // boxed reference elements: a uniform $arr, no unboxing
                "(block (result anyref) (array.set $arr (ref.cast (ref $arr) " + recur a + ") "
                + unwrapI32 (recur i) + " " + recur v + ") (ref.i31 (i32.const 0)))"
            else
                emitError ("array write needs a statically known element type (got '" + nm + "')")
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
            if nm = "$ref" then
                "(call $ofi (array.len (ref.cast (ref $arr) " + recur a + ")))"
            elif nm = "$str" then
                // .Length on a STRING receiver (the "$str" sentinel)
                "(call $ofi (array.len (ref.cast (ref $str) " + recur a + ")))"
            elif pk <> "" then
                "(call $ofi (array.len (ref.cast (ref " + parrOf pk + ") " + recur a + ")))"
            elif isPod nm then
                let _, _, wd = (dictTryFind podLayout nm).Value
                "(call $ofi (i32.div_u " + hLen (recur a) + " (i32.const " + string wd + ")))"
            elif isStructName nm then
                "(call $ofi (array.len (struct.get $sarr_" + nm + " 0 (ref.cast (ref $sarr_" + nm + ") " + recur a + "))))"
            elif nm <> "" && not (nm.StartsWith "#") then
                // boxed reference elements live in a uniform $arr
                "(call $ofi (array.len (ref.cast (ref $arr) " + recur a + ")))"
            else
                emitError ("length needs a statically known element type (got '" + nm + "')")
                "(ref.i31 (i32.const 0))"
        | EArrayCreate (nm, n, EUnknown "$zero") ->
            // Array.zeroCreate: wasm's array.new_default IS the zero fill —
            // numeric zeros, null refs — so no loop and no value operand
            let pk = primKindOf nm
            if pk <> "" then
                "(array.new_default " + parrOf pk + " " + unwrapI32 (recur n) + ")"
            elif isPod nm then
                let _, _, wd = (dictTryFind podLayout nm).Value
                "(struct.new $hnd (array.new_default $pk (i32.mul " + unwrapI32 (recur n)
                + " (i32.const " + string wd + "))) (i32.const 0) (i32.const 0))"
            elif isStructName nm then
                let fs = structRecords |> List.pick (fun (rn, fs) -> if rn = nm then Some fs else None)
                let nl = newTypedLocal "zn" "i32"
                let mk (k : string) =
                    match k with
                    | "f" | "s" | "l" | "i" | "h" -> "(array.new_default " + parrOf k + " (local.get " + nl + "))"
                    | _ -> "(array.new_default $arr (local.get " + nl + "))"
                "(block (result anyref) (local.set " + nl + " " + unwrapI32 (recur n) + ") "
                + "(struct.new $sarr_" + nm + " " + (fs |> List.map (fun (_, k) -> mk k) |> String.concat " ") + "))"
            else
                // a reference element zero-fills with nulls
                "(array.new_default $arr " + unwrapI32 (recur n) + ")"
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
            let res = newLocal "tres"
            let exn = newLocal "texn"
            let w = System.Text.StringBuilder()
            w.Append("(block (result anyref) (block $tdone" + res + " (local.set " + exn + " (block $tcatch" + res + " (result anyref) ") |> ignore
            w.Append("(try_table (catch $fppexn $tcatch" + res + ") (local.set " + res + " " + recur body + ")) ") |> ignore
            w.Append("(br $tdone" + res + "))) ") |> ignore
            cases |> List.iteri (fun i (pat, guard, cbody) ->
                // same shared-body scheme as EMatch (see there)
                let lbl = "$tcase" + res + "_" + string i
                let alts = expandOr pat
                w.Append("(block " + lbl + " ") |> ignore
                (match alts with
                 | [ single ] ->
                     let tests = System.Text.StringBuilder()
                     compilePat locals extraLocals freeEnv tests lbl ("(local.get " + exn + ")") single
                     w.Append(tests.ToString()) |> ignore
                 | many ->
                     let hm = "$thave" + res + "_" + string i
                     // one slot map shared by all alternatives: they bind the
                     // same identities, and the shared body reads one slot
                     let orSlots = dictNew<string * int, string> ()
                     w.Append("(block " + hm + " ") |> ignore
                     many |> List.iteri (fun j alt ->
                         let al = "$talt" + res + "_" + string i + "_" + string j
                         w.Append("(block " + al + " ") |> ignore
                         let tests = System.Text.StringBuilder()
                         compilePatWith orSlots locals extraLocals freeEnv tests al ("(local.get " + exn + ")") alt
                         // after the first alternative, every binder it
                         // introduced is the slot the others must reuse
                         for k, sl in dictPairs locals do
                             if (dictTryFind orSlots k).IsNone then dictSet orSlots k sl
                         w.Append(tests.ToString()) |> ignore
                         w.Append("(br " + hm + ")) ") |> ignore)
                     w.Append("(br " + lbl + ")) ") |> ignore)
                (match guard with
                 | Some g -> w.Append("(br_if " + lbl + " (i32.eqz " + unwrapI32 (recur g) + ")) ") |> ignore
                 | None -> ())
                w.Append("(local.set " + res + " " + recur cbody + ") (br $tdone" + res + ") ") |> ignore
                w.Append(")") |> ignore)
            w.Append(" (throw $fppexn (local.get " + exn + "))) (local.get " + res + "))") |> ignore
            w.ToString()
        | EMatch (scrut, cases) ->
            let sl = newLocal "scrut"
            let res = newLocal "res"
            let w = System.Text.StringBuilder()
            w.Append("(block (result anyref) (local.set " + sl + " " + recur scrut + ") (block $done" + res + " ") |> ignore
            cases |> List.iteri (fun i (pat, guard, body) ->
                // or-alternatives each get a TEST block; the BODY is emitted
                // ONCE and shared — duplicating it per alternative made the
                // emitted text multiplicative under nesting, and emitting the
                // compiler's own emitter ran out of memory on exactly that
                let lbl = "$case" + res + "_" + string i
                let alts = expandOr pat
                w.Append("(block " + lbl + " ") |> ignore
                (match alts with
                 | [ single ] ->
                     let tests = System.Text.StringBuilder()
                     compilePat locals extraLocals freeEnv tests lbl ("(local.get " + sl + ")") single
                     w.Append(tests.ToString()) |> ignore
                 | many ->
                     let hm = "$have" + res + "_" + string i
                     // one slot map shared by all alternatives: they bind the
                     // same identities, and the shared body reads one slot
                     let orSlots = dictNew<string * int, string> ()
                     w.Append("(block " + hm + " ") |> ignore
                     many |> List.iteri (fun j alt ->
                         let al = "$alt" + res + "_" + string i + "_" + string j
                         w.Append("(block " + al + " ") |> ignore
                         let tests = System.Text.StringBuilder()
                         compilePatWith orSlots locals extraLocals freeEnv tests al ("(local.get " + sl + ")") alt
                         // after the first alternative, every binder it
                         // introduced is the slot the others must reuse
                         for k, sl in dictPairs locals do
                             if (dictTryFind orSlots k).IsNone then dictSet orSlots k sl
                         w.Append(tests.ToString()) |> ignore
                         w.Append("(br " + hm + ")) ") |> ignore)
                     w.Append("(br " + lbl + ")) ") |> ignore)
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
    /// Emit code pushing the scalar leaves of a struct-typed expression.
    /// Never materializes when the shape is known (record literal,
    /// scalarized param, packed-array read, scalarized call).
    and compileLeaves (locals : Dict<string * int, string>) (extraLocals : Vec<string * string>)
                      (freeEnv : Dict<string * int, int>) (rn : string) (e : Expr) : string =
        let recur = compileExpr locals extraLocals freeEnv false
        let leaves = leavesOf rn
        let unboxLeaf (k : string) (w : string) =
            match k with
            | "f" | "s" | "l" -> unboxK k w
            | _ -> "(call $toi " + w + ")"
        match e with
        | ERecord (_, _) ->
            // project each leaf out of the literal without allocating
            let rec leafFromRecord (rn2 : string) (ex : Expr) (path : string) : string option =
                match ex with
                | ERecord (_, fields) ->
                    let i = path.IndexOf '.'
                    let head = if i < 0 then path else path.Substring (0, i)
                    (match fields |> List.tryFind (fun (f, _) -> f = head) with
                     | Some (_, v) ->
                         if i < 0 then
                             let _, k, _ = leavesOf rn2 |> List.find (fun (lp, _, _) -> lp = path)
                             Some (unboxLeaf k (recur v))
                         else
                             let fs = structRecords |> List.pick (fun (n, f) -> if n = rn2 then Some f else None)
                             let _, fk = fs |> List.find (fun (fn, _) -> fn = head)
                             leafFromRecord (structKindName fk) v (path.Substring (i + 1))
                     | None -> None)
                | _ -> None
            let parts = leaves |> List.map (fun (lp, k, _) ->
                match leafFromRecord rn e lp with
                | Some w -> w
                | None ->
                    let l = newTypedLocalOuter extraLocals "lv" "anyref"
                    unboxLeaf k ("(local.get " + l + ")"))
            String.concat " " parts
        | EVarI (v, sch, _) -> recur (EVar (v, sch))
        | EVar (v, _) when (dictTryFind paramLeaves (v.Path, v.Offset)).IsSome ->
            let _, m = (dictTryFind paramLeaves (v.Path, v.Offset)).Value
            leaves |> List.map (fun (lp, _, _) -> "(local.get " + (dictTryFind m lp).Value + ")") |> String.concat " "
        | EIndex (nm, a, i) when nm = rn && isPod nm ->
            // read leaves straight out of the packed array
            let _, _, wd = (dictTryFind podLayout nm).Value
            let al = newTypedLocalOuter extraLocals "la" "anyref"
            let bl = newTypedLocalOuter extraLocals "lb" "i32"
            let tys = leaves |> List.map (fun (_, k, _) -> wasmTyOf2 k) |> String.concat " "
            "(block (result " + tys + ") (local.set " + al + " " + recur a + ") "
            + "(local.set " + bl + " (i32.mul (call $toi " + recur i + ") (i32.const " + string wd + "))) "
            + (leaves |> List.map (fun (lp, _, _) -> fieldFromWords nm ("(local.get " + al + ")") ("(local.get " + bl + ")") lp) |> String.concat " ")
            + ")"
        | EApp (EVar (fv, _), args) when
            (match dictTryFind sigStructs (fv.Path, fv.Offset) with
             | Some (_, Some r) -> r = rn && (dictTryFind topArity (fv.Path, fv.Offset)) = Some args.Length
             | _ -> false) ->
            // multi-value composition: the callee's leaves are our leaves
            compileCall locals extraLocals freeEnv fv args
        | _ ->
            // fallback: materialize once, then project
            let l = newTypedLocalOuter extraLocals "sv" "anyref"
            "(block (result " + (leaves |> List.map (fun (_, k, _) -> wasmTyOf2 k) |> String.concat " ") + ") "
            + "(local.set " + l + " " + recur e + ") "
            + (leaves |> List.map (fun (lp, _, _) -> leafGet rn ("(local.get " + l + ")") lp) |> String.concat " ")
            + ")"

    /// A direct call, expanding struct args into leaves where scalarized.
    and compileCall (locals : Dict<string * int, string>) (extraLocals : Vec<string * string>)
                    (freeEnv : Dict<string * int, int>) (v : VarId) (args : Expr list) : string =
        let recur = compileExpr locals extraLocals freeEnv false
        let fname = (dictTryFind topName (v.Path, v.Offset)).Value
        let pss, _ =
            match dictTryFind sigStructs (v.Path, v.Offset) with
            | Some x -> x
            | None -> List.replicate args.Length None, None
        let pks, _ =
            match dictTryFind sigKinds (v.Path, v.Offset) with
            | Some x -> x
            | None -> List.replicate args.Length "u", "u"
        let wrapped =
            args |> List.mapi (fun i a ->
                match (if i < pss.Length then List.item i pss else None) with
                | Some srn -> compileLeaves locals extraLocals freeEnv srn a
                | None ->
                    let k = if i < pks.Length then List.item i pks else "u"
                    if k = "u" then recur a else unboxK k (recur a))
        "(call " + fname + " " + String.concat " " wrapped + ")"

    and compilePat locals extraLocals freeEnv (out : System.Text.StringBuilder) (failLbl : string) (v : string) (p : Pat) : unit =
        compilePatWith (dictNew ()) locals extraLocals freeEnv out failLbl v p

    and compilePatWith (orSlots : Dict<string * int, string>) locals extraLocals freeEnv (out : System.Text.StringBuilder) (failLbl : string) (v : string) (p : Pat) : unit =
        let app (s : string) = out.Append(s + " ") |> ignore
        let newLocal (base_ : string) =
            let n = "$p" + string (vecLen extraLocals) + "_" + base_
            vecAdd extraLocals (n, "anyref")
            n
        match p with
        | PWild -> ()
        | POr _ ->
            // `expandOr` removes these before compilePat ever sees one; a
            // survivor would bind nothing and test nothing, silently
            emitError "an or-pattern reached pattern compilation"
        | PVar (var, _) ->
            // REUSE the slot if this variable is already bound in this
            // pattern position: or-alternatives bind the SAME identity
            // (lowering aligned them), so every alternative must write the
            // one slot the shared body reads
            let l =
                match dictTryFind orSlots (var.Path, var.Offset) with
                | Some existing -> existing
                | None ->
                    let fresh = newLocal "v"
                    dictSet locals (var.Path, var.Offset) fresh
                    fresh
            app ("(local.set " + l + " " + v + ")")
        | PAs (inner, var, _) ->
            let l = newLocal "as"
            dictSet locals (var.Path, var.Offset) l
            app ("(local.set " + l + " " + v + ")")
            compilePatWith orSlots locals extraLocals freeEnv out failLbl ("(local.get " + l + ")") inner
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
        | PLit LNull ->
            app ("(br_if " + failLbl + " (i32.eqz (ref.is_null " + v + ")))")
        | PTypeTest tn ->
            // the same checks a `:?` expression performs, in pattern form
            let idOf =
                "(struct.get $desc 0 (ref.cast (ref $desc) (struct.get $obj 0 (ref.cast (ref $obj) " + v + "))))"
            let classIdTest (classes : string list) =
                let hit =
                    match classes |> List.filter isObjRecord
                          |> List.map (fun c -> "(i32.eq " + idOf + " (i32.const " + string (descId c) + "))") with
                    | [] -> "(i32.const 0)"
                    | [ one ] -> one
                    | many -> many |> List.reduce (fun a b -> "(i32.or " + a + " " + b + ")")
                "(if (result i32) (ref.test (ref $obj) " + v + ") (then " + hit + ") (else (i32.const 0)))"
            let implementorsOf (iface : string) =
                classImpls
                |> List.filter (fun (_, impls) -> impls |> List.exists (fun (i, _) -> i = iface))
                |> List.collect (fun (cn, _) -> subclassesOf cn)
                |> List.distinct
            if tn = "list" then
                // nil is a null reference: null MATCHES `:? list`
                app ("(br_if " + failLbl + " (i32.eqz (i32.or (ref.is_null " + v + ") (ref.test (ref $cons) " + v + "))))")
            elif tn = "array" then
                app ("(br_if " + failLbl + " (i32.eqz (call $isArrayRep " + v + ")))")
            elif tn = "string" then
                app ("(br_if " + failLbl + " (i32.eqz (ref.test (ref $str) " + v + ")))")
            elif isObjRecord tn then
                app ("(br_if " + failLbl + " (ref.is_null " + v + "))")
                app ("(br_if " + failLbl + " (i32.eqz " + classIdTest (subclassesOf tn) + "))")
            elif interfaceDecls |> List.exists (fun (i, _) -> i = tn) then
                app ("(br_if " + failLbl + " (ref.is_null " + v + "))")
                app ("(br_if " + failLbl + " (i32.eqz " + classIdTest (implementorsOf tn) + "))")
            else
                vecAdd errors ("cannot type-test against " + tn + ": not a class")
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
                     compilePatWith orSlots locals extraLocals freeEnv out failLbl field a2)
             | None -> vecAdd errors ("unknown constructor pattern " + name))
        | PTuple ps ->
            let tn = "$tup" + string ps.Length
            ps |> List.iteri (fun i a ->
                let field = "(struct.get " + tn + " " + string i + " (ref.cast (ref " + tn + ") " + v + "))"
                compilePatWith orSlots locals extraLocals freeEnv out failLbl field a)
        | PCons (h, t) ->
            app ("(br_if " + failLbl + " (i32.eqz (ref.test (ref $cons) " + v + ")))")
            compilePatWith orSlots locals extraLocals freeEnv out failLbl ("(struct.get $cons 0 (ref.cast (ref $cons) " + v + "))") h
            compilePatWith orSlots locals extraLocals freeEnv out failLbl ("(struct.get $cons 1 (ref.cast (ref $cons) " + v + "))") t
        | PListLit ps ->
            let mutable cur = v
            for a in ps do
                app ("(br_if " + failLbl + " (i32.eqz (ref.test (ref $cons) " + cur + ")))")
                compilePatWith orSlots locals extraLocals freeEnv out failLbl ("(struct.get $cons 0 (ref.cast (ref $cons) " + cur + "))") a
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
            | EVarI (v, _, _) -> noteFree (v.Path, v.Offset)
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
            | EField (r, _, _) -> walk r
            | EFieldSet (r, _, _, v) -> walk r; walk v
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
        // a cell is captured AS the cell — dereferencing here would copy the
        // value and the closure's writes would be lost
        let captureW (k : string * int) =
            if (dictTryFind cellVars k).IsSome then
                match dictTryFind outerLocals k with
                | Some l -> "(local.get " + l + ")"
                | None ->
                    match dictTryFind outerFree k with
                    | Some idx ->
                        "(array.get $arr (ref.cast (ref $arr) (local.get $env)) (i32.const " + string idx + "))"
                    | None -> "(ref.null any)"
            else
                recurOuter (EVar ({ Path = fst k; Offset = snd k; Name = "_free" }, Fpp.Analysis.Types.mono (Fpp.Analysis.Types.TCon ("?", []))))
        // FLAT environment: one array, one indexed read per access. The
        // cons-chain form emitted k nested struct.gets for capture k, which
        // made the TEXT of closure-heavy functions quadratic — emitting the
        // compiler's own emitter ran out of memory on exactly that
        let envW =
            if List.isEmpty freeList then "(ref.null any)"
            else
                "(array.new_fixed $arr " + string (List.length freeList) + " "
                + String.concat " " (List.map captureW freeList) + ")"
        "(struct.new $clo (ref.func " + fname + ") " + envW + ")"

    // ---- module assembly --------------------------------------------------

    line "(module"
    line "  (type $u1 (func (param anyref anyref) (result anyref)))"
    line "  (type $clo (struct (field (ref $u1)) (field anyref)))"
    // one mutable slot: a mutable local that a closure captures lives here,
    // so the frame and the closure write to the same place
    line "  (type $cell (struct (field (mut anyref))))"
    line "  (type $cons (struct (field (mut anyref)) (field (mut anyref))))"
    line "  (type $str (array (mut i8)))"
    line "  (type $boxf (struct (field f64)))"
    // mutable so this stays a DIFFERENT heap type from $du0, which is also
    // one i32: wasm-GC canonicalizes identical shapes, and a nullary DU case
    // was being read as a boxed int
    line "  (type $boxi (struct (field (mut i32))))"
    line "  (type $arr (array (mut anyref)))"
    line "  (type $parr_i (array (mut i32)))"
    line "  (type $parr_f (array (mut f64)))"
    line "  (type $parr_s (array (mut f32)))"
    line "  (type $parr_l (array (mut i64)))"
    line "  (type $parr_h (array (mut i16)))"
    // the built-in seq iterator: (mode, a, b, index) — mode 0 walks a cons
    // chain in (a=current, b=rest), mode 1 indexes an array in (a, index)
    line "  (type $iter (struct (field i32) (field (mut anyref)) (field (mut anyref)) (field (mut i32))))"
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
    line "  (global $selfmark (ref $du0) (struct.new $du0 (i32.const -999)))"
    // identity numbers are handed out on first use and never reused
    line "  (global $nextid (mut i32) (i32.const 0))"

    // object model: every class instance starts with its descriptor, so
    // dispatch and downcasts can read it without knowing the class
    line "  (type $vt (array funcref))"
    line "  (type $desc (struct (field i32) (field (ref $vt))))"
    line "  (type $obj (sub (struct (field (mut anyref)))))"
    // one canonical function type per interface-method arity (receiver + args)
    let ifaceArities =
        classDecls
        |> List.collect (fun (cn, _, _, _) ->
            vtableSlots
            |> List.choose (fun (i, m) ->
                slotImpl cn i m |> Option.bind (fun v -> dictTryFind topArity (v.Path, v.Offset))))
        |> List.distinct
        |> List.sort
    for k in (if List.contains 1 ifaceArities then ifaceArities else 1 :: ifaceArities)
              |> (fun l -> if List.contains 2 l then l else 2 :: l)
              |> List.sort do
        line ("  (type $v" + string k + " (func " + String.concat " " (List.replicate k "(param anyref)") + " (result anyref)))")

    // program-declared types
    for rn, fs, st in records do
        // every field is declared mutable: classes assign to their state,
        // and wasm-GC needs the mutability in the type, not at the use site
        let fieldTy2 (fname : string) (k : string) =
            match fieldKindOf st fname k with
            | "f" -> "(field (mut f64))" | "s" -> "(field (mut f32))"
            | "l" -> "(field (mut i64))" | "i" -> "(field (mut i32))"
            | k2 when k2.StartsWith "S:" -> "(field (mut (ref $r_" + k2.Substring 2 + ")))"
            | _ -> "(field (mut anyref))"
        let fields = fs |> List.map (fun (f, k) -> fieldTy2 f k) |> String.concat " "
        if isObjRecord rn then
            let super = match baseOf rn with Some b when b <> rn -> "$r_" + b | _ -> "$obj"
            line ("  (type $r_" + rn + " (sub " + super + " (struct " + fields + ")))")
        else line ("  (type $r_" + rn + " (struct " + fields + "))")
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

    // Generated identity. A record compares and hashes over its fields; a
    // class is its own identity unless it overrides. Both are reached
    // through the descriptor, so a value of unknown type still resolves.
    for rn, fs, st in records do
      if not st && isObjRecord rn then
        let fieldIdx = fs |> List.mapi (fun i (f, _) -> i, f) |> List.filter (fun (_, f) -> f <> "__desc")
        let cast (v : string) = "(ref.cast (ref $r_" + rn + ") " + v + ")"
        if isClassName rn then
            // reference identity: a class is equal only to itself
            line ("  (func $eq_" + rn + " (param $a anyref) (param $b anyref) (result anyref)"
                  + " (ref.i31 (ref.eq (ref.cast (ref null eq) (local.get $a)) (ref.cast (ref null eq) (local.get $b)))))")
            // A per-OBJECT identity number, handed out on first use and kept
            // in the object. wasm-GC exposes no address and no identity of
            // its own — `ref.eq` compares, it does not number — because a
            // moving collector would invalidate anything address-derived.
            // This is what the JVM and .NET do for the same reason.
            line ("  (func $hash_" + rn + " (param $v anyref) (result anyref) (local $h i32)")
            line ("    (local.set $h (struct.get $r_" + rn + " 1 (ref.cast (ref $r_" + rn + ") (local.get $v))))")
            line ("    (if (i32.eqz (local.get $h))")
            line ("      (then")
            line ("        (global.set $nextid (i32.add (global.get $nextid) (i32.const 1)))")
            line ("        (local.set $h (global.get $nextid))")
            line ("        (struct.set $r_" + rn + " 1 (ref.cast (ref $r_" + rn + ") (local.get $v)) (local.get $h))))")
            // spread the sequential ids so they do not cluster in a table
            line ("    (ref.i31 (i32.mul (local.get $h) (i32.const -1640531527))))")
        else
            let cmp =
                fieldIdx
                |> List.map (fun (i, _) ->
                    "(i32.eqz (i31.get_s (ref.cast (ref i31) (call $equal (struct.get $r_" + rn + " " + string i
                    + " " + cast "(local.get $a)" + ") (struct.get $r_" + rn + " " + string i + " " + cast "(local.get $b)" + ")))))")
                |> List.map (fun c -> "(if " + c + " (then (return (ref.i31 (i32.const 0)))))")
            line ("  (func $eq_" + rn + " (param $a anyref) (param $b anyref) (result anyref) "
                  + String.concat " " cmp + " (ref.i31 (i32.const 1)))")
            let h =
                fieldIdx
                |> List.map (fun (i, _) ->
                    "(call $hashv (struct.get $r_" + rn + " " + string i + " " + cast "(local.get $v)" + "))")
            let folded =
                match h with
                | [] -> "(i32.const " + string (descId rn) + ")"
                | first :: rest ->
                    rest |> List.fold (fun acc x -> "(i32.add (i32.mul " + acc + " (i32.const 31)) " + x + ")") first
            line ("  (func $hash_" + rn + " (param $v anyref) (result anyref) (ref.i31 " + folded + "))")

    // per-class descriptor: class id plus the vtable, one slot per
    // (interface, method) in the whole program
    let identityAdapters = vecNew<string * int * string> ()
    for cn in objRecordNames do
        let identity =
            [ "Equals", "$eq_" + cn, 2; "GetHashCode", "$hash_" + cn, 1 ]
            |> List.map (fun (mname, generated, wantArity) ->
                match identityImpl cn mname with
                | Some v ->
                    (match dictTryFind topName (v.Path, v.Offset) with
                     | Some fn ->
                         // `GetHashCode()` is written with a unit argument, so
                         // its arity does not match the slot; adapt it
                         let actual = match dictTryFind topArity (v.Path, v.Offset) with Some a -> a | None -> wantArity
                         if actual = wantArity then "(ref.func " + fn + ")"
                         elif actual = wantArity + 1 then
                             let ad = "$adapt" + string wantArity + "_" + cn + "_" + mname
                             vecAdd identityAdapters (ad, wantArity, fn)
                             "(ref.func " + ad + ")"
                         else "(ref.func " + generated + ")"
                     | None -> "(ref.func " + generated + ")")
                | None -> "(ref.func " + generated + ")")
        let slots =
            vtableSlots
            |> List.map (fun (i, m) ->
                match slotImpl cn i m with
                | Some v ->
                    (match dictTryFind topName (v.Path, v.Offset) with
                     | Some fn -> "(ref.func " + fn + ")"
                     | None -> "(ref.null func)")
                | None -> "(ref.null func)")
        let slots = identity @ slots
        let vt =
            if List.isEmpty slots then "(array.new_fixed $vt 0)"
            else "(array.new_fixed $vt " + string slots.Length + " " + String.concat " " slots + ")"
        line ("  (global $desc_" + cn + " (ref $desc) (struct.new $desc (i32.const "
              + string (descId cn) + ") " + vt + "))")

    // A union's identity: structural by default (tag, then payload), or the
    // union's own override. Indexed by case tag, which is globally unique.
    line "  (func $eq_du_default (param $a anyref) (param $b anyref) (result anyref)"
    line "    (if (i32.and (ref.test (ref $du1) (local.get $a)) (ref.test (ref $du1) (local.get $b)))"
    line "      (then (return (call $equal (struct.get $du1 1 (ref.cast (ref $du1) (local.get $a)))"
    line "                                (struct.get $du1 1 (ref.cast (ref $du1) (local.get $b)))))))"
    line "    (ref.i31 (i32.const 1)))"
    line "  (func $hash_du_default (param $v anyref) (result anyref)"
    line "    (if (ref.test (ref $du1) (local.get $v))"
    line "      (then (return (ref.i31 (i32.add"
    line "        (i32.mul (struct.get $du1 0 (ref.cast (ref $du1) (local.get $v))) (i32.const 31))"
    line "        (call $hashv (struct.get $du1 1 (ref.cast (ref $du1) (local.get $v)))))))))"
    line "    (ref.i31 (struct.get $du0 0 (ref.cast (ref $du0) (local.get $v)))))"
    let tagCount = (dictPairs caseTag |> List.map snd |> List.fold max (-1)) + 1
    let duSlot (which : string) (dflt : string) (wantArity : int) =
        List.init tagCount (fun t ->
            let owner =
                dictPairs caseTag
                |> List.tryPick (fun (c, tg) -> if tg = t then dictTryFind caseOwner c else None)
            match owner |> Option.bind (fun o -> identityImpl o which) with
            | Some v ->
                (match dictTryFind topName (v.Path, v.Offset) with
                 | Some fn ->
                     let actual = match dictTryFind topArity (v.Path, v.Offset) with Some a -> a | None -> wantArity
                     if actual = wantArity then "(ref.func " + fn + ")"
                     elif actual = wantArity + 1 then
                         let ad = "$adaptdu" + string wantArity + "_" + string t
                         vecAdd identityAdapters (ad, wantArity, fn)
                         "(ref.func " + ad + ")"
                     else "(ref.func " + dflt + ")"
                 | None -> "(ref.func " + dflt + ")")
            | None -> "(ref.func " + dflt + ")")
    if tagCount > 0 then
        line ("  (global $duEq (ref $vt) (array.new_fixed $vt " + string tagCount + " "
              + String.concat " " (duSlot "Equals" "$eq_du_default" 2) + "))")
        line ("  (global $duHash (ref $vt) (array.new_fixed $vt " + string tagCount + " "
              + String.concat " " (duSlot "GetHashCode" "$hash_du_default" 1) + "))")
    else
        line "  (global $duEq (ref $vt) (array.new_fixed $vt 1 (ref.func $eq_du_default)))"
        line "  (global $duHash (ref $vt) (array.new_fixed $vt 1 (ref.func $hash_du_default)))"

    for ad, arity, target in vecToList identityAdapters do
        let ps = List.init arity (fun i -> "(param $p" + string i + " anyref)") |> String.concat " "
        let args = List.init arity (fun i -> "(local.get $p" + string i + ")") |> String.concat " "
        line ("  (func " + ad + " " + ps + " (result anyref) (call " + target + " " + args
              + " (ref.i31 (i32.const 0))))")

    // runtime: putc, print, itoa, equal, append, apply
    let runtimeSrc = """  (func $putc (param $c i32)
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
  (func $printiu (param $n i32)
    (local $m i32)
    (local.set $m (i32.div_u (local.get $n) (i32.const 10)))
    (if (i32.gt_u (local.get $m) (i32.const 0)) (then (call $printiu (local.get $m))))
    (call $putc (i32.add (i32.const 48) (i32.rem_u (local.get $n) (i32.const 10)))))
  (func $printu (param $v anyref)
    (if (ref.test (ref i31) (local.get $v))
      (then (call $printiu (i31.get_s (ref.cast (ref i31) (local.get $v)))) (return)))
    (if (ref.test (ref $boxi) (local.get $v))
      (then (call $printiu (struct.get $boxi 0 (ref.cast (ref $boxi) (local.get $v)))) (return)))
    (call $printval (local.get $v)))
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
    ;; null equals only null
    (if (i32.or (ref.is_null (local.get $a)) (ref.is_null (local.get $b)))
      (then (return (ref.i31 (i32.and (ref.is_null (local.get $a)) (ref.is_null (local.get $b)))))))
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
    ;; Any reference type: descriptors are per-type, so two values whose
    ;; descriptors differ are of different types and cannot be equal. That
    ;; is what makes this sound where a shape test is not — wasm-GC
    ;; canonicalizes same-shaped structs into ONE heap type.
    (if (i32.and (ref.test (ref $obj) (local.get $a)) (ref.test (ref $obj) (local.get $b)))
      (then
        (if (i32.eqz (ref.eq
              (ref.cast (ref null eq) (struct.get $obj 0 (ref.cast (ref $obj) (local.get $a))))
              (ref.cast (ref null eq) (struct.get $obj 0 (ref.cast (ref $obj) (local.get $b))))))
          (then (return (ref.i31 (i32.const 0)))))
        (return (call_ref $v2 (local.get $a) (local.get $b)
          (ref.cast (ref $v2) (array.get $vt
            (struct.get $desc 1 (ref.cast (ref $desc) (struct.get $obj 0 (ref.cast (ref $obj) (local.get $a)))))
            (i32.const 0)))))))
    ;; tuples: $tupN is a distinct type per arity, so this cannot confuse
    ;; two different shapes
TUPLE_EQ
    ;; DU cases: the tag is globally unique, so equal tags are the same case,
    ;; and a table indexed by tag is a DU's equivalent of a vtable — which is
    ;; how an Equals override on a union is reached.
    (if (i32.and (ref.test (ref $du0) (local.get $a)) (ref.test (ref $du0) (local.get $b)))
      (then
        (if (i32.ne (struct.get $du0 0 (ref.cast (ref $du0) (local.get $a)))
                    (struct.get $du0 0 (ref.cast (ref $du0) (local.get $b))))
          (then (return (ref.i31 (i32.const 0)))))
        (return (call_ref $v2 (local.get $a) (local.get $b) (ref.cast (ref $v2)
          (array.get $vt (global.get $duEq) (struct.get $du0 0 (ref.cast (ref $du0) (local.get $a)))))))))
    (if (i32.and (ref.test (ref $du1) (local.get $a)) (ref.test (ref $du1) (local.get $b)))
      (then
        (if (i32.ne (struct.get $du1 0 (ref.cast (ref $du1) (local.get $a)))
                    (struct.get $du1 0 (ref.cast (ref $du1) (local.get $b))))
          (then (return (ref.i31 (i32.const 0)))))
        (return (call_ref $v2 (local.get $a) (local.get $b) (ref.cast (ref $v2)
          (array.get $vt (global.get $duEq) (struct.get $du1 0 (ref.cast (ref $du1) (local.get $a)))))))))
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
  ;; .Length where the element representation is not statically known: the
  ;; two generic call sites referenced this WITHOUT it existing, so any
  ;; module reaching them failed validation
  (func $lenv (param $v anyref) (result anyref)
    (if (ref.test (ref $arr) (local.get $v))
      (then (return (call $ofi (array.len (ref.cast (ref $arr) (local.get $v)))))))
    (if (ref.test (ref $parr_i) (local.get $v))
      (then (return (call $ofi (array.len (ref.cast (ref $parr_i) (local.get $v)))))))
    (if (ref.test (ref $parr_f) (local.get $v))
      (then (return (call $ofi (array.len (ref.cast (ref $parr_f) (local.get $v)))))))
    (if (ref.test (ref $parr_s) (local.get $v))
      (then (return (call $ofi (array.len (ref.cast (ref $parr_s) (local.get $v)))))))
    (if (ref.test (ref $parr_l) (local.get $v))
      (then (return (call $ofi (array.len (ref.cast (ref $parr_l) (local.get $v)))))))
    (if (ref.test (ref $parr_h) (local.get $v))
      (then (return (call $ofi (array.len (ref.cast (ref $parr_h) (local.get $v)))))))
    (if (ref.test (ref $str) (local.get $v))
      (then (return (call $ofi (array.len (ref.cast (ref $str) (local.get $v)))))))
    (ref.i31 (i32.const 0)))
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
    (if (ref.test (ref $obj) (local.get $v))
      (then (return (i31.get_s (ref.cast (ref i31) (call_ref $v1 (local.get $v)
        (ref.cast (ref $v1) (array.get $vt
          (struct.get $desc 1 (ref.cast (ref $desc) (struct.get $obj 0 (ref.cast (ref $obj) (local.get $v)))))
          (i32.const 1)))))))))
    ;; Arrays hash to their LENGTH: identity equality only obliges equal
    ;; values to hash equally, and length is the one thing about an array
    ;; that writes to its elements cannot change. See DIVERGENCES.md.
    (if (ref.test (ref $arr) (local.get $v))
      (then (return (array.len (ref.cast (ref $arr) (local.get $v))))))
    (if (ref.test (ref $parr_i) (local.get $v))
      (then (return (array.len (ref.cast (ref $parr_i) (local.get $v))))))
    (if (ref.test (ref $parr_f) (local.get $v))
      (then (return (array.len (ref.cast (ref $parr_f) (local.get $v))))))
    (if (ref.test (ref $parr_s) (local.get $v))
      (then (return (array.len (ref.cast (ref $parr_s) (local.get $v))))))
    (if (ref.test (ref $parr_l) (local.get $v))
      (then (return (array.len (ref.cast (ref $parr_l) (local.get $v))))))
    (if (ref.test (ref $parr_h) (local.get $v))
      (then (return (array.len (ref.cast (ref $parr_h) (local.get $v))))))
TUPLE_HASH
    (if (ref.test (ref $du0) (local.get $v))
      (then (return (i31.get_s (ref.cast (ref i31) (call_ref $v1 (local.get $v) (ref.cast (ref $v1)
        (array.get $vt (global.get $duHash) (struct.get $du0 0 (ref.cast (ref $du0) (local.get $v)))))))))))
    (if (ref.test (ref $du1) (local.get $v))
      (then (return (i31.get_s (ref.cast (ref i31) (call_ref $v1 (local.get $v) (ref.cast (ref $v1)
        (array.get $vt (global.get $duHash) (struct.get $du1 0 (ref.cast (ref $du1) (local.get $v)))))))))))
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
  (func $cmpv (param $a anyref) (param $b anyref) (result i32)
    (local $i i32) (local $la i32) (local $lb i32) (local $x i32) (local $y i32) (local $c i32)
    (if (i32.and (ref.test (ref $str) (local.get $a)) (ref.test (ref $str) (local.get $b)))
      (then
        (local.set $la (array.len (ref.cast (ref $str) (local.get $a))))
        (local.set $lb (array.len (ref.cast (ref $str) (local.get $b))))
        (block $d (loop $go
          (br_if $d (i32.or (i32.ge_u (local.get $i) (local.get $la))
                            (i32.ge_u (local.get $i) (local.get $lb))))
          (local.set $x (array.get_u $str (ref.cast (ref $str) (local.get $a)) (local.get $i)))
          (local.set $y (array.get_u $str (ref.cast (ref $str) (local.get $b)) (local.get $i)))
          (if (i32.lt_u (local.get $x) (local.get $y)) (then (return (i32.const -1))))
          (if (i32.gt_u (local.get $x) (local.get $y)) (then (return (i32.const 1))))
          (local.set $i (i32.add (local.get $i) (i32.const 1)))
          (br $go)))
        (if (i32.lt_u (local.get $la) (local.get $lb)) (then (return (i32.const -1))))
        (if (i32.gt_u (local.get $la) (local.get $lb)) (then (return (i32.const 1))))
        (return (i32.const 0))))
    (if (i32.and (ref.test (ref $boxf) (local.get $a)) (ref.test (ref $boxf) (local.get $b)))
      (then
        (if (f64.lt (struct.get $boxf 0 (ref.cast (ref $boxf) (local.get $a)))
                    (struct.get $boxf 0 (ref.cast (ref $boxf) (local.get $b))))
          (then (return (i32.const -1))))
        (if (f64.gt (struct.get $boxf 0 (ref.cast (ref $boxf) (local.get $a)))
                    (struct.get $boxf 0 (ref.cast (ref $boxf) (local.get $b))))
          (then (return (i32.const 1))))
        (return (i32.const 0))))
    (if (i32.and (ref.is_null (local.get $a)) (ref.is_null (local.get $b)))
      (then (return (i32.const 0))))
    (if (ref.is_null (local.get $a)) (then (return (i32.const -1))))
    (if (ref.is_null (local.get $b)) (then (return (i32.const 1))))
    (if (i32.and (ref.test (ref $cons) (local.get $a)) (ref.test (ref $cons) (local.get $b)))
      (then
        (local.set $c (call $cmpv (struct.get $cons 0 (ref.cast (ref $cons) (local.get $a)))
                                  (struct.get $cons 0 (ref.cast (ref $cons) (local.get $b)))))
        (if (i32.ne (local.get $c) (i32.const 0)) (then (return (local.get $c))))
        (return (call $cmpv (struct.get $cons 1 (ref.cast (ref $cons) (local.get $a)))
                            (struct.get $cons 1 (ref.cast (ref $cons) (local.get $b)))))))
    ;; numeric / immediates
    (local.set $x (call $toi (local.get $a)))
    (local.set $y (call $toi (local.get $b)))
    (if (i32.lt_s (local.get $x) (local.get $y)) (then (return (i32.const -1))))
    (if (i32.gt_s (local.get $x) (local.get $y)) (then (return (i32.const 1))))
    (i32.const 0))
  (func $append (param $a anyref) (param $b anyref) (result anyref)
    (if (result anyref) (ref.test (ref $cons) (local.get $a))
      (then (struct.new $cons
        (struct.get $cons 0 (ref.cast (ref $cons) (local.get $a)))
        (call $append (struct.get $cons 1 (ref.cast (ref $cons) (local.get $a))) (local.get $b))))
      (else (local.get $b))))
  ;; int -> decimal string
  (func $ndigits (param $n i32) (result i32)
    (local $c i32) (local $m i32)
    (local.set $m (local.get $n))
    (if (i32.lt_s (local.get $m) (i32.const 0))
      (then (local.set $c (i32.const 1)) (local.set $m (i32.sub (i32.const 0) (local.get $m))))
      (else (local.set $c (i32.const 0))))
    (local.set $c (i32.add (local.get $c) (i32.const 1)))
    (block $done
      (loop $go
        (local.set $m (i32.div_u (local.get $m) (i32.const 10)))
        (br_if $done (i32.eqz (local.get $m)))
        (local.set $c (i32.add (local.get $c) (i32.const 1)))
        (br $go)))
    (local.get $c))
  (func $itoa (param $n i32) (result anyref)
    (local $len i32) (local $s (ref $str)) (local $i i32) (local $m i32) (local $neg i32)
    (local.set $len (call $ndigits (local.get $n)))
    (local.set $s (array.new $str (i32.const 48) (local.get $len)))
    (local.set $m (local.get $n))
    (if (i32.lt_s (local.get $m) (i32.const 0))
      (then (local.set $neg (i32.const 1))
            (local.set $m (i32.sub (i32.const 0) (local.get $m)))
            (array.set $str (local.get $s) (i32.const 0) (i32.const 45))))
    (local.set $i (i32.sub (local.get $len) (i32.const 1)))
    (block $done
      (loop $go
        (array.set $str (local.get $s) (local.get $i)
          (i32.add (i32.const 48) (i32.rem_u (local.get $m) (i32.const 10))))
        (local.set $m (i32.div_u (local.get $m) (i32.const 10)))
        (local.set $i (i32.sub (local.get $i) (i32.const 1)))
        (br_if $done (i32.eqz (local.get $m)))
        (br_if $done (i32.lt_s (local.get $i) (local.get $neg)))
        (br $go)))
    (local.get $s))
  (func $strsub (param $s (ref $str)) (param $start i32) (param $len i32) (result anyref)
    (local $r (ref $str)) (local $i i32)
    (local.set $r (array.new_default $str (local.get $len)))
    (block $d (loop $l
      (br_if $d (i32.ge_u (local.get $i) (local.get $len)))
      (array.set $str (local.get $r) (local.get $i)
        (array.get_u $str (local.get $s) (i32.add (local.get $start) (local.get $i))))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $l)))
    (local.get $r))
  ;; ---- builtin string members ------------------------------------------
  ;; .NET semantics, deliberately: an empty needle is found at `from`, a
  ;; missing one is -1, Replace scans left to right without overlapping.
  (func $strFind (param $s (ref $str)) (param $p (ref $str)) (param $from i32) (result i32)
    (local $i i32) (local $j i32) (local $ls i32) (local $lp i32)
    (local.set $ls (array.len (local.get $s)))
    (local.set $lp (array.len (local.get $p)))
    (local.set $i (local.get $from))
    (if (i32.lt_s (local.get $i) (i32.const 0)) (then (local.set $i (i32.const 0))))
    (if (i32.eqz (local.get $lp)) (then (return (select (local.get $i) (local.get $ls)
                                                        (i32.le_s (local.get $i) (local.get $ls))))))
    (block $done
      (loop $outer
        (br_if $done (i32.gt_s (i32.add (local.get $i) (local.get $lp)) (local.get $ls)))
        (local.set $j (i32.const 0))
        (block $mismatch
          (loop $inner
            (if (i32.ge_u (local.get $j) (local.get $lp)) (then (return (local.get $i))))
            (br_if $mismatch (i32.ne (array.get_u $str (local.get $s) (i32.add (local.get $i) (local.get $j)))
                                     (array.get_u $str (local.get $p) (local.get $j))))
            (local.set $j (i32.add (local.get $j) (i32.const 1)))
            (br $inner)))
        (local.set $i (i32.add (local.get $i) (i32.const 1)))
        (br $outer)))
    (i32.const -1))
  (func $strFindChar (param $s (ref $str)) (param $c i32) (result i32)
    (local $i i32)
    (block $done (loop $go
      (br_if $done (i32.ge_u (local.get $i) (array.len (local.get $s))))
      (if (i32.eq (array.get_u $str (local.get $s) (local.get $i)) (local.get $c))
        (then (return (local.get $i))))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $go)))
    (i32.const -1))
  (func $strLastFindChar (param $s (ref $str)) (param $c i32) (result i32)
    (local $i i32)
    (local.set $i (array.len (local.get $s)))
    (block $done (loop $go
      (br_if $done (i32.eqz (local.get $i)))
      (local.set $i (i32.sub (local.get $i) (i32.const 1)))
      (if (i32.eq (array.get_u $str (local.get $s) (local.get $i)) (local.get $c))
        (then (return (local.get $i))))
      (br $go)))
    (i32.const -1))
  (func $strStarts (param $s (ref $str)) (param $p (ref $str)) (result i32)
    (local $i i32)
    (if (i32.gt_u (array.len (local.get $p)) (array.len (local.get $s))) (then (return (i32.const 0))))
    (block $done (loop $go
      (br_if $done (i32.ge_u (local.get $i) (array.len (local.get $p))))
      (if (i32.ne (array.get_u $str (local.get $s) (local.get $i))
                  (array.get_u $str (local.get $p) (local.get $i)))
        (then (return (i32.const 0))))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $go)))
    (i32.const 1))
  (func $strEnds (param $s (ref $str)) (param $p (ref $str)) (result i32)
    (local $i i32) (local $off i32)
    (if (i32.gt_u (array.len (local.get $p)) (array.len (local.get $s))) (then (return (i32.const 0))))
    (local.set $off (i32.sub (array.len (local.get $s)) (array.len (local.get $p))))
    (block $done (loop $go
      (br_if $done (i32.ge_u (local.get $i) (array.len (local.get $p))))
      (if (i32.ne (array.get_u $str (local.get $s) (i32.add (local.get $off) (local.get $i)))
                  (array.get_u $str (local.get $p) (local.get $i)))
        (then (return (i32.const 0))))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $go)))
    (i32.const 1))
  ;; n+1 pieces for n separators — "a,b," splits to "a", "b", ""
  (func $strSplitChar (param $s (ref $str)) (param $c i32) (result anyref)
    (local $n i32) (local $i i32) (local $start i32) (local $k i32) (local $r (ref $arr))
    (local.set $n (i32.const 1))
    (block $cd (loop $cg
      (br_if $cd (i32.ge_u (local.get $i) (array.len (local.get $s))))
      (if (i32.eq (array.get_u $str (local.get $s) (local.get $i)) (local.get $c))
        (then (local.set $n (i32.add (local.get $n) (i32.const 1)))))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $cg)))
    (local.set $r (array.new_default $arr (local.get $n)))
    (local.set $i (i32.const 0))
    (block $sd (loop $sg
      (br_if $sd (i32.ge_u (local.get $i) (array.len (local.get $s))))
      (if (i32.eq (array.get_u $str (local.get $s) (local.get $i)) (local.get $c))
        (then
          (array.set $arr (local.get $r) (local.get $k)
            (call $strsub (local.get $s) (local.get $start) (i32.sub (local.get $i) (local.get $start))))
          (local.set $k (i32.add (local.get $k) (i32.const 1)))
          (local.set $start (i32.add (local.get $i) (i32.const 1)))))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $sg)))
    (array.set $arr (local.get $r) (local.get $k)
      (call $strsub (local.get $s) (local.get $start) (i32.sub (array.len (local.get $s)) (local.get $start))))
    (local.get $r))
  (func $strReplace (param $s (ref $str)) (param $a (ref $str)) (param $b (ref $str)) (result anyref)
    (local $i i32) (local $at i32) (local $acc anyref)
    (local.set $acc (array.new_default $str (i32.const 0)))
    (if (i32.eqz (array.len (local.get $a))) (then (return (local.get $s))))
    (block $done (loop $go
      (local.set $at (call $strFind (local.get $s) (local.get $a) (local.get $i)))
      (br_if $done (i32.lt_s (local.get $at) (i32.const 0)))
      (local.set $acc (call $strcat (ref.cast (ref $str) (local.get $acc))
        (ref.cast (ref $str) (call $strsub (local.get $s) (local.get $i) (i32.sub (local.get $at) (local.get $i))))))
      (local.set $acc (call $strcat (ref.cast (ref $str) (local.get $acc)) (local.get $b)))
      ;; past the match, never into it: replacements do not overlap
      (local.set $i (i32.add (local.get $at) (array.len (local.get $a))))
      (br $go)))
    (call $strcat (ref.cast (ref $str) (local.get $acc))
      (ref.cast (ref $str) (call $strsub (local.get $s) (local.get $i)
        (i32.sub (array.len (local.get $s)) (local.get $i))))))
  (func $strIsWs (param $c i32) (result i32)
    (i32.or (i32.eq (local.get $c) (i32.const 32))
      (i32.or (i32.eq (local.get $c) (i32.const 9))
        (i32.or (i32.eq (local.get $c) (i32.const 10))
          (i32.or (i32.eq (local.get $c) (i32.const 13))
            (i32.or (i32.eq (local.get $c) (i32.const 11)) (i32.eq (local.get $c) (i32.const 12))))))))
  (func $strTrim (param $s (ref $str)) (result anyref)
    (local $a i32) (local $b i32)
    (local.set $b (array.len (local.get $s)))
    (block $ld (loop $lg
      (br_if $ld (i32.ge_u (local.get $a) (local.get $b)))
      (br_if $ld (i32.eqz (call $strIsWs (array.get_u $str (local.get $s) (local.get $a)))))
      (local.set $a (i32.add (local.get $a) (i32.const 1))) (br $lg)))
    (block $rd (loop $rg
      (br_if $rd (i32.ge_u (local.get $a) (local.get $b)))
      (br_if $rd (i32.eqz (call $strIsWs (array.get_u $str (local.get $s) (i32.sub (local.get $b) (i32.const 1))))))
      (local.set $b (i32.sub (local.get $b) (i32.const 1))) (br $rg)))
    (call $strsub (local.get $s) (local.get $a) (i32.sub (local.get $b) (local.get $a))))
  ;; TrimEnd over a char ARRAY: chars are POD, so the array is packed i32
  (func $strTrimEndChars (param $s (ref $str)) (param $cs anyref) (result anyref)
    (local $b i32) (local $j i32) (local $hit i32) (local $ca (ref $parr_i)) (local $c i32)
    (local.set $ca (ref.cast (ref $parr_i) (local.get $cs)))
    (local.set $b (array.len (local.get $s)))
    (block $done (loop $go
      (br_if $done (i32.eqz (local.get $b)))
      (local.set $c (array.get_u $str (local.get $s) (i32.sub (local.get $b) (i32.const 1))))
      (local.set $hit (i32.const 0))
      (local.set $j (i32.const 0))
      (block $sd (loop $sg
        (br_if $sd (i32.ge_u (local.get $j) (array.len (local.get $ca))))
        (if (i32.eq (array.get $parr_i (local.get $ca) (local.get $j)) (local.get $c))
          (then (local.set $hit (i32.const 1)) (br $sd)))
        (local.set $j (i32.add (local.get $j) (i32.const 1))) (br $sg)))
      (br_if $done (i32.eqz (local.get $hit)))
      (local.set $b (i32.sub (local.get $b) (i32.const 1)))
      (br $go)))
    (call $strsub (local.get $s) (i32.const 0) (local.get $b)))
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
  ;; ---- float16 ----------------------------------------------------------
  ;; wasm has no f16, so a half is carried as its 16 BIT PATTERN in an i31 —
  ;; allocation-free, like an int — and every operation widens to f32, works
  ;; there, and rounds back. That single rounding is CORRECT: f32 carries 24
  ;; significand bits and f16 needs 11, and double rounding is innocuous once
  ;; the wider format has at least 2p+2, which 24 exactly is. So +, -, *, /
  ;; and sqrt on halves agree bit-for-bit with native f16 hardware.
  (func $h2f (param $h i32) (result f32)
    (local $exp i32) (local $man i32) (local $sgn f32)
    (local.set $exp (i32.and (i32.shr_u (local.get $h) (i32.const 10)) (i32.const 0x1f)))
    (local.set $man (i32.and (local.get $h) (i32.const 0x3ff)))
    (local.set $sgn (select (f32.const -1) (f32.const 1)
                            (i32.and (i32.shr_u (local.get $h) (i32.const 15)) (i32.const 1))))
    (if (i32.eq (local.get $exp) (i32.const 0))
      (then
        ;; zero or subnormal: the value is mantissa * 2^-24, exact in f32
        (return (f32.mul (local.get $sgn)
                         (f32.mul (f32.convert_i32_u (local.get $man))
                                  (f32.const 0x1p-24))))))
    (if (i32.eq (local.get $exp) (i32.const 0x1f))
      (then
        ;; infinity or NaN: rebuild with f32's exponent and a shifted payload
        (return (f32.reinterpret_i32
                  (i32.or (i32.shl (i32.and (i32.shr_u (local.get $h) (i32.const 15)) (i32.const 1))
                                   (i32.const 31))
                          (i32.or (i32.const 0x7f800000)
                                  (i32.shl (local.get $man) (i32.const 13))))))))
    (f32.reinterpret_i32
      (i32.or (i32.shl (i32.and (i32.shr_u (local.get $h) (i32.const 15)) (i32.const 1)) (i32.const 31))
              (i32.or (i32.shl (i32.add (local.get $exp) (i32.const 112)) (i32.const 23))
                      (i32.shl (local.get $man) (i32.const 13))))))
  ;; round-to-nearest-even, including the subnormal range, where adding a
  ;; magic constant makes the float unit do the rounding for us
  (func $f2h (param $f f32) (result i32)
    (local $u i32) (local $sign i32) (local $o i32)
    (local.set $u (i32.reinterpret_f32 (local.get $f)))
    (local.set $sign (i32.and (local.get $u) (i32.const 0x80000000)))
    (local.set $u (i32.xor (local.get $u) (local.get $sign)))
    (if (i32.ge_u (local.get $u) (i32.const 0x47800000))
      (then
        ;; NaN keeps a payload bit so it stays a NaN; anything else saturates
        (local.set $o (select (i32.const 0x7e00) (i32.const 0x7c00)
                              (i32.gt_u (local.get $u) (i32.const 0x7f800000)))))
      (else
        (if (i32.lt_u (local.get $u) (i32.const 0x38800000))
          (then
            (local.set $o
              (i32.sub (i32.reinterpret_f32
                         (f32.add (f32.reinterpret_i32 (local.get $u)) (f32.const 0.5)))
                       (i32.const 0x3f000000))))
          (else
            ;; ties-to-even: bias by half an ulp, plus one when already odd
            (local.set $u
              (i32.add (local.get $u)
                       (i32.add (i32.const 0xfff)
                                (i32.and (i32.shr_u (local.get $u) (i32.const 13)) (i32.const 1)))))
            ;; shift into place AND rebias: f32 biases by 127, f16 by 15,
            ;; so the exponent field moves down by (127-15) << 10
            (local.set $o (i32.sub (i32.shr_u (local.get $u) (i32.const 13))
                                   (i32.const 0x1c000)))))))
    (i32.or (i32.shr_u (local.get $sign) (i32.const 16)) (local.get $o)))
  ;; double -> half in ONE step. Going through f32 would round twice, and
  ;; that is observable: 2.98023224e-08 sits just above the tie between 0 and
  ;; the smallest subnormal half, but is exactly the tie once narrowed to f32,
  ;; so the two routes disagree.
  (func $f2h64 (param $v f64) (result i32)
    (local $u i64) (local $mag i64) (local $sign i32) (local $o i32)
    (local.set $u (i64.reinterpret_f64 (local.get $v)))
    (local.set $sign (i32.wrap_i64
                       (i64.shr_u (i64.and (local.get $u) (i64.const 0x8000000000000000))
                                  (i64.const 48))))
    (local.set $mag (i64.and (local.get $u) (i64.const 0x7fffffffffffffff)))
    (if (i64.ge_u (local.get $mag) (i64.const 0x40f0000000000000))
      (then
        (local.set $o (select (i32.const 0x7e00) (i32.const 0x7c00)
                              (i64.gt_u (local.get $mag) (i64.const 0x7ff0000000000000)))))
      (else
        (if (i64.lt_u (local.get $mag) (i64.const 0x3f10000000000000))
          (then
            ;; adding 2^28 puts the half's last bit at the double's last bit,
            ;; so the float unit does the rounding
            (local.set $o
              (i32.wrap_i64
                (i64.sub (i64.reinterpret_f64
                           (f64.add (f64.reinterpret_i64 (local.get $mag)) (f64.const 268435456)))
                         (i64.const 0x41b0000000000000)))))
          (else
            ;; ties-to-even at bit 42, then rebias 1023 -> 15
            (local.set $mag
              (i64.add (local.get $mag)
                       (i64.add (i64.const 0x1ffffffffff)
                                (i64.and (i64.shr_u (local.get $mag) (i64.const 42)) (i64.const 1)))))
            (local.set $o
              (i32.wrap_i64 (i64.sub (i64.shr_u (local.get $mag) (i64.const 42))
                                     (i64.const 1032192))))))))
    (i32.or (local.get $sign) (local.get $o)))
  (func $strcmp (param $a (ref $str)) (param $b (ref $str)) (result i32)
    (local $i i32) (local $la i32) (local $lb i32) (local $ca i32) (local $cb i32)
    (local.set $la (array.len (local.get $a)))
    (local.set $lb (array.len (local.get $b)))
    (block $done (loop $go
      ;; one operand exhausted: the shorter string sorts first
      (br_if $done (i32.or (i32.ge_u (local.get $i) (local.get $la))
                           (i32.ge_u (local.get $i) (local.get $lb))))
      (local.set $ca (array.get_u $str (local.get $a) (local.get $i)))
      (local.set $cb (array.get_u $str (local.get $b) (local.get $i)))
      (if (i32.ne (local.get $ca) (local.get $cb))
        (then (return (select (i32.const -1) (i32.const 1)
                              (i32.lt_u (local.get $ca) (local.get $cb))))))
      (local.set $i (i32.add (local.get $i) (i32.const 1))) (br $go)))
    (if (i32.lt_u (local.get $la) (local.get $lb)) (then (return (i32.const -1))))
    (if (i32.gt_u (local.get $la) (local.get $lb)) (then (return (i32.const 1))))
    (i32.const 0))
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
  ;; ---- number-to-string: the string builders are the PRIMARY
  ;; implementations; the printers print their result ----
  (func $sput (param $s (ref $str)) (param $p i32) (param $c i32) (result i32)
    (array.set $str (local.get $s) (local.get $p) (local.get $c))
    (i32.add (local.get $p) (i32.const 1)))
  ;; digits of an i64 MAGNITUDE, unsigned — `0 - min` wraps to min, whose
  ;; unsigned value is exactly the magnitude, so negation never overflows
  (func $lput (param $s (ref $str)) (param $p i32) (param $n i64) (result i32)
    (local $m i64)
    (local.set $m (i64.div_u (local.get $n) (i64.const 10)))
    (if (i64.gt_u (local.get $m) (i64.const 0))
      (then (local.set $p (call $lput (local.get $s) (local.get $p) (local.get $m)))))
    (call $sput (local.get $s) (local.get $p)
      (i32.add (i32.const 48) (i32.wrap_i64 (i64.rem_u (local.get $n) (i64.const 10))))))
  (func $strTake (param $s (ref $str)) (param $p i32) (result anyref)
    (local $r (ref $str))
    (local.set $r (array.new_default $str (local.get $p)))
    (array.copy $str $str (local.get $r) (i32.const 0) (local.get $s) (i32.const 0) (local.get $p))
    (local.get $r))
  (func $ltoa (param $n i64) (result anyref)
    (local $s (ref $str)) (local $p i32)
    (local.set $s (array.new_default $str (i32.const 24)))
    (if (i64.lt_s (local.get $n) (i64.const 0))
      (then
        (local.set $p (call $sput (local.get $s) (local.get $p) (i32.const 45)))
        (local.set $n (i64.sub (i64.const 0) (local.get $n)))))
    (local.set $p (call $lput (local.get $s) (local.get $p) (local.get $n)))
    (call $strTake (local.get $s) (local.get $p)))
  (func $ultoa (param $n i64) (result anyref)
    (local $s (ref $str)) (local $p i32)
    (local.set $s (array.new_default $str (i32.const 24)))
    (local.set $p (call $lput (local.get $s) (local.get $p) (local.get $n)))
    (call $strTake (local.get $s) (local.get $p)))
  (func $ftoa (param $v f64) (result anyref)
    (local $s (ref $str)) (local $p i32)
    (local $ip f64) (local $frac f64) (local $k i32) (local $d i32) (local $e i32)
    (local.set $s (array.new_default $str (i32.const 40)))
    ;; NaN is the only value not equal to itself
    (if (f64.ne (local.get $v) (local.get $v))
      (then
        (local.set $p (call $sput (local.get $s) (local.get $p) (i32.const 78)))
        (local.set $p (call $sput (local.get $s) (local.get $p) (i32.const 97)))
        (local.set $p (call $sput (local.get $s) (local.get $p) (i32.const 78)))
        (return (call $strTake (local.get $s) (local.get $p)))))
    (if (f64.lt (local.get $v) (f64.const 0))
      (then
        (local.set $p (call $sput (local.get $s) (local.get $p) (i32.const 45)))
        (local.set $v (f64.neg (local.get $v)))))
    ;; .NET prints U+221E, not the word — so this stays oracle-checkable
    (if (f64.eq (local.get $v) (f64.const inf))
      (then
        (local.set $p (call $sput (local.get $s) (local.get $p) (i32.const 226)))
        (local.set $p (call $sput (local.get $s) (local.get $p) (i32.const 136)))
        (local.set $p (call $sput (local.get $s) (local.get $p) (i32.const 158)))
        (return (call $strTake (local.get $s) (local.get $p)))))
    ;; past what an i64 holds, normalize into [1, 10) and add an exponent
    (if (f64.ge (local.get $v) (f64.const 1e18))
      (then
        (block $scaled (loop $go
          (br_if $scaled (f64.lt (local.get $v) (f64.const 10)))
          (local.set $v (f64.div (local.get $v) (f64.const 10)))
          (local.set $e (i32.add (local.get $e) (i32.const 1)))
          (br $go)))))
    (local.set $ip (f64.floor (local.get $v)))
    (local.set $p (call $lput (local.get $s) (local.get $p) (i64.trunc_f64_s (local.get $ip))))
    (local.set $frac (f64.sub (local.get $v) (local.get $ip)))
    (if (f64.gt (local.get $frac) (f64.const 0))
      (then
        (local.set $p (call $sput (local.get $s) (local.get $p) (i32.const 46)))
        (block $done
          (loop $go
            (br_if $done (i32.ge_s (local.get $k) (i32.const 15)))
            (local.set $frac (f64.mul (local.get $frac) (f64.const 10)))
            (local.set $d (i32.trunc_f64_s (f64.floor (local.get $frac))))
            (local.set $p (call $sput (local.get $s) (local.get $p) (i32.add (i32.const 48) (local.get $d))))
            (local.set $frac (f64.sub (local.get $frac) (f64.floor (local.get $frac))))
            (br_if $done (f64.eq (local.get $frac) (f64.const 0)))
            (local.set $k (i32.add (local.get $k) (i32.const 1)))
            (br $go)))))
    (if (i32.ne (local.get $e) (i32.const 0))
      (then
        (local.set $p (call $sput (local.get $s) (local.get $p) (i32.const 69)))
        (local.set $p (call $sput (local.get $s) (local.get $p) (i32.const 43)))
        (local.set $p (call $lput (local.get $s) (local.get $p) (i64.extend_i32_u (local.get $e))))))
    (call $strTake (local.get $s) (local.get $p)))
  ;; %f is .NET's fixed-six-decimals form
  (func $ftoa6 (param $v f64) (result anyref)
    (local $s (ref $str)) (local $p i32) (local $ip f64) (local $frac f64)
    (local $k i32) (local $d i32)
    (local.set $s (array.new_default $str (i32.const 40)))
    (if (f64.ne (local.get $v) (local.get $v))
      (then
        (local.set $p (call $sput (local.get $s) (local.get $p) (i32.const 78)))
        (local.set $p (call $sput (local.get $s) (local.get $p) (i32.const 97)))
        (local.set $p (call $sput (local.get $s) (local.get $p) (i32.const 78)))
        (return (call $strTake (local.get $s) (local.get $p)))))
    (if (f64.lt (local.get $v) (f64.const 0))
      (then
        (local.set $p (call $sput (local.get $s) (local.get $p) (i32.const 45)))
        (local.set $v (f64.neg (local.get $v)))))
    (if (f64.ge (local.get $v) (f64.const 1e18))
      (then (return (call $ftoa (local.get $v)))))
    ;; round at the sixth decimal first, so 0.0000005 carries
    (local.set $v (f64.add (local.get $v) (f64.const 5e-7)))
    (local.set $ip (f64.floor (local.get $v)))
    (local.set $p (call $lput (local.get $s) (local.get $p) (i64.trunc_f64_s (local.get $ip))))
    (local.set $p (call $sput (local.get $s) (local.get $p) (i32.const 46)))
    (local.set $frac (f64.sub (local.get $v) (local.get $ip)))
    (block $done (loop $go
      (br_if $done (i32.ge_s (local.get $k) (i32.const 6)))
      (local.set $frac (f64.mul (local.get $frac) (f64.const 10)))
      (local.set $d (i32.trunc_f64_s (f64.floor (local.get $frac))))
      (local.set $p (call $sput (local.get $s) (local.get $p) (i32.add (i32.const 48) (local.get $d))))
      (local.set $frac (f64.sub (local.get $frac) (f64.floor (local.get $frac))))
      (local.set $k (i32.add (local.get $k) (i32.const 1)))
      (br $go)))
    (call $strTake (local.get $s) (local.get $p)))
  ;; hex and octal digits of an i64 magnitude
  (func $xput (param $s (ref $str)) (param $p i32) (param $n i64) (param $base i64) (param $upper i32) (result i32)
    (local $m i64) (local $d i32)
    (local.set $m (i64.div_u (local.get $n) (local.get $base)))
    (if (i64.gt_u (local.get $m) (i64.const 0))
      (then (local.set $p (call $xput (local.get $s) (local.get $p) (local.get $m) (local.get $base) (local.get $upper)))))
    (local.set $d (i32.wrap_i64 (i64.rem_u (local.get $n) (local.get $base))))
    (call $sput (local.get $s) (local.get $p)
      (if (result i32) (i32.lt_u (local.get $d) (i32.const 10))
        (then (i32.add (i32.const 48) (local.get $d)))
        (else (i32.add (select (i32.const 55) (i32.const 87) (local.get $upper)) (local.get $d))))))
  (func $ltobase (param $n i64) (param $base i64) (param $upper i32) (result anyref)
    (local $s (ref $str)) (local $p i32)
    (local.set $s (array.new_default $str (i32.const 24)))
    (local.set $p (call $xput (local.get $s) (i32.const 0) (local.get $n) (local.get $base) (local.get $upper)))
    (call $strTake (local.get $s) (local.get $p)))
  (func $itobase (param $n i32) (param $base i32) (param $upper i32) (result anyref)
    (local $s (ref $str)) (local $p i32)
    (local.set $s (array.new_default $str (i32.const 24)))
    (local.set $p (call $xput (local.get $s) (local.get $p)
                    (i64.and (i64.extend_i32_u (local.get $n)) (i64.const 0xffffffff))
                    (i64.extend_i32_u (local.get $base)) (local.get $upper)))
    (call $strTake (local.get $s) (local.get $p)))
  ;; %A at a hole whose static type is unknown: dispatch on the runtime
  ;; representation, best effort (records and unions show as "?")
  (func $showv (param $v anyref) (result anyref)
    (if (ref.is_null (local.get $v))
      (then (return (array.new_fixed $str 4 (i32.const 110) (i32.const 117) (i32.const 108) (i32.const 108)))))
    (if (ref.test (ref i31) (local.get $v))
      (then (return (call $itoa (i31.get_s (ref.cast (ref i31) (local.get $v)))))))
    (if (ref.test (ref $boxi) (local.get $v))
      (then (return (call $itoa (struct.get $boxi 0 (ref.cast (ref $boxi) (local.get $v)))))))
    (if (ref.test (ref $boxl) (local.get $v))
      (then (return (call $ltoa (struct.get $boxl 0 (ref.cast (ref $boxl) (local.get $v)))))))
    (if (ref.test (ref $boxf) (local.get $v))
      (then (return (call $ftoa (struct.get $boxf 0 (ref.cast (ref $boxf) (local.get $v)))))))
    (if (ref.test (ref $boxs) (local.get $v))
      (then (return (call $ftoa (f64.promote_f32 (struct.get $boxs 0 (ref.cast (ref $boxs) (local.get $v))))))))
    (if (ref.test (ref $str) (local.get $v))
      (then
        ;; %A quotes strings, as F# does
        (return (call $strcat
          (ref.cast (ref $str) (call $strcat (array.new_fixed $str 1 (i32.const 34))
                                             (ref.cast (ref $str) (local.get $v))))
          (array.new_fixed $str 1 (i32.const 34))))))
    (array.new_fixed $str 1 (i32.const 63)))
  ;; the built-in iterator: mode 0 = list (cur/rest in the two anyref
  ;; slots), mode 1 = array (source + index)
  (func $isBuiltinSeq (param $v anyref) (result i32)
    (i32.or (ref.is_null (local.get $v))
      (i32.or (ref.test (ref $cons) (local.get $v))
        (i32.or (ref.test (ref $arr) (local.get $v))
          (i32.or (ref.test (ref $parr_i) (local.get $v))
            (i32.or (ref.test (ref $parr_f) (local.get $v))
              (i32.or (ref.test (ref $parr_s) (local.get $v))
                (i32.or (ref.test (ref $parr_l) (local.get $v))
                        (ref.test (ref $parr_h) (local.get $v))))))))))
  (func $isArrayRep (param $v anyref) (result i32)
    (i32.or (ref.test (ref $arr) (local.get $v))
      (i32.or (ref.test (ref $parr_i) (local.get $v))
        (i32.or (ref.test (ref $parr_f) (local.get $v))
          (i32.or (ref.test (ref $parr_s) (local.get $v))
            (i32.or (ref.test (ref $parr_l) (local.get $v))
                    (ref.test (ref $parr_h) (local.get $v))))))))
  (func $iterNew (param $v anyref) (result anyref)
    (if (result anyref)
        (i32.or (ref.is_null (local.get $v)) (ref.test (ref $cons) (local.get $v)))
      (then (struct.new $iter (i32.const 0) (ref.null any) (local.get $v) (i32.const 0)))
      (else (struct.new $iter (i32.const 1) (local.get $v) (ref.null any) (i32.const 0)))))
  ;; one element of ANY array representation, boxed uniformly
  (func $arrGetAny (param $v anyref) (param $i i32) (result anyref)
    (if (ref.test (ref $arr) (local.get $v))
      (then (return (array.get $arr (ref.cast (ref $arr) (local.get $v)) (local.get $i)))))
    (if (ref.test (ref $parr_i) (local.get $v))
      (then (return (call $ofi (array.get $parr_i (ref.cast (ref $parr_i) (local.get $v)) (local.get $i))))))
    (if (ref.test (ref $parr_f) (local.get $v))
      (then (return (call $off (array.get $parr_f (ref.cast (ref $parr_f) (local.get $v)) (local.get $i))))))
    (if (ref.test (ref $parr_s) (local.get $v))
      (then (return (call $oss (array.get $parr_s (ref.cast (ref $parr_s) (local.get $v)) (local.get $i))))))
    (if (ref.test (ref $parr_l) (local.get $v))
      (then (return (call $ofl (array.get $parr_l (ref.cast (ref $parr_l) (local.get $v)) (local.get $i))))))
    (if (ref.test (ref $parr_h) (local.get $v))
      (then (return (call $ofi (array.get_u $parr_h (ref.cast (ref $parr_h) (local.get $v)) (local.get $i))))))
    (ref.i31 (i32.const 0)))
  (func $iterNext (param $st anyref) (result anyref)
    (local $it (ref $iter)) (local $rest anyref) (local $i i32)
    (local.set $it (ref.cast (ref $iter) (local.get $st)))
    (if (result anyref) (i32.eqz (struct.get $iter 0 (local.get $it)))
      (then
        ;; list: advance the cons chain
        (local.set $rest (struct.get $iter 2 (local.get $it)))
        (if (result anyref) (ref.is_null (local.get $rest))
          (then (ref.i31 (i32.const 0)))
          (else
            (struct.set $iter 1 (local.get $it)
              (struct.get $cons 0 (ref.cast (ref $cons) (local.get $rest))))
            (struct.set $iter 2 (local.get $it)
              (struct.get $cons 1 (ref.cast (ref $cons) (local.get $rest))))
            (ref.i31 (i32.const 1)))))
      (else
        ;; array: bump the index
        (local.set $i (struct.get $iter 3 (local.get $it)))
        (if (result anyref)
            (i32.ge_s (local.get $i)
              (i31.get_s (ref.cast (ref i31) (call $lenv (struct.get $iter 1 (local.get $it))))))
          (then (ref.i31 (i32.const 0)))
          (else
            (struct.set $iter 3 (local.get $it) (i32.add (local.get $i) (i32.const 1)))
            (ref.i31 (i32.const 1)))))))
  (func $iterCur (param $st anyref) (result anyref)
    (local $it (ref $iter))
    (local.set $it (ref.cast (ref $iter) (local.get $st)))
    (if (result anyref) (i32.eqz (struct.get $iter 0 (local.get $it)))
      (then (struct.get $iter 1 (local.get $it)))
      (else (call $arrGetAny (struct.get $iter 1 (local.get $it))
                             (i32.sub (struct.get $iter 3 (local.get $it)) (i32.const 1))))))
  (func $strPad (param $v (ref $str)) (param $w i32) (param $c i32) (param $left i32) (result anyref)
    (local $n i32) (local $r (ref $str)) (local $off i32)
    (local.set $n (array.len (local.get $v)))
    (if (i32.ge_u (local.get $n) (local.get $w)) (then (return (local.get $v))))
    (local.set $r (array.new $str (local.get $c) (local.get $w)))
    (local.set $off (select (i32.const 0) (i32.sub (local.get $w) (local.get $n)) (local.get $left)))
    (array.copy $str $str (local.get $r) (local.get $off) (local.get $v) (i32.const 0) (local.get $n))
    (local.get $r))
  (func $printl (param $n i64)
    (call $prints (ref.cast (ref $str) (call $ltoa (local.get $n)))))
  (func $printf64 (param $v f64)
    (call $prints (ref.cast (ref $str) (call $ftoa (local.get $v)))))
  (func $ofi (param $n i32) (result anyref)
    (if (result anyref) (i32.eq (local.get $n) (i32.shr_s (i32.shl (local.get $n) (i32.const 1)) (i32.const 1)))
      (then (ref.i31 (local.get $n)))
      (else (struct.new $boxi (local.get $n)))))
  (func $toi (param $v anyref) (result i32)
    (if (result i32) (ref.test (ref i31) (local.get $v))
      (then (i31.get_s (ref.cast (ref i31) (local.get $v))))
      (else (struct.get $boxi 0 (ref.cast (ref $boxi) (local.get $v))))))
  (func $patchself (param $c anyref)
    ;; tie the recursive knot: replace the marker captured in the closure's
    ;; environment (a FLAT array) with the closure itself
    (local $e anyref)
    (local $i i32)
    (local $n i32)
    (local.set $e (struct.get $clo 1 (ref.cast (ref $clo) (local.get $c))))
    (block $done
      (br_if $done (i32.eqz (ref.test (ref $arr) (local.get $e))))
      (local.set $n (array.len (ref.cast (ref $arr) (local.get $e))))
      (local.set $i (i32.const 0))
      (block $out
        (loop $go
          (br_if $out (i32.ge_u (local.get $i) (local.get $n)))
          (if (ref.eq (ref.cast (ref null eq) (array.get $arr (ref.cast (ref $arr) (local.get $e)) (local.get $i)))
                      (ref.cast (ref null eq) (global.get $selfmark)))
            (then (array.set $arr (ref.cast (ref $arr) (local.get $e)) (local.get $i) (local.get $c))))
          (local.set $i (i32.add (local.get $i) (i32.const 1)))
          (br $go)))))
  (func $patchmark (param $c anyref) (param $mark anyref) (param $v anyref)
    ;; tie one strand of a rec GROUP's knot: in closure $c's FLAT environment,
    ;; whatever slot still holds the marker $mark becomes $v
    (local $e anyref)
    (local $i i32)
    (local $n i32)
    (local.set $e (struct.get $clo 1 (ref.cast (ref $clo) (local.get $c))))
    (block $done
      (br_if $done (i32.eqz (ref.test (ref $arr) (local.get $e))))
      (local.set $n (array.len (ref.cast (ref $arr) (local.get $e))))
      (local.set $i (i32.const 0))
      (block $out
        (loop $go
          (br_if $out (i32.ge_u (local.get $i) (local.get $n)))
          (if (ref.eq (ref.cast (ref null eq) (array.get $arr (ref.cast (ref $arr) (local.get $e)) (local.get $i)))
                      (ref.cast (ref null eq) (local.get $mark)))
            (then (array.set $arr (ref.cast (ref $arr) (local.get $e)) (local.get $i) (local.get $v))))
          (local.set $i (i32.add (local.get $i) (i32.const 1)))
          (br $go)))))
  (func $applyc (param $f anyref) (param $a anyref) (result anyref)
    (call_ref $u1 (local.get $a)
      (struct.get $clo 1 (ref.cast (ref $clo) (local.get $f)))
      (struct.get $clo 0 (ref.cast (ref $clo) (local.get $f)))))"""

    // Structural equality and hashing for tuples: $tupN is a distinct wasm
    // type per arity, so testing it cannot confuse two different shapes.
    let tupleEqCases =
        vecToList tupleArities
        |> List.map (fun n ->
            let t = "$tup" + string n
            let cmp i =
                "        (if (i32.eqz (i31.get_s (ref.cast (ref i31) (call $equal "
                + "(struct.get " + t + " " + string i + " (ref.cast (ref " + t + ") (local.get $a))) "
                + "(struct.get " + t + " " + string i + " (ref.cast (ref " + t + ") (local.get $b)))))))\n"
                + "          (then (return (ref.i31 (i32.const 0)))))"
            "    (if (i32.and (ref.test (ref " + t + ") (local.get $a)) (ref.test (ref " + t + ") (local.get $b)))\n"
            + "      (then\n"
            + String.concat "\n" (List.init n cmp) + "\n"
            + "        (return (ref.i31 (i32.const 1)))))")
        |> String.concat "\n"
    let tupleHashCases =
        vecToList tupleArities
        |> List.map (fun n ->
            let t = "$tup" + string n
            let part i =
                "(call $hashv (struct.get " + t + " " + string i + " (ref.cast (ref " + t + ") (local.get $v))))"
            let combined =
                List.init n part
                |> List.reduce (fun acc x -> "(i32.add (i32.mul " + acc + " (i32.const 31)) " + x + ")")
            "    (if (ref.test (ref " + t + ") (local.get $v))\n      (then (return " + combined + ")))")
        |> String.concat "\n"
    line (runtimeSrc.Replace("TUPLE_EQ", tupleEqCases).Replace("TUPLE_HASH", tupleHashCases))


    // top-level functions and value initializers
    let initFuncs = vecNew<string> ()
    for d in decls do
        match d with
        | DLet (_, v, _, ELam (ps, body)) ->
            let fname = (dictTryFind topName (v.Path, v.Offset)).Value
            currentFn <- v.Name
            ceMemos.Clear ()
            let pks, rk =
                match dictTryFind sigKinds (v.Path, v.Offset) with
                | Some (pk, r) -> pk, r
                | None -> List.replicate ps.Length "u", "u"
            let pss, rs =
                match dictTryFind sigStructs (v.Path, v.Offset) with
                | Some (a, b) -> a, b
                | None -> List.replicate ps.Length None, None
            let locals = dictNew<string * int, string> ()
            let paramDecls = vecNew<string> ()
            ps |> List.iteri (fun i (pv, _) ->
                match (if i < pss.Length then List.item i pss else None) with
                | Some srn ->
                    // scalarized: one param per leaf, field access hits them
                    let m = dictNew<string, string> ()
                    leavesOf srn |> List.iteri (fun j (lp, k, _) ->
                        let nm = "$a" + string i + "_" + string j
                        vecAdd paramDecls ("(param " + nm + " " + wasmTyOf2 k + ")")
                        dictSet m lp nm)
                    dictSet paramLeaves (pv.Path, pv.Offset) (srn, m)
                | None ->
                    vecAdd paramDecls ("(param $a" + string i + " " + wasmTyOf (List.item i pks) + ")")
                    dictSet locals (pv.Path, pv.Offset) ("$a" + string i)
                    dictSet localKinds (pv.Path, pv.Offset) (List.item i pks))
            let extra = vecNew<string * string> ()
            match rs with
            | Some srn ->
                let leaves = leavesOf srn
                let bodyW = compileLeaves locals extra (dictNew ()) srn body
                let resTys = leaves |> List.map (fun (_, k, _) -> wasmTyOf2 k) |> String.concat " "
                let localDecls = vecToList extra |> List.map (fun (l, ty) -> "(local " + l + " " + ty + ")") |> String.concat " "
                line ("  (func " + fname + " " + String.concat " " (vecToList paramDecls) + " (result " + resTys + ") " + localDecls + " " + bodyW + ")")
            | None ->
                let bodyRaw = compileExpr locals extra (dictNew ()) (rk = "u") body
                let bodyW = if rk = "u" then bodyRaw else unboxK rk bodyRaw
                let localDecls = vecToList extra |> List.map (fun (l, ty) -> "(local " + l + " " + ty + ")") |> String.concat " "
                line ("  (func " + fname + " " + String.concat " " (vecToList paramDecls) + " (result " + wasmTyOf rk + ") " + localDecls + " " + bodyW + ")")
        | DLet (_, v, _, rhs) ->
            let gname = (dictTryFind topName (v.Path, v.Offset)).Value
            currentFn <- v.Name
            ceMemos.Clear ()
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

    // constructors as first-class functions
    for name in vecToList ctorAsFn do
        line ("  (func $ctorfn_" + name + " (type $u1) (param $a anyref) (param $env anyref) (result anyref) (struct.new $du1 (i32.const " + string (dictTryFind caseTag name).Value + ") (local.get $a)))")

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
    for name in vecToList ctorAsFn do vecAdd declared ("$ctorfn_" + name)
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
              "(call $ofi ", "(call $toi "
              // literal box forms
              "(call $tof ", "(struct.new $boxf "
              "(call $tos ", "(struct.new $boxs "
              "(call $tol ", "(struct.new $boxl " ]
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
                        let arg : string = t.Substring (innerStart + inner.Length, innerEnd - (innerStart + inner.Length))
                        let before : string = t.Substring (0, idx)
                        let after : string = t.Substring (innerEnd + 2)
                        t <- before + arg + after
                        changed <- true
                        idx <- t.IndexOf pat
                    else
                        idx <- t.IndexOf (pat, idx + 1)
        t

    { Wat = peephole (sb.ToString ()); Errors = vecToList errors }
