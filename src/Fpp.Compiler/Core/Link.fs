module Fpp.Core.Link

open Fpp.Prelude
open Fpp.Analysis
open Fpp.Analysis.Types
open Fpp.Core.Ir

// ---- tier-1 monomorphization ---------------------------------------------
// One stamped copy per distinct STRUCT instantiation; ONE shared body for
// all reference-type instantiations (__Canon). Unclassifiable instantiations
// are errors, never a silent uniform fallback.

type Classification =
    | Stamp of string list      // struct instantiation -> specialize
    | Canon                     // all-reference instantiation -> share
    | Unclassifiable of string  // compile error

/// `isStructName` decides which type names are value types needing layout.
let classify (isStructName : string -> bool) (inst : string list) : Classification =
    // "#id" = instantiated at the enclosing binding's type variable. In the
    // UNSTAMPED generic body that is exactly the canonical (uniform) case;
    // inside a stamped clone these have already been substituted away.
    if inst |> List.exists (fun t -> t = "" || t.StartsWith "#") then Canon
    elif inst |> List.exists isStructName then Stamp inst
    else Canon

/// substitute a symbolic element/type name ("#id") with the concrete one
/// An arithmetic prim carries the operand TYPE when it is not one of the
/// primitives the backend spells with a suffix letter — either a type
/// variable of the enclosing binding (`+@#7`) or a named type. Stamping
/// substitutes the variable; this then turns the name back into the letter
/// the emitter understands.
let private opTypeName (op : string) : string option =
    let i = op.IndexOf "@"
    if i < 0 then None else Some (op.Substring (i + 1))

let private withOpType (op : string) (name : string) : string =
    let i = op.IndexOf "@"
    let baseOp = if i < 0 then op else op.Substring (0, i)
    match name with
    | "float" -> baseOp + "f"
    | "float32" -> baseOp + "s"
    | "float16" -> baseOp + "h"
    | "int64" -> baseOp + "l"
    | "uint32" -> baseOp + "w"
    | "uint64" -> baseOp + "v"
    | "string" -> baseOp + "t"
    // byte and sbyte are int-SHAPED: the value is already masked (or sign
    // extended) into an i32, so every operator on them is the integer one.
    // Leaving them out sent `<@byte` looking for an instance member — and
    // found the generated `compare`, whose own body is that comparison.
    // int16 and uint16 are int-SHAPED like byte and sbyte: the value is
    // already masked (or sign extended) into an i32, so every operator on
    // them is the integer one
    | "int" | "char" | "bool" | "byte" | "sbyte" | "int16" | "uint16" ->
        // int-shaped EQUALITY stays typed (i32.eq beats structural $equal);
        // arithmetic on ints is already the bare default
        if baseOp = "=" || baseOp = "<>" then baseOp + "i" else baseOp
    // a type whose instance has a body: still unresolved here, and emission
    // reports it rather than silently running the integer path
    | other -> baseOp + "@" + other

/// Key for one instance member: the class, the member, and the head types.
let instanceKey (cls : string) (memberName : string) (heads : string list) : string =
    cls + "|" + memberName + "|" + String.concat "@" heads

/// A type variable can sit ANYWHERE in an instantiated name, not just be the
/// whole of it: `StructTuple2$<bool.SetNode$<#42>>` is the struct a generic
/// body builds, and a clone that only replaced whole-name variables would
/// keep the `#42` and name a record that is never declared.
let private substName (subst : Dict<string, string>) (n : string) =
    if not (n.Contains "#") then n
    else
        let out = vecNew<string> ()
        let mutable i = 0
        while i < n.Length do
            if n.[i] = '#' then
                let start = i
                i <- i + 1
                while i < n.Length && isDigit n.[i] do i <- i + 1
                let var = n.Substring (start, i - start)
                vecAdd out (match dictTryFind subst var with Some c -> c | None -> var)
            else
                vecAdd out (substr n i 1)
                i <- i + 1
        String.concat "" (vecToList out)

/// Split an instantiation name into its constructor and arguments:
/// `list$<int>` is "list" with ["int"], and `Map$<int.list$<int>>` is "Map"
/// with ["int"; "list$<int>"]. Nesting is bracketed, so the split counts
/// depth rather than taking the first separator.
let splitInstName (n : string) : string * string list =
    let i = n.IndexOf "$<"
    if i <= 0 || not (n.EndsWith ">") then n, []
    else
        let head = n.Substring (0, i)
        let inner = n.Substring (i + 2, strLen n - i - 3)
        let args = vecNew<string> ()
        let piece = vecNew<string> ()
        let mutable depth = 0
        let mutable k = 0
        while k < strLen inner do
            let ch = substr inner k 1
            if ch = "<" then depth <- depth + 1
            elif ch = ">" then depth <- depth - 1
            if ch = "." && depth = 0 then
                vecAdd args (String.concat "" (vecToList piece))
                vecClear piece
            else vecAdd piece ch
            k <- k + 1
        if vecLen piece > 0 then vecAdd args (String.concat "" (vecToList piece))
        head, vecToList args

/// Does an instance head PATTERN accept this concrete instantiation name?
/// A `#n` stands for one of the instance's own variables and accepts
/// anything, so `list$<#28>` accepts `list$<int>`.
let rec nameMatches (pat : string) (name : string) : bool =
    if pat.StartsWith "#" then true
    else
        let ph, pa = splitInstName pat
        let nh, na = splitInstName name
        ph = nh && pa.Length = na.Length && List.forall2 nameMatches pa na

/// How general a head pattern is: the number of variables it leaves open.
/// Fewer is more specific, which is how the overlapping instance wins.
let rec nameHoles (pat : string) : int =
    if pat.StartsWith "#" then 1
    else splitInstName pat |> snd |> List.sumBy nameHoles

let private mangleInst (name : string) (inst : string list) =
    name + "$" + String.concat "$" inst

/// Substitute the quantified vars of a scheme with concrete named types.
let private substScheme (inst : string list) (sch : Scheme) : Scheme =
    if List.isEmpty sch.Quantified || sch.Quantified.Length <> inst.Length then sch
    else
        let m = dictNew<int, Type> ()
        List.zip sch.Quantified inst |> List.iter (fun (v, n) -> dictSet m (prunedId v) (TCon (n, [])))
        let rec go (t : Type) : Type =
            match prune t with
            | TVar v -> (match dictTryFind m v.Id with Some c -> c | None -> TVar v)
            | TCon (n, args) -> TCon (n, List.map go args)
            | TFun (a, b) -> TFun (go a, go b)
            | TTuple ts -> TTuple (List.map go ts)
        { Quantified = []; Constraints = []; Body = go sch.Body }

let rec private mapExpr (f : Expr -> Expr) (e : Expr) : Expr =
    let r = mapExpr f
    let e2 =
        match e with
        | ELam (ps, b) -> ELam (ps, r b)
        | EApp (g, args) -> EApp (r g, List.map r args)
        | ELet (rc, v, s, rhs, b) -> ELet (rc, v, s, r rhs, r b)
        | EIf (a, b, c) -> EIf (r a, r b, r c)
        | EMatch (s, cs) -> EMatch (r s, cs |> List.map (fun (p, g, b) -> p, Option.map r g, r b))
        | ETuple xs -> ETuple (List.map r xs)
        | EListLit xs -> EListLit (List.map r xs)
        | ESeq xs -> ESeq (List.map r xs)
        | EPrim (op, xs) -> EPrim (op, List.map r xs)
        | ECtor (n, s, xs) -> ECtor (n, s, List.map r xs)
        | ERecord (n, fs) -> ERecord (n, fs |> List.map (fun (k, v) -> k, r v))
        | ERecordExt (n, bse, fs) -> ERecordExt (n, r bse, fs |> List.map (fun (k, v) -> k, r v))
        | EField (x, fn, o) -> EField (r x, fn, o)
        | EIfaceCall (i, m, recv, args) -> EIfaceCall (i, m, r recv, List.map r args)
        | ECast (t, x, d) -> ECast (t, r x, d)
        | ETypeTest (t, x) -> ETypeTest (t, r x)
        | EFieldSet (x, fn, o, v) -> EFieldSet (r x, fn, o, r v)
        | EWhile (c, b) -> EWhile (r c, r b)
        | EAssign (v, x) -> EAssign (v, r x)
        | EArray (n, xs) -> EArray (n, List.map r xs)
        | EIndex (n, a, i) -> EIndex (n, r a, r i)
        | EIndexSet (n, a, i, v) -> EIndexSet (n, r a, r i, r v)
        | EArrayLen (n, a) -> EArrayLen (n, r a)
        | EArrayCreate (n, a, b) -> EArrayCreate (n, r a, r b)
        | EArrayPin (n, a) -> EArrayPin (n, r a)
        | EArrayUnpin (n, a) -> EArrayUnpin (n, r a)
        | EArrayBytes (n, a) -> EArrayBytes (n, r a)
        | ETry (b, cs) -> ETry (r b, cs |> List.map (fun (p, g, x) -> p, Option.map r g, r x))
        | other -> other
    f e2

/// Stamp a generic record per instantiation. A `'a` field has no
/// representation until `'a` is known, so sharing one declaration across
/// instantiations would force every field to be boxed. Each instantiation
/// gets its own declaration, and therefore its own layout.
let stampRecords (decls : Decl list) : Decl list =
    let templates =
        decls
        |> List.choose (fun d ->
            match d with
            | DRecord (n, ps, fs, st) when not (List.isEmpty ps) -> Some (n, (ps, fs, st))
            | _ -> None)
    if List.isEmpty templates then decls
    else
        let used = dictNew<string, bool> ()
        let note (n : string) = if n <> "" && n <> "?" then dictSet used n true
        let noteIn (e : Expr) =
            mapExpr
                (fun x ->
                    (match x with
                     | ERecord (n, _) -> note n
                     | EField (_, _, o) | EFieldSet (_, _, o, _) -> note o
                     | EArray (n, _) | EIndex (n, _, _) | EIndexSet (n, _, _, _)
                     | EArrayLen (n, _) | EArrayCreate (n, _, _)
                     | EArrayPin (n, _) | EArrayUnpin (n, _) | EArrayBytes (n, _) -> note n
                     | _ -> ())
                    x)
                e |> ignore
        for d in decls do
            match d with
            | DLet (_, _, _, e) -> noteIn e
            | _ -> ()
        /// `Pair$<int.Pair$<int.int>>` -> ("Pair", ["int"; "Pair$<int.int>"])
        let splitInst (name : string) : (string * string list) option =
            let i = name.IndexOf "$<"
            if i < 0 || not (name.EndsWith ">") then None
            else
                let baseName = name.Substring (0, i)
                let inner = name.Substring (i + 2, name.Length - i - 3)
                let args = vecNew<string> ()
                // chunks joined per argument: a builder is not part of the
                // seam, and string append would be quadratic
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
                Some (baseName, vecToList args)
        let stamped = vecNew<Decl> ()
        for name, _ in dictPairs used do
            // a name still mentioning a type variable belongs to code that
            // is itself generic; it is stamped when that code is
            if name.Contains "$<" && not (name.Contains "#") then
                match splitInst name with
                | Some (baseName, args) when not (List.isEmpty args) ->
                    (match templates |> List.tryFind (fun (n, _) -> n = baseName) with
                     | Some (_, (ps, fs, st)) when ps.Length = args.Length ->
                         let fs2 =
                             fs
                             |> List.map (fun (f, t) ->
                                 if t.StartsWith "'" then
                                     let v = t.Substring 1
                                     match ps |> List.tryFindIndex (fun p -> p = v) with
                                     | Some i -> f, List.item i args
                                     | None -> f, t
                                 else f, t)
                         vecAdd stamped (DRecord (name, [], fs2, st))
                     | _ -> ())
                | _ -> ()
        decls @ vecToList stamped

/// Stamp one specialized copy per struct instantiation, rewrite the calls,
/// and report anything that cannot be classified.
/// `instanceFns` maps "Class@T1@T2" to the function an instance supplies,
/// so an operator inside a body stamped at a user type becomes a call to it.
let monomorphizeWith (isStructName : string -> bool) (instanceFns : Dict<string, VarId * bool>)
                     (decls : Decl list) : Decl list * string list =
    let errors = vecNew<string> ()
    let bodies = dictNew<string * int, bool * VarId * Scheme * Expr> ()
    for d in decls do
        match d with
        | DLet (rc, v, sch, e) -> dictSet bodies (v.Path, v.Offset) (rc, v, sch, e)
        | _ -> ()
    // Two top-level functions may share a bare name (Array.rev and Seq.rev):
    // their stamps must not collide, so an AMBIGUOUS name carries its
    // definition offset. Unique names keep the readable form.
    let nameShared = dictNew<string, bool> ()
    let nameSeenAt = dictNew<string, string * int> ()
    for d in decls do
        match d with
        | DLet (_, v, _, _) ->
            (match dictTryFind nameSeenAt v.Name with
             | Some k when k <> (v.Path, v.Offset) -> dictSet nameShared v.Name true
             | Some _ -> ()
             | None -> dictSet nameSeenAt v.Name (v.Path, v.Offset))
        | _ -> ()
    let mangleFor (v : VarId) (inst : string list) =
        if (dictTryFind nameShared v.Name) = Some true
        then mangleInst (v.Name + "_" + string v.Offset) inst
        else mangleInst v.Name inst
    // A body that performs array/layout operations at a type-variable
    // element type cannot be shared: int[], string[] and struct[] have
    // different representations. Such functions are stamped at EVERY
    // instantiation, not just struct ones.
    let layoutDependent = dictNew<string * int, bool> ()
    let rec usesLayoutVar (e : Expr) : bool =
        let anyOf xs = xs |> List.exists usesLayoutVar
        let symbolic (n : string) = n.StartsWith "#"
        match e with
        | EArray (n, xs) -> symbolic n || anyOf xs
        | EIndex (n, a, i) -> symbolic n || usesLayoutVar a || usesLayoutVar i
        | EIndexSet (n, a, i, v) -> symbolic n || anyOf [ a; i; v ]
        | EArrayLen (n, a) -> symbolic n || usesLayoutVar a
        | EArrayCreate (n, a, b) -> symbolic n || anyOf [ a; b ]
        | EArrayPin (n, a) | EArrayUnpin (n, a) | EArrayBytes (n, a) -> symbolic n || usesLayoutVar a
        | ELam (_, b) -> usesLayoutVar b
        | EApp (f, args) -> usesLayoutVar f || anyOf args
        | ELet (_, _, _, r, b) -> usesLayoutVar r || usesLayoutVar b
        | EIf (a, b, c) -> anyOf [ a; b; c ]
        // the GUARD counts as much as the body: an operator or array op in
        // a `when` clause is just as unshareable across instantiations
        | EMatch (s, cs) ->
            usesLayoutVar s
            || (cs |> List.exists (fun (_, g, b) ->
                    usesLayoutVar b || (match g with Some x -> usesLayoutVar x | None -> false)))
        | ETuple xs | EListLit xs | ESeq xs -> anyOf xs
        // an operator at a type variable cannot be shared either: the
        // instance — and so the machine instruction — differs per type
        | EPrim (op, xs) ->
            (match opTypeName op with Some n -> symbolic n | None -> false) || anyOf xs
        // an unresolved class member is unshareable for the same reason an
        // operator is: which function it denotes depends on the type
        | EUnknown n -> n.StartsWith "$class:" && n.Contains "#"
        | ECtor (_, _, xs) -> anyOf xs
        // a record whose NAME still mentions a type variable has no layout
        // yet, so code building it must be stamped just like an array op
        | ERecord (n, fs) -> n.Contains "#" || (fs |> List.exists (fun (_, v) -> usesLayoutVar v))
        | ERecordExt (_, bse, fs) -> usesLayoutVar bse || (fs |> List.exists (fun (_, v) -> usesLayoutVar v))
        | EField (r, _, o) -> o.Contains "#" || usesLayoutVar r
        | EIfaceCall (_, _, recv, args) -> usesLayoutVar recv || anyOf args
        | ECast (_, x, _) -> usesLayoutVar x
        | ETypeTest (_, x) -> usesLayoutVar x
        | EFieldSet (r, _, o, v) -> o.Contains "#" || usesLayoutVar r || usesLayoutVar v
        | EWhile (c, b) -> usesLayoutVar c || usesLayoutVar b
        | EAssign (_, x) -> usesLayoutVar x
        | ETry (b, cs) ->
            usesLayoutVar b
            || (cs |> List.exists (fun (_, g, x) ->
                    usesLayoutVar x || (match g with Some y -> usesLayoutVar y | None -> false)))
        | _ -> false
    for d in decls do
        match d with
        | DLet (_, v, _, e) -> dictSet layoutDependent (v.Path, v.Offset) (usesLayoutVar e)
        | _ -> ()
    // transitive: calling a layout-dependent generic at a symbolic
    // instantiation makes the caller layout-dependent too (fixpoint)
    let rec callsLayoutDep (e : Expr) : bool =
        let anyOf xs = xs |> List.exists callsLayoutDep
        match e with
        | EVarI (v, _, inst) ->
            (dictTryFind layoutDependent (v.Path, v.Offset)) = Some true
            && inst |> List.exists (fun t -> t = "" || t.Contains "#")
        | ELam (_, b) -> callsLayoutDep b
        | EApp (f, args) -> callsLayoutDep f || anyOf args
        | ELet (_, _, _, r, b) -> callsLayoutDep r || callsLayoutDep b
        | EIf (a, b, c) -> anyOf [ a; b; c ]
        | EMatch (s, cs) ->
            callsLayoutDep s
            || (cs |> List.exists (fun (_, g, b) ->
                    callsLayoutDep b || (match g with Some x -> callsLayoutDep x | None -> false)))
        | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) -> anyOf xs
        | ECtor (_, _, xs) -> anyOf xs
        | ERecord (_, fs) -> fs |> List.exists (fun (_, v) -> callsLayoutDep v)
        | ERecordExt (_, bse, fs) -> callsLayoutDep bse || (fs |> List.exists (fun (_, v) -> callsLayoutDep v))
        | EField (r, _, _) -> callsLayoutDep r
        | EIfaceCall (_, _, recv, args) -> callsLayoutDep recv || anyOf args
        | ECast (_, x, _) -> callsLayoutDep x
        | ETypeTest (_, x) -> callsLayoutDep x
        | EFieldSet (r, _, _, v) -> callsLayoutDep r || callsLayoutDep v
        | EWhile (c, b) -> callsLayoutDep c || callsLayoutDep b
        | EAssign (_, x) -> callsLayoutDep x
        | EArray (_, xs) -> anyOf xs
        | EIndex (_, a, i) -> anyOf [ a; i ]
        | EIndexSet (_, a, i, v) -> anyOf [ a; i; v ]
        | EArrayLen (_, a) | EArrayPin (_, a) | EArrayUnpin (_, a) | EArrayBytes (_, a) -> callsLayoutDep a
        | EArrayCreate (_, a, b) -> anyOf [ a; b ]
        | ETry (b, cs) ->
            callsLayoutDep b
            || (cs |> List.exists (fun (_, g, x) ->
                    callsLayoutDep x || (match g with Some y -> callsLayoutDep y | None -> false)))
        | _ -> false
    let mutable changed = true
    while changed do
        changed <- false
        for d in decls do
            match d with
            | DLet (_, v, _, e) ->
                if (dictTryFind layoutDependent (v.Path, v.Offset)) <> Some true && callsLayoutDep e then
                    dictSet layoutDependent (v.Path, v.Offset) true
                    changed <- true
            | _ -> ()
    // A class whose VTABLE members depend on the layout drags its
    // constructor in with them, however plain the constructor looks. The
    // constructor is what allocates, and allocating is what picks the
    // vtable: without a stamp per instantiation there is nowhere to hang
    // one, and the interface call lands in the canonical member that reads
    // a packed array as uniform.
    let vtableLayoutDep = dictNew<string, bool> ()
    for d in decls do
        match d with
        | DClass (n, _, own, impls) ->
            let ms =
                (own |> List.map snd)
                @ (impls |> List.collect (fun (_, mems) -> mems |> List.map snd))
            if ms |> List.exists (fun mv -> (dictTryFind layoutDependent (mv.Path, mv.Offset)) = Some true) then
                dictSet vtableLayoutDep n true
        | _ -> ()
    /// constructors forced into stamping by their class' vtable, NOT by
    /// anything in their own body
    let vtableCtor = dictNew<string * int, bool> ()
    for d in decls do
        match d with
        | DLet (_, v, sch, ELam _) when
                (dictTryFind vtableLayoutDep v.Name) = Some true
                && not (List.isEmpty sch.Quantified) ->
            if (dictTryFind layoutDependent (v.Path, v.Offset)) <> Some true then
                dictSet vtableCtor (v.Path, v.Offset) true
            dictSet layoutDependent (v.Path, v.Offset) true
        | _ -> ()

    let stamped = dictNew<string, Decl> ()      // mangled name -> clone
    let queue = vecNew<(string * int) * string list> ()
    let seen = dictNew<string, bool> ()
    // A DIVERGENCE CAP. Poisoned member schemes (class vars mutated by a
    // use — the shared-representative hazard) hand the vtable stamper
    // instantiations that GROW each round: IndexList<T> begets
    // IndexList<StructTuple2<T, T>> begets its double, and the queue never
    // drains. An instantiation nested deeper than any real program writes
    // degrades to the uniform representation — boxed, correct, and finite.
    // A stamp's IDENTITY. It used to be offset + hash(mangled) mod 1e6 —
    // and with a few thousand stamps two different clones COLLIDE, one
    // reading the other's signature: a zip crash when the arities differ,
    // invalid wasm when they happen to agree. The registry hands each
    // mangled name one offset, first come first served, deterministically.
    // The base sits far above every synthetic-offset family the lowerer
    // mints (7e6 _fmt, 1.5e7/1.7e7, 7e7 set_Item, 9.5e7 Dispose, 9.7e7) —
    // dense allocation from a shared base COLLIDED with 7e6+offset vars.
    let stampOffsets = dictNew<string, int> ()
    // stamp offset -> the TEMPLATE's offset. What lets a demand on a stamped
    // constructor unpark the class members that parked on the template.
    let stampOrigins = dictNew<int, int> ()
    let mutable stampNext = 500000000
    let stampOffsetOf (baseOffset : int) (mangled : string) : int =
        match dictTryFind stampOffsets mangled with
        | Some o -> o
        | None ->
            let o = stampNext
            stampNext <- stampNext + 1
            dictSet stampOffsets mangled o
            dictSet stampOrigins o baseOffset
            o
    let mutable cappedWarned = false
    let capInst (i : string list) : string list =
        i |> List.map (fun t ->
            let mutable depth = 0
            let mutable worst = 0
            for k in 0 .. strLen t - 1 do
                if charAt t k = '<' then
                    depth <- depth + 1
                    if depth > worst then worst <- depth
                elif charAt t k = '>' then depth <- depth - 1
            if worst > 5 then
                if not cappedWarned then
                    cappedWarned <- true
                    ewarn ("mono: instantiation depth capped (" + substr t 0 (min 60 (strLen t)) + "...) — a scheme is poisoned, see CLAUDE.md")
                "$ref"
            else t)

    // rewrite EVarI uses: struct instantiations point at the stamped clone,
    // reference instantiations keep the shared body
    // `isTemplate` marks the original body of a layout-dependent generic:
    // it is never emitted (every use is stamped, DCE drops it), so demands
    // that are still symbolic there are not errors — they resolve in clones.
    /// Demand one stamped copy of `v` at `i` and return the reference to it.
    /// The worklist is what actually clones the body, so a reference that is
    /// PRODUCED during rewriting (rather than walked over) has to enqueue the
    /// work itself — `mapExpr` never revisits what its callback returns.
    let stampRef (v : VarId) (sch : Scheme) (i : string list) (fallback : Expr) : Expr =
        let i = capInst i
        let key = (v.Path, v.Offset)
        match dictTryFind bodies key with
        | Some _ ->
            let mangled = mangleFor v i
            if not (dictTryFind seen mangled).IsSome then
                dictSet seen mangled true
                vecAdd queue (key, i)
            EVar ({ Path = v.Path; Offset = stampOffsetOf v.Offset mangled
                    Name = mangled }, substScheme i sch)
        | None -> fallback

    let rewrite (owner : string) (ownerKey : string * int) (subst : Dict<string, string>) (isTemplate : bool) (e : Expr) : Expr =
        e |> mapExpr (fun x ->
            match x with
            | EVarI (v, sch, inst0) ->
                // propagate the caller's instantiation into nested demands
                let inst =
                    inst0 |> List.map (fun t ->
                        if t.Contains "#" then
                            // substName, not a whole-name lookup: an
                            // instantiation may MENTION a variable rather
                            // than be one (`list$<#42>`)
                            match (let r = substName subst t
                                   if r.Contains "#" then None else Some r) with
                            | Some concrete -> concrete
                            | None ->
                                // outside a template an unsubstituted var is
                                // UNCONSTRAINED at this call: nothing observes
                                // it, so it carries no layout requirement and
                                // canonicalizes (this is not a deopt — there
                                // is no representation to specialize for)
                                if isTemplate then t else "obj"
                        else t)
                let needsLayout = (dictTryFind layoutDependent (v.Path, v.Offset)) = Some true
                // A demand with no NAME at all can never become one: stamping
                // substitutes "#id" variables, and there is nothing to
                // substitute. So it is an error even inside a template, where
                // a symbolic demand would legitimately resolve per clone.
                // Suppressing it there is what let a class member fail
                // SILENTLY — the template is never emitted, every use was
                // supposed to be stamped, and the member simply vanished.
                let nameless = inst |> List.exists (fun t -> t = "")
                let cls =
                    if needsLayout then
                        // a slot with NO name is one nothing observes at this
                        // call (an empty dictionary passed straight in, say):
                        // the uniform representation is correct for it, so
                        // stamp at $ref rather than leaving the use naming a
                        // template that specialization removes
                        if not isTemplate then
                            // OUTSIDE a template nothing will ever clone this
                            // body, so a slot that is still symbolic (or has
                            // no name at all) will never become concrete —
                            // and nothing observes its layout here. Uniform
                            // is the right answer, and it keeps the use from
                            // naming a template that specialization removes.
                            Stamp (inst |> List.map (fun t -> if t = "" || t.Contains "#" then "$ref" else t))
                        elif nameless then
                            Unclassifiable "the type argument has no name to specialize on"
                        elif inst |> List.exists (fun t -> t.Contains "#") then
                            Unclassifiable "element layout is not statically known here"
                        else Stamp inst
                    else classify isStructName inst
                (match cls with
                 | Canon -> EVar (v, sch)
                 | Unclassifiable why ->
                     if not isTemplate || nameless then
                         vecAdd errors ("cannot specialize '" + v.Name + "' in " + owner + ": " + why)
                     EVar (v, sch)
                 | Stamp i0 ->
                     let i = capInst i0
                     let mangled = mangleFor v i
                     let key = (v.Path, v.Offset)
                     (match dictTryFind bodies key with
                      | Some (_, _, _, _) ->
                          if not (dictTryFind seen mangled).IsSome then
                              dictSet seen mangled true
                              vecAdd queue (key, i)
                          EVar ({ Path = v.Path; Offset = stampOffsetOf v.Offset mangled
                                  Name = mangled }, substScheme i sch)
                      | None ->
                          // a struct instantiation whose body we cannot see
                          // would have to run on the uniform representation:
                          // that is a silent deoptimization, so it is an error
                          if not isTemplate then
                              vecAdd errors
                                ("cannot specialize '" + v.Name + "' at struct instantiation <"
                                 + String.concat ", " i + "> in " + owner
                                 + ": the body is not available for stamping")
                          EVar (v, sch)))
            | EPrim (op, xs) ->
                (match opTypeName op with
                 | Some n ->
                     let resolved = withOpType op (substName subst n)
                     // still named: the operand type has an instance with a
                     // body, so the operator is a call to it. Only the
                     // homogeneous case is reachable here — a heterogeneous
                     // use is never generic in both operands at once.
                     (match opTypeName resolved with
                      | Some tn ->
                          let cls =
                              match Classes.operatorClass (resolved.Substring (0, resolved.IndexOf "@")) with
                              | Some c -> c
                              | None -> ""
                          // homogeneous two-parameter, else single-parameter
                          let baseOp = resolved.Substring (0, resolved.IndexOf "@")
                          let mem = Classes.operatorMemberName baseOp
                          let key2 = instanceKey cls mem [ tn; tn ]
                          let key1 = instanceKey cls mem [ tn ]
                          let asCall (fnp : VarId * bool) =
                              let fn, _ = fnp
                              let call = EApp (EVar (fn, mono (TCon ("?", []))), xs)
                              // ordering has one operation; the predicates
                              // test its result
                              if cls = "Ordered" then EPrim (baseOp, [ call; ELit (LInt "0") ]) else call
                          // resolving to the function BEING rewritten turns
                          // its own body into a call to itself. That is
                          // exactly the shape of the generated `compare`,
                          // whose body IS the two ordering primitives — so
                          // for it the primitive stands, and a type the
                          // backend cannot spell is reported at emission
                          // rather than looping forever at runtime.
                          let notSelf (fnp : VarId * bool) =
                              let fn, _ = fnp
                              (fn.Path, fn.Offset) <> ownerKey
                          (match dictTryFind instanceFns key2 with
                           | Some fn when notSelf fn -> asCall fn
                           | Some _ -> EPrim (resolved, xs)
                           | None ->
                               match dictTryFind instanceFns key1 with
                               | Some fn when notSelf fn -> asCall fn
                               | Some _ -> EPrim (resolved, xs)
                               | None -> EPrim (resolved, xs))
                      | None -> EPrim (resolved, xs))
                 | None -> EPrim (op, xs))
            | EUnknown n when n.StartsWith "$sizeof:" ->
                // resolve the SYMBOLIC instantiation the way $class does:
                // the size is only knowable once the stamp names the type
                EUnknown ("$sizeof:" + substName subst (n.Substring 8))
            | EUnknown n when n.StartsWith "$class:" ->
                // an ARRAY pattern would read better here, but F++ has no
                // array patterns yet (see PLAN.md) — an array literal in
                // pattern position parses as a list pattern
                (let parts = n.Substring(7).Split ':'
                 match parts.Length with
                 | 3 ->
                     let cls = parts.[0]
                     let memberName = parts.[1]
                     let tn = substName subst parts.[2]
                     // a one-parameter class keys on one head, a homogeneous
                     // two-parameter one on the pair
                     let byOne = dictTryFind instanceFns (instanceKey cls memberName [ tn ])
                     let byTwo = dictTryFind instanceFns (instanceKey cls memberName [ tn; tn ])
                     // An instantiation names its arguments (`list$<int>`),
                     // but an instance registers under its CONSTRUCTOR. So a
                     // miss falls back to the constructor — and then hands
                     // the arguments on as the instance's own instantiation,
                     // which is what lets a GENERIC instance's `when` context
                     // resolve here: `Sized<list<'a>>` reached at list$<int>
                     // stamps its body at 'a = int.
                     let hd, hdArgs = splitInstName tn
                     let byHead =
                         if hd = tn then None
                         else
                             match dictTryFind instanceFns (instanceKey cls memberName [ hd ]) with
                             | Some v -> Some v
                             | None -> dictTryFind instanceFns (instanceKey cls memberName [ hd; hd ])
                     // Neither the exact name nor the constructor found one:
                     // scan the class' instance heads as PATTERNS. This is
                     // what resolves `list$<int>` against `instance C<list<'a>>`
                     // once overlapping instances make the constructor alone
                     // ambiguous — and among several matches the one with the
                     // fewest open variables wins, which is the same
                     // most-specific rule the checker used.
                     let byPattern () =
                         let prefix = cls + "|" + memberName + "|"
                         let hits = vecNew<int * (VarId * bool)> ()
                         for key, value in dictPairs instanceFns do
                             if key.StartsWith prefix then
                                 let heads = key.Substring(strLen prefix).Split '@' |> Array.toList
                                 match heads with
                                 | [ h ] when nameMatches h tn -> vecAdd hits (nameHoles h, value)
                                 | [ h1; h2 ] when nameMatches h1 tn && nameMatches h2 tn ->
                                     vecAdd hits (nameHoles h1, value)
                                 | _ -> ()
                         let ranked = vecToList hits |> List.sortBy fst
                         match ranked with
                         | [] -> None
                         | [ (_, v) ] -> Some v
                         // a tie at the same generality is the ambiguity the
                         // checker already rejects; leave it unresolved
                         | (n1, v) :: (n2, _) :: _ -> if n1 < n2 then Some v else None
                     let chosen =
                         match byOne with
                         | Some _ -> byOne
                         | None ->
                             match byTwo with
                             | Some _ -> byTwo
                             | None -> (match byHead with Some _ -> byHead | None -> byPattern ())
                     (match chosen with
                      | Some (fn, takesUnit) ->
                          // Only a template needs the instantiation; an
                          // ordinary instance member is one body and naming
                          // it with arguments would stamp copies nobody asked
                          // for.
                          let needsInst =
                              (dictTryFind layoutDependent (fn.Path, fn.Offset)) = Some true
                              && not (List.isEmpty hdArgs)
                          let plain = EVar (fn, mono (TCon ("?", [])))
                          let r =
                              if needsInst then stampRef fn (mono (TCon ("?", []))) hdArgs plain
                              else plain
                          // a value-like member (`static mempty = ...`) lifts
                          // as a function of unit, so the NAME applies it
                          if takesUnit then EApp (r, [ ELit LUnit ]) else r
                      | None -> EUnknown ("$class:" + cls + ":" + memberName + ":" + tn))
                 | _ -> EUnknown n)
            | ERecord (n, fs) -> ERecord (substName subst n, fs)
            | EField (x, fn, o) -> EField (x, fn, substName subst o)
            | EFieldSet (x, fn, o, v) -> EFieldSet (x, fn, substName subst o, v)
            | EArray (n, xs) -> EArray (substName subst n, xs)
            | EIndex (n, a, i) -> EIndex (substName subst n, a, i)
            | EIndexSet (n, a, i, v) -> EIndexSet (substName subst n, a, i, v)
            | EArrayLen (n, a) -> EArrayLen (substName subst n, a)
            | EArrayCreate (n, a, b) -> EArrayCreate (substName subst n, a, b)
            | EArrayPin (n, a) -> EArrayPin (substName subst n, a)
            | EArrayUnpin (n, a) -> EArrayUnpin (substName subst n, a)
            | EArrayBytes (n, a) -> EArrayBytes (substName subst n, a)
            | other -> other)

    /// Give a clone its own binder identities. Two stamped copies of the
    /// same template otherwise share parameter and local VarIds, and every
    /// backend table keyed by those (scalarized parameters, local kinds)
    /// would then leak state from one specialization into another.
    let alphaRename (delta : int) (e : Expr) : Expr =
        let bound = dictNew<string * int, bool> ()
        let rec collectPat (p : Pat) =
            match p with
            | PVar (v, _) -> dictSet bound (v.Path, v.Offset) true
            | PAs (inner, v, _) -> dictSet bound (v.Path, v.Offset) true; collectPat inner
            | PCtor (_, _, ps) | PTuple ps | PListLit ps | POr ps -> List.iter collectPat ps
            | PCons (h, t) -> collectPat h; collectPat t
            | PWild | PLit _ | PTypeTest _ -> ()
        // mapExpr visits every node; we only use it to gather binders
        mapExpr
            (fun x ->
                (match x with
                 | ELam (ps, _) -> for v, _ in ps do dictSet bound (v.Path, v.Offset) true
                 | ELet (_, v, _, _, _) -> dictSet bound (v.Path, v.Offset) true
                 | EMatch (_, cs) -> for p, _, _ in cs do collectPat p
                 | ETry (_, cs) -> for p, _, _ in cs do collectPat p
                 | _ -> ())
                x)
            e |> ignore
        let ren (v : VarId) =
            if (dictTryFind bound (v.Path, v.Offset)).IsSome then { v with Offset = v.Offset + delta } else v
        let rec renPat (p : Pat) =
            match p with
            | PVar (v, sc) -> PVar (ren v, sc)
            | PAs (inner, v, sc) -> PAs (renPat inner, ren v, sc)
            | PCtor (n, sc, ps) -> PCtor (n, sc, List.map renPat ps)
            | PTuple ps -> PTuple (List.map renPat ps)
            | PListLit ps -> PListLit (List.map renPat ps)
            | POr ps -> POr (List.map renPat ps)
            | PCons (h, t) -> PCons (renPat h, renPat t)
            | other -> other
        e
        |> mapExpr (fun x ->
            match x with
            | EVar (v, sc) -> EVar (ren v, sc)
            | EVarI (v, sc, inst) -> EVarI (ren v, sc, inst)
            | EAssign (v, rhs) -> EAssign (ren v, rhs)
            | ELam (ps, b) -> ELam (ps |> List.map (fun (v, sc) -> ren v, sc), b)
            | ELet (rc, v, sc, rhs, b) -> ELet (rc, ren v, sc, rhs, b)
            | EMatch (sc, cs) -> EMatch (sc, cs |> List.map (fun (p, g, b) -> renPat p, g, b))
            | ETry (b, cs) -> ETry (b, cs |> List.map (fun (p, g, x2) -> renPat p, g, x2))
            | other -> other)

    let out = vecNew<Decl> ()
    for d in decls do
        match d with
        | DLet (rc, v, sch, e) ->
            let isFunction = (match e with ELam _ -> true | _ -> false)
            // a TEMPLATE is a GENERIC layout-dependent function: its uses are
            // stamped, so symbolic demands inside it resolve per clone. A
            // MONOMORPHIC one is never cloned, so its symbolic demands must
            // be settled here rather than deferred forever.
            let isTemplate =
                isFunction
                && (dictTryFind layoutDependent (v.Path, v.Offset)) = Some true
                && not (List.isEmpty sch.Quantified)
            vecAdd out (DLet (rc, v, sch, rewrite v.Name (v.Path, v.Offset) (dictNew ()) isTemplate e))
        | other -> vecAdd out other

    // transitive closure: stamping a clone may demand further stamps
    // ---- per-instantiation vtables ----------------------------------------
    //
    // A member reached through a vtable keeps the canonical all-anyref
    // signature — that IS the dispatch contract — so it is never specialized,
    // and it would read a `'a[]` field at the uniform representation while a
    // C<int> holds a PACKED array. One class, one descriptor, one vtable,
    // shared by every instantiation: the cast fails.
    //
    // So each instantiation of a class that implements an interface becomes a
    // SUBCLASS of it. The stamped constructor allocates C$<int>, whose vtable
    // slots name the members stamped at int; everything else — the fields,
    // their order, the field reads that cast to C — is inherited and
    // unchanged, and `:? C` still answers true because the chain says so.
    let classImplsOf = dictNew<string, (string * (string * VarId) list) list> ()
    let classOwnOf = dictNew<string, (string * VarId) list> ()
    for d in decls do
        match d with
        // a class with OWN members and no direct impls still needs the
        // treatment: an override (MapVal's Compute) fills a base-declared
        // vtable slot, and only a stamped copy of it can run at this
        // instantiation
        | DClass (n, _, own, impls) when not (List.isEmpty impls) || not (List.isEmpty own) ->
            dictSet classImplsOf n impls
            dictSet classOwnOf n own
        | _ -> ()
    /// the class a constructor builds — a class' ctor is the top-level
    /// function that carries its name
    let classOfCtor = dictNew<string * int, string> ()
    for d in decls do
        match d with
        | DLet (_, v, _, ELam _) when (dictTryFind classImplsOf v.Name).IsSome ->
            dictSet classOfCtor (v.Path, v.Offset) v.Name
        | _ -> ()
    /// the instantiated subclasses to declare, in discovery order
    let instClasses = vecNew<string * string * (string * (string * VarId) list) list * (string * VarId) list> ()
    let instClassSeen = dictNew<string, bool> ()

    let mutable i = 0
    while i < vecLen queue do
        let key, inst = vecGet queue i
        (match dictTryFind bodies key with
         | Some (rc, v, sch, e) ->
             let mangled = mangleFor v inst
             let nv = { Path = v.Path; Offset = stampOffsetOf v.Offset mangled; Name = mangled }
             // map the callee's quantified vars to this instantiation so
             // demands nested in the body specialize too
             let subst = dictNew<string, string> ()
             if sch.Quantified.Length = inst.Length then
                 List.zip sch.Quantified inst
                 |> List.iter (fun (qv, n) -> dictSet subst ("#" + string (prunedId qv)) n)
             // A recursive call carries no instantiation: inside its own
             // body a function is monomorphic, so the self-call is a plain
             // EVar. In a stamped clone it must target the clone, not the
             // template that specialization removed.
             let selfKey = (v.Path, v.Offset)
             let selfFix (x : Expr) =
                 mapExpr
                     (fun y ->
                         match y with
                         | EVar (w, s2) when (w.Path, w.Offset) = selfKey -> EVar (nv, s2)
                         | other -> other)
                     x
             // this instantiation's own subclass, if the class has a vtable
             let instClass =
                 match dictTryFind classOfCtor key with
                 | Some cn ->
                     let sub = mangleInst cn inst
                     // one member stamp per interface method — the SAME
                     // instantiation the constructor got, so the member's
                     // quantified variables have to line up with it
                     // A member's quantified list is not the class' — it may
                     // carry variables of its own (an interface method's
                     // result type brings one). The class' parameters are
                     // found POSITIONALLY, through the receiver: whatever
                     // `self` is generic in gets this instantiation, and a
                     // variable the class does not name is unconstrained
                     // here, which is what canonical means.
                     let memberInst (msch : Scheme) : string list option =
                         match prune msch.Body with
                         | TFun (self, _) ->
                             (match prune self with
                              | TCon (n, args) when n = cn && args.Length = inst.Length ->
                                  let m = dictNew<int, string> ()
                                  List.zip args inst
                                  |> List.iter (fun (a, t) ->
                                        match prune a with
                                        | TVar v -> dictSet m v.Id t
                                        | _ -> ())
                                  Some (msch.Quantified
                                        |> List.map (fun q ->
                                              match dictTryFind m (prunedId q) with
                                              | Some t -> t
                                              | None -> "obj"))
                              | _ -> None)
                         | _ -> None
                     let stampMember (mv : VarId) : VarId =
                         match dictTryFind bodies (mv.Path, mv.Offset) with
                         | Some (_, _, msch, _) when not (List.isEmpty msch.Quantified) ->
                             (match memberInst msch with
                              | Some minst ->
                                  let minst = capInst minst
                                  let mm = mangleFor mv minst
                                  if not (dictTryFind seen mm).IsSome then
                                      dictSet seen mm true
                                      vecAdd queue ((mv.Path, mv.Offset), minst)
                                  { Path = mv.Path
                                    Offset = stampOffsetOf mv.Offset mm
                                    Name = mm }
                              | None -> mv)
                         | _ -> mv
                     if not (dictTryFind instClassSeen sub).IsSome then
                         dictSet instClassSeen sub true
                         let impls =
                             match dictTryFind classImplsOf cn with
                             | Some xs -> xs |> List.map (fun (ifn, ms) -> ifn, ms |> List.map (fun (mn, mv) -> mn, stampMember mv))
                             | None -> []
                         let own =
                             match dictTryFind classOwnOf cn with
                             | Some xs -> xs |> List.map (fun (mn, mv) -> mn, stampMember mv)
                             | None -> []
                         vecAdd instClasses (sub, cn, impls, own)
                     Some sub
                 | None -> None
             // allocate the subclass instead of the class itself
             let allocFix (x : Expr) =
                 match instClass with
                 | None -> x
                 | Some sub ->
                     let cn = (dictTryFind classOfCtor key) |> Option.defaultValue ""
                     mapExpr
                         (fun y ->
                             match y with
                             | ERecord (n, fs) when n = cn -> ERecord (sub, fs)
                             | ERecordExt (n, b, fs) when n = cn -> ERecordExt (sub, b, fs)
                             | other -> other)
                         x
             let clone =
                 DLet (rc, nv, substScheme inst sch,
                       alphaRename (10000000 + (abs (strHash mangled) % 1000000) * 10)
                           (allocFix (selfFix (rewrite mangled selfKey subst false e))))
             dictSet stamped mangled clone
         | None -> ())
        i <- i + 1

    // A layout-dependent template is normally unreachable — every use of one
    // is stamped — but "normally" is not "always": a use whose instantiation
    // is all-reference classifies CANON and keeps naming the template. So the
    // rule is reachability, measured AFTER rewriting: drop a template only if
    // nothing still refers to it. (Removing them unconditionally is how
    // `dictNew` became an unbound variable at two call sites, and an earlier
    // form of the same rule deleted `infer` and `emit` outright.)
    let stillNamed = dictNew<string * int, bool> ()
    let rec noteRefs (e : Expr) : unit =
        mapExpr
            (fun x ->
                (match x with
                 | EVar (v, _) | EVarI (v, _, _) -> dictSet stillNamed (v.Path, v.Offset) true
                 | _ -> ())
                x)
            e |> ignore
    for d in vecToList out do
        match d with
        | DLet (_, _, _, e) -> noteRefs e
        | _ -> ()
    for _, d in dictPairs stamped do
        match d with
        | DLet (_, _, _, e) -> noteRefs e
        | _ -> ()
    let emitted =
        vecToList out
        |> List.filter (fun d ->
            match d with
            | DLet (_, v, sch, ELam _) ->
                (dictTryFind layoutDependent (v.Path, v.Offset)) <> Some true
                || List.isEmpty sch.Quantified
                // A constructor forced into stamping by its class' vtable is
                // not a template: its own body is layout-free, and the call
                // sites that carry no instantiation — every construction at a
                // reference element type, where the canonical vtable is
                // already right — still name it. Dropping it made every such
                // call an "unbound variable HashSet".
                || (dictTryFind vtableCtor (v.Path, v.Offset)) = Some true
            | _ -> true)
    // the instantiated subclasses: no fields of their own, so they inherit
    // the class' layout exactly; only the vtable differs
    let instDecls =
        vecToList instClasses
        |> List.collect (fun (sub, cn, impls, own) ->
            [ DRecord (sub, [], [], false)
              DClass (sub, Some cn, own, impls) ])
    emitted @ (dictPairs stamped |> List.map snd) @ instDecls, vecToList errors

// The link step, v0: demand-closure over symbols. Roots are the program's
// top-level value initializers; only reachable functions survive. Tier-1
// instantiation stamping plugs in here once call sites carry instantiations.

let deadCodeEliminate (decls : Decl list) : Decl list =
    let keep = dictNew<string * int, bool> ()
    let bodies = dictNew<string * int, Expr> ()
    for d in decls do
        match d with
        | DLet (_, v, _, e) -> dictSet bodies (v.Path, v.Offset) e
        | _ -> ()
    let work = vecNew<string * int> ()
    let demand (k : string * int) =
        if not (dictTryFind keep k).IsSome then
            dictSet keep k true
            vecAdd work k
    let rec scan (e : Expr) =
        match e with
        | EVarI (v, _, _) -> demand (v.Path, v.Offset)
        | EVar (v, _) -> demand (v.Path, v.Offset)
        | ELam (_, b) -> scan b
        | EApp (f, args) -> scan f; List.iter scan args
        | ELet (_, _, _, r, b) -> scan r; scan b
        | EIf (a, b, c) -> scan a; scan b; scan c
        | EMatch (s, cs) ->
            scan s
            for _, g, b in cs do
                (match g with Some g -> scan g | None -> ())
                scan b
        | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) -> List.iter scan xs
        | ECtor (_, _, xs) -> List.iter scan xs
        | ERecord (_, fs) -> for _, v in fs do scan v
        | ERecordExt (_, bse, fs) -> scan bse; (for _, v in fs do scan v)
        | EField (r, _, _) -> scan r
        | EIfaceCall (_, _, recv, args) -> scan recv; List.iter scan args
        | ECast (_, x, _) -> scan x
        | ETypeTest (_, x) -> scan x
        | EFieldSet (r, _, _, v) -> scan r; scan v
        | EWhile (c, b) -> scan c; scan b
        | EAssign (v, e) -> demand (v.Path, v.Offset); scan e
        | ETry (b, cs) ->
            scan b
            for _, g, e in cs do
                (match g with Some g -> scan g | None -> ())
                scan e
        | EArray (_, xs) -> List.iter scan xs
        | EIndex (_, a, i) -> scan a; scan i
        | EIndexSet (_, a, i, v) -> scan a; scan i; scan v
        | EArrayLen (_, a) -> scan a
        | EArrayCreate (_, n, v) -> scan n; scan v
        | EArrayPin (_, a) -> scan a
        | EArrayUnpin (_, a) | EArrayBytes (_, a) -> scan a
        | _ -> ()
    // roots: members reached through a vtable. Nothing names them, so
    // scanning cannot find them — but only a class that is CONSTRUCTED can
    // have any of them called, so park them on the constructor (the DLet over
    // the type's own def) and demand them if and when construction turns out
    // to be reachable. Demanding them outright keeps every class in every
    // program: one class hierarchy in the prelude then costs each module its
    // whole vtable, used or not.
    //
    // A class whose constructor cannot be identified falls back to the
    // unconditional rule, which is never wrong, only bigger.
    // a class's constructor and every STAMPED clone of it: members parked on
    // the class must wake when ANY of them is demanded — a generic class is
    // usually constructed only through its stamps
    let classNames = dictNew<string, bool> ()
    for d in decls do
        match d with
        | DClass (n, _, _, _) -> dictSet classNames n true
        | _ -> ()
    let ctorKeys = dictNew<string, (string * int) list> ()
    for d in decls do
        match d with
        | DLet (_, v, _, ELam _) ->
            // a STAMP's mangled name is the template's name plus argument
            // segments; strip from the right until a class name appears
            let baseName =
                if v.Offset >= 500000000 && not (dictTryFind classNames v.Name).IsSome then
                    let mutable n = v.Name
                    let mutable go = true
                    while go do
                        match n.LastIndexOf '_' with
                        | i when i > 0 ->
                            n <- n.Substring (0, i)
                            if (dictTryFind classNames n).IsSome then go <- false
                        | _ -> go <- false
                    if (dictTryFind classNames n).IsSome then n else v.Name
                else v.Name
            let prev = match dictTryFind ctorKeys baseName with Some p -> p | None -> []
            dictSet ctorKeys baseName ((v.Path, v.Offset) :: prev)
        | _ -> ()
    /// members waiting for their class to be constructed somewhere
    let onCtor = dictNew<string * int, (string * int) list> ()
    /// did the members park on `cls`'s constructor?
    let parkOn (cls : string) (ms : (string * int) list) =
        match dictTryFind ctorKeys cls with
        | Some ks ->
            for k in ks do
                let prev = match dictTryFind onCtor k with Some p -> p | None -> []
                dictSet onCtor k (ms @ prev)
            true
        | None -> false
    for d in decls do
        match d with
        | DMembers (n, own) ->
            let ms = own |> List.map (fun (_, v) -> v.Path, v.Offset)
            // records and DUs declare members too, and those are not reached
            // through a constructor function
            if not (dictTryFind classNames n).IsSome || not (parkOn n ms) then
                for k in ms do demand k
        | DClass (n, _, own, impls) ->
            let ms =
                (own |> List.map (fun (_, v) -> v.Path, v.Offset))
                @ (impls
                   |> List.map (fun (_, mems) -> mems |> List.map (fun (_, v) -> v.Path, v.Offset))
                   |> List.concat)
            if not (parkOn n ms) then for k in ms do demand k
        | _ -> ()
    // ---- which initializers have to run at all? -----------------------------
    // A value binding is a root because its EFFECTS must happen. One that
    // cannot have effects only needs to run if the value is read, and an
    // unread pure global is dead weight: `HashMap.empty` alone would
    // otherwise root a class hierarchy's entire vtable, in every program.
    //
    // Conservative throughout: unresolved names, dynamic dispatch, mutation,
    // loops and exception handling all count as effects, and so does calling
    // anything that has them. Only a binding PROVEN effect-free is skipped.
    let directEffect = dictNew<string * int, bool> ()
    let calleesOf = dictNew<string * int, (string * int) list> ()
    let mutable sawEffect = false
    let mutable callAcc = vecNew<string * int> ()
    let rec walk (e : Expr) =
        match e with
        // an unresolved name is resolved by NAME at emit time, so what it
        // does is unknown here
        | EUnknown _ -> sawEffect <- true
        | EIfaceCall (_, _, recv, args) -> sawEffect <- true; walk recv; List.iter walk args
        | EAssign (_, x) -> sawEffect <- true; walk x
        | EFieldSet (r, _, _, v) -> sawEffect <- true; walk r; walk v
        | EIndexSet (_, a, i, v) -> sawEffect <- true; walk a; walk i; walk v
        | EWhile (c, b) -> sawEffect <- true; walk c; walk b
        | EArrayPin (_, a) -> sawEffect <- true; walk a
        | EArrayUnpin (_, a) -> sawEffect <- true; walk a
        | EArrayBytes (_, a) -> walk a
        | ETry (b, cs) ->
            sawEffect <- true
            walk b
            for _, g, x in cs do
                (match g with Some g -> walk g | None -> ())
                walk x
        // READING a name is pure, whatever the name holds: an effect happens
        // when something is CALLED, so only the callee position is an edge
        | EVarI (_, _, _) -> ()
        | EVar (_, _) -> ()
        | ELam (_, b) -> walk b
        | EApp (f, args) ->
            (match f with
             | EVar (v, _) -> vecAdd callAcc (v.Path, v.Offset)
             | EVarI (v, _, _) -> vecAdd callAcc (v.Path, v.Offset)
             // calling something computed — a parameter holding a function,
             // a field, a closure out of a list — has an unknown target
             | _ -> sawEffect <- true; walk f)
            List.iter walk args
        | ELet (_, _, _, r, b) -> walk r; walk b
        | EIf (a, b, c) -> walk a; walk b; walk c
        | EMatch (s, cs) ->
            walk s
            for _, g, b in cs do
                (match g with Some g -> walk g | None -> ())
                walk b
        | ETuple xs | EListLit xs | ESeq xs | EPrim (_, xs) -> List.iter walk xs
        | ECtor (_, _, xs) -> List.iter walk xs
        | ERecord (_, fs) -> for _, v in fs do walk v
        | ERecordExt (_, bse, fs) -> walk bse; (for _, v in fs do walk v)
        | EField (r, _, _) -> walk r
        | ECast (_, x, _) -> walk x
        | ETypeTest (_, x) -> walk x
        | EArray (_, xs) -> List.iter walk xs
        | EIndex (_, a, i) -> walk a; walk i
        | EArrayLen (_, a) -> walk a
        | EArrayCreate (_, n, v) -> walk n; walk v
        | _ -> ()
    for d in decls do
        match d with
        | DLet (_, v, _, e) ->
            sawEffect <- false
            callAcc <- vecNew<string * int> ()
            walk e
            dictSet directEffect (v.Path, v.Offset) sawEffect
            dictSet calleesOf (v.Path, v.Offset) (vecToList callAcc)
        | _ -> ()
    // propagate: a binding has effects if it does anything effectful itself or
    // reaches something that does
    let hasEffect = dictNew<string * int, bool> ()
    for k, eff in dictPairs directEffect do
        if eff then dictSet hasEffect k true
    let mutable changed = true
    while changed do
        changed <- false
        for k, cs in dictPairs calleesOf do
            if not (dictTryFind hasEffect k).IsSome then
                let reaches =
                    cs
                    |> List.exists (fun c ->
                        // a name with no binding of its own here (a parameter
                        // holding a function, a builtin) is opaque
                        (dictTryFind hasEffect c).IsSome
                        || not (dictTryFind directEffect c).IsSome)
                if reaches then
                    dictSet hasEffect k true
                    changed <- true
    let mustRun (k : string * int) = (dictTryFind hasEffect k).IsSome

    // roots: value initializers that have effects to deliver
    for d in decls do
        match d with
        | DLet (_, v, _, e) ->
            (match e with
             | ELam _ -> ()
             | _ ->
                 if mustRun (v.Path, v.Offset) then
                     demand (v.Path, v.Offset)
                     scan e)
        // an exported function is a root: the HOST is the caller, and
        // nothing in the program names it
        | DExport (v, _) -> demand (v.Path, v.Offset)
        | _ -> ()
    let mutable i = 0
    while i < vecLen work do
        let k = vecGet work i
        (match dictTryFind bodies k with
         | Some body -> scan body
         | None -> ())
        // this key is a constructor: everything reachable through the class's
        // vtable becomes reachable with it. A STAMPED constructor stands for
        // its template — members parked there become reachable too.
        (match dictTryFind onCtor k with
         | Some ms -> for m in ms do demand m
         | None -> ())

        i <- i + 1
    decls
    |> List.filter (fun d ->
        match d with
        | DLet (_, v, _, ELam _) -> (dictTryFind keep (v.Path, v.Offset)).IsSome
        | DExtern (v, _) -> (dictTryFind keep (v.Path, v.Offset)).IsSome
        // a value nobody reads, whose initializer cannot have an effect, does
        // not need to be computed — and dropping it drops whatever only its
        // initializer reached
        | DLet (_, v, _, _) ->
            (dictTryFind keep (v.Path, v.Offset)).IsSome || mustRun (v.Path, v.Offset)
        | _ -> true)

/// The bodies of the primitive instances. `instance Add<int,int>` declares
/// no member because `a + b` compiles to `i32.add`, but `Add.(+)` names the
/// member, and a name must denote a function. Generated here rather than
/// written in the prelude, because a prelude body would have to spell the
/// very operation it is defining — `compare` written with `<` at int would
/// call itself.
///
/// Only members the instance did NOT give a body get one here.
let builtinInstanceWrappers (classes : Classes.Tables) : Decl list =
    [ for cls, insts in dictPairs classes.Instances do
        match dictTryFind classes.Classes cls with
        | None -> ()
        | Some cd ->
            for i in vecToList insts do
                if i.Builtin then
                    for index, (m, msch) in List.indexed cd.Members do
                        let alreadyBodied = i.Members |> List.exists (fun (mn, _) -> mn = m)
                        // the operand types come from the head; the result
                        // from the associated type where the class has one
                        // (Add), and from the member's own signature where it
                        // does not (compare returns int)
                        let rec arity (t : Type) = match prune t with TFun (_, b) -> 1 + arity b | _ -> 0
                        let operands =
                            match i.Head with
                            | [ only ] -> List.replicate (max 1 (arity msch.Body)) only
                            | many -> many
                        let result =
                            match i.Assoc with
                            | [ (_, res) ] -> res
                            | _ ->
                                let rec ret (t : Type) = match prune t with TFun (_, b) -> ret b | other -> other
                                ret msch.Body
                        let im = Classes.wrapperMember i index m
                        let v = { Path = im.MPath; Offset = im.MOffset; Name = im.MName }
                        let ps =
                            operands
                            |> List.mapi (fun k t ->
                                { Path = im.MPath; Offset = im.MOffset * 16 + k; Name = "p" + string k }, mono t)
                        let sch = mono (List.foldBack (fun t acc -> TFun (t, acc)) operands result)
                        let args = ps |> List.map (fun (pv, psch) -> EVar (pv, psch))
                        let opnd = typeConName (List.head operands)
                        let prim (name : string) = EPrim (withOpType (name + "@") opnd, args)
                        let body =
                            match Classes.memberOperator m with
                            | Some op -> Some (prim (Classes.primOperator op))
                            // three-way comparison out of the two primitive
                            // predicates — the one place the ordering
                            // predicates are more primitive than `compare`
                            | None when m = "compare" ->
                                Some (EIf (EPrim (withOpType "<@" opnd, args),
                                           ELit (LInt "-1"),
                                           EIf (EPrim (withOpType ">@" opnd, args),
                                                ELit (LInt "1"),
                                                ELit (LInt "0"))))
                            // unary machine instructions
                            | None when m = "sqrt" || m = "abs" || m = "truncate" -> Some (prim m)
                            | None -> None
                        let emit =
                            match body with
                            | Some b -> if alreadyBodied then [] else [ DLet (false, v, sch, ELam (ps, b)) ]
                            | None -> []
                        yield! emit ]

/// Every instance member that has a function behind it — the bodies an
/// instance wrote, plus the wrappers generated for the primitive ones. This
/// is what a use site resolves against once monomorphization has made the
/// type concrete.
let instanceFunctions (classes : Classes.Tables) : Dict<string, VarId * bool> =
    let table = dictNew<string, VarId * bool> ()
    for cls, insts in dictPairs classes.Instances do
        match dictTryFind classes.Classes cls with
        | None -> ()
        | Some cd ->
            for i in vecToList insts do
                let heads = i.Head |> List.map typeConName
                for index, (m, _) in List.indexed cd.Members do
                    let key = instanceKey cls m heads
                    match i.Members |> List.tryPick (fun (mn, im) -> if mn = m then Some im else None) with
                    | Some im ->
                        dictSet table key
                            ({ Path = im.MPath; Offset = im.MOffset; Name = im.MName }, im.MTakesUnit)
                    | None ->
                        if i.Builtin then
                            let im = Classes.wrapperMember i index m
                            dictSet table key
                                ({ Path = im.MPath; Offset = im.MOffset; Name = im.MName }, im.MTakesUnit)
    // A GENERIC instance head registers under its mangled name — `list$<#28>`,
    // `Map$<#31.#32>` — because that is what the head type prints as. A
    // constraint discharged inside a generic function knows only the head
    // constructor (`list`), so register that spelling too and head-based
    // resolution finds the instance. Two instances of one class sharing a head
    // constructor would be overlapping instances: there is nothing safe to
    // pick, so those are left out rather than resolved arbitrarily.
    let stripHead (n : string) =
        let i = n.IndexOf "$<"
        if i <= 0 then n else n.Substring (0, i)
    let altCount = dictNew<string, int> ()
    let altValue = dictNew<string, VarId * bool> ()
    for key, value in dictPairs table do
        let parts = key.Split '|'
        if parts.Length = 3 then
            let heads = parts.[2].Split '@' |> Array.toList
            let stripped = heads |> List.map stripHead
            if stripped <> heads then
                let alt = parts.[0] + "|" + parts.[1] + "|" + String.concat "@" stripped
                if not (dictTryFind table alt).IsSome then
                    let prev = match dictTryFind altCount alt with Some c -> c | None -> 0
                    dictSet altCount alt (prev + 1)
                    dictSet altValue alt value
    for alt, n in dictPairs altCount do
        if n = 1 then
            match dictTryFind altValue alt with
            | Some v -> dictSet table alt v
            | None -> ()
    table

/// Monomorphize with no user instances in play.
let monomorphize (isStructName : string -> bool) (decls : Decl list) : Decl list * string list =
    monomorphizeWith isStructName (dictNew ()) decls
