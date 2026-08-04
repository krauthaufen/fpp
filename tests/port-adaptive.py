#!/usr/bin/env python3
"""Port the WHOLE of FSharp.Data.Adaptive to F++, in compile order.

The acceptance criterion is the library's own: the heart — the algorithms,
the data structures, the adaptive machinery — is untouched. What gets
replaced is every dependency on a runtime service F++ does not have.

The library also targets Fable, and that branch is tempting: no reflection,
no threading, no weak references. It is not what this port takes. Fable's
WeakReference never dies, its Monitor is a no-op and its
ShallowEqualityComparer is reference equality — changes to the semantics of
the heart, which is the one thing that must survive. So the port takes the
.NET branch, and the runtime surface it expects (Monitor, Interlocked,
WeakReference) is provided in the F++ prelude, honestly, with its
divergences written down.

Reflection is the part with no runtime answer, and it gets a LANGUAGE one:
`ShallowEqualityComparer<'a>` builds a comparer per type with DynamicMethod,
which is what a typeclass with overlapping instances does at compile time.

Run:  python3 tests/port-adaptive.py <FSharp.Data.Adaptive/src/...> <out.fpp>
"""
import os, re, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import importlib.util
_spec = importlib.util.spec_from_file_location(
    "portref", os.path.join(os.path.dirname(os.path.abspath(__file__)), "port-reference.py"))
_portref = importlib.util.module_from_spec(_spec)
# port-reference.py runs its own main at import; feed it a no-op argv
_argv = sys.argv
sys.argv = ["port-reference", os.devnull, os.devnull]
try:
    _spec.loader.exec_module(_portref)
finally:
    sys.argv = _argv

pick_branch = _portref.pick_branch
strip_attrs = _portref.strip_attrs
port_closures = _portref.port_closures
dotnet_exception_ctors = _portref.dotnet_exception_ctors
drop_dotnet_interop_interfaces = _portref.drop_dotnet_interop_interfaces
drop_fsharp_core_set_bridges = _portref.drop_fsharp_core_set_bridges


def drop_fable_interop(src):
    """`[<Emit("$0 === $1")>] let equals a b : bool = jsNative` is Fable's way
    of reaching JavaScript. F++ has the same operations as primitives, so the
    declaration is replaced by the primitive it stands for."""
    # `[<Emit("$0 === $1")>] let f ... = jsNative` — reference equality
    src = re.sub(r'\[<Emit\("\$0 === \$1"\)>\]\s*\n(\s*)let (\w+) ([^=]*)= jsNative',
                 lambda m: m.group(1) + "let " + m.group(2) + " " + m.group(3) + "= refEq a b",
                 src)
    # Fable's WeakMap under ConditionalWeakTable: a strong Dictionary here,
    # which is what the FABLE WeakReference already amounts to
    src = src.replace("Fable.Core.JS.WeakMap.Create<'K, 'V> []", "Dictionary<'K, 'V>()")
    src = re.sub(r"^\s*open Fable\.Core.*$", "", src, flags=re.M)
    return src


# Files with no port, only a REPLACEMENT: what they provide is a runtime
# service F++ does not have, and the replacement provides it another way.
# `tests/adaptive-shims/<name>.fpp` is the substitute.
REPLACED = {"ShallowEquality.fs": "ShallowEquality.fpp", "Equality.fs": "Equality.fpp"}


def rewrite_shallow_calls(src):
    """`ShallowEqualityComparer<'T>.Instance` and `.ShallowEquals(a, b)` are
    a type with class-constrained statics, which is not expressible yet; the
    replacement offers the same three operations as constrained functions."""
    src = re.sub(r"ShallowEqualityComparer<[^>]*>\.Instance\.GetHashCode\s+(\w+)",
                 r"shallowHashCode \1", src)
    src = re.sub(r"ShallowEqualityComparer<[^>]*>\.Instance\.Equals\(([^,]+),\s*([^)]+)\)",
                 r"shallowEqualsOf (\1) (\2)", src)
    src = re.sub(r"ShallowEqualityComparer(<[^>]*>)?\.ShallowEquals\(([^,]+),\s*([^)]+)\)",
                 r"shallowEqualsOf (\2) (\3)", src)
    src = re.sub(r"ShallowEqualityComparer<[^>]*>\.Instance", "shallowComparer ()", src)
    return src


def strip_namespace_headers(src, first):
    """One F++ module for the whole library: the files share a namespace, and
    concatenating them is what makes the port a single compilation."""
    out = []
    for line in src.split("\n"):
        t = line.strip()
        if t.startswith("namespace "):
            continue
        if t.startswith("module ") and t.endswith(" =") is False and " " in t and first:
            pass
        out.append(line)
    return chr(10).join(out)


def dotnet_hashset(src):
    """`HashSet<T>` is System.Collections.Generic's when the file's HEADER
    opens that namespace last. F# is last-open-wins — measured, not assumed —
    so a header open applies to the whole file and decides every bare use in
    it.

    HEADER opens only. `Deltas.fs` opens the namespace INSIDE a module, which
    binds only there, and reading the whole file for the last occurrence
    rewrote uses that mean the library's own type — it moved the frontier
    backwards by 1,400 lines.

    This is the harness's mess to clean up rather than a change to what the
    library means: flattening every namespace into one module is what
    destroys the shadowing, and F++ identifies a type by its bare NAME, so
    two called `HashSet` merge (DIVERGENCES.md — it is also why the prelude's
    mutable set is `MutableHashSet`). Until a type can be told apart by more
    than its name, the resolution F# performed has to be replayed here.
    """
    header = src.split("\nmodule ")[0].split("\ntype ")[0].split("\n[<")[0]
    generic = header.rfind("open System.Collections.Generic")
    if generic < 0:
        return src
    if header.rfind("open FSharp.Data.Adaptive") > generic:
        return src
    # not in the file that DECLARES it: inside `HashCollections.fs` every
    # `HashSet<'T>` is the one being defined, all 77 of them
    if re.search(r"^\s*(type|and)\s+HashSet\b", src, re.M):
        return src
    return re.sub(r"\bHashSet\s*<", "MutableHashSet<", src)


def port(path, first):
    src = open(path, encoding="utf-8-sig").read()
    # The .NET branch, not the Fable one: Fable's WeakReference never dies,
    # its Monitor is a no-op and its ShallowEqualityComparer is plain
    # reference equality. Those are changes to the HEART, not to the
    # reflection, and the point of this port is that the heart survives.
    src = pick_branch(src, defined=())
    src = port_closures(src)
    src = strip_attrs(src)
    src = dotnet_exception_ctors(src)
    src = drop_fsharp_core_set_bridges(src)
    src = rewrite_shallow_calls(src)
    src = drop_dotnet_interop_interfaces(src)
    src = dotnet_hashset(src)
    src = strip_namespace_headers(src, first)
    if path.endswith("AdaptiveIndexList.fs"):
        # this file's Cache is keyed by a STRUCT tuple; the calls pass the
        # elements bare and F++ does not adapt plain to struct tuples
        src = src.replace("cache.TryRevoke(i, ov)", "cache.TryRevoke(struct (i, ov))")
        src = src.replace("cache.TryRevoke(i, v)", "cache.TryRevoke(struct (i, v))")
        src = src.replace("cache.Invoke(i,v)", "cache.Invoke(struct (i, v))")
    return src


def qualify_colliding_types(src):
    """F++ keys types by BARE NAME, so two types of one name declared in
    DIFFERENT modules become one type. The library does that a lot — a private
    `Traceable` sits in three modules, and `MapReader`/`ChooseReader`/
    `AValReader` in both the hash-set and the index-list implementation.
    Merged, `IndexList.trace` answered with the HashSet one.

    F# tells them apart by their enclosing module, and so does IL. This does
    the same textually: the SECOND and later declarations of a name, when they
    sit inside a `module X =`, are renamed `X_Name` within that module's
    extent. The first keeps the plain name, so the deliberate merge with a
    same-named prelude type is untouched.

    A porting transformation, not a fix — see DIVERGENCES.md.
    """
    lines = src.split("\n")
    # `and` also continues a property (`with get() ... and inline set v = ...`),
    # so a declaration is only one when the name is followed by `<`, `(` or `=`
    # ONLY `private` types. A public one is referenced from outside its
    # module, and renaming it inside the module alone breaks those references
    # — measured: renaming everything that collides is WORSE than renaming
    # nothing (263 diagnostics against 259), while the private ones alone
    # take it to 245.
    decl = re.compile(r"^(\s*)(?:type|and)\s+private\s+"
                      r"([A-Za-z_][A-Za-z0-9_]*)\s*(?=[<(=])")
    # any declaration, for collision detection between a module-nested type
    # and a later TOP-LEVEL one of the same name (AVal.AbstractVal vs the
    # public AbstractVal): there the NESTED one is renamed — its references
    # all sit inside its module extent, the top-level one is the public API
    decl_any = re.compile(r"^(\s*)(?:type|and)\s+(?:private\s+|internal\s+)?"
                          r"([A-Za-z_][A-Za-z0-9_]*)\s*(?=[<(=])")
    modl = re.compile(r"^(\s*)module\s+(?:private\s+|internal\s+)?([A-Za-z_][A-Za-z0-9_.]*)\s*=\s*$")

    def enclosing(ln, ind):
        """nearest `module X =` above `ln` with a smaller indent, and its extent"""
        for j in range(ln - 1, -1, -1):
            m = modl.match(lines[j])
            if m and len(m.group(1)) < ind:
                mi = len(m.group(1))
                end = len(lines)
                for k in range(j + 1, len(lines)):
                    l = lines[k]
                    if l.strip() and (len(l) - len(l.lstrip())) <= mi:
                        end = k
                        break
                return m.group(2).split(".")[-1], j + 1, end
            # a module at the SAME (or deeper) indent is a closed SIBLING
            # scope above us, not the enclosing one — walk past it
        return None

    # `and` opens a property accessor too (`and inline set v = ...`); these
    # are never type names, and renaming one rewrites the KEYWORD
    KEYWORDS = {"set", "get", "inline", "new", "val", "member", "this", "static",
                "mutable", "rec", "of", "with", "abstract", "override", "default"}
    seen, renames = {}, []
    # seed with EVERY declaration: a private type whose name collides with an
    # EARLIER public one (module HashSet's `type private Traceable<'T>` vs the
    # core Traceable record) must rename too — tracking only private decls let
    # the first private collision through unrenamed
    for i, l in enumerate(lines):
        d = decl_any.match(l)
        if d and d.group(2) not in KEYWORDS and d.group(2) not in seen:
            seen[d.group(2)] = i
    for i, l in enumerate(lines):
        d = decl.match(l)
        if not d:
            continue
        name = d.group(2)
        if name in KEYWORDS:
            continue
        if seen.get(name) == i:
            continue
        enc = enclosing(i, len(d.group(1)))
        if enc is not None:
            n = 1 + lines[i][d.end():].split(">")[0].count(",") if "<" in lines[i][d.end():d.end()+2] else 0
            renames.append((name, enc[0] + "_" + name, enc[1], enc[2], n))
    # NON-private colliding types (three MapReaders, one per collection
    # family): each family lives inside ONE source file, so the rename runs
    # from the declaration to the file's end marker. Arity-guarded like the
    # private pass, so a same-name type of a different arity is untouched.
    file_marks = [i for i, l in enumerate(lines) if l.startswith("// ==== ")]
    def file_end(ln):
        for m in file_marks:
            if m > ln:
                return m
        return len(lines)
    decl_pub = re.compile(r"^(\s*)(?:type|and)\s+(?:internal\s+)?"
                          r"([A-Za-z_][A-Za-z0-9_]*)\s*(?=[<(=])")
    already = set((r[0], r[2]) for r in renames)
    for i, l in enumerate(lines):
        d = decl_pub.match(l)
        if not d:
            continue
        # `type X<'T> with` AUGMENTS the existing type; it declares nothing
        if l.rstrip().endswith(" with"):
            continue
        name = d.group(2)
        # `already` holds (name, extent-start): the same bare name may need
        # renaming in SEVERAL disjoint module extents (three AValReaders)
        if name in KEYWORDS or (name, i) in already:
            continue
        if seen.get(name) is None or seen.get(name) >= i:
            continue
        enc = enclosing(i, len(d.group(1)))
        if enc is None:
            continue
        n = 1 + lines[i][d.end():].split(">")[0].count(",") if "<" in lines[i][d.end():d.end()+2] else 0
        renames.append((name, enc[0] + "_" + name, i, file_end(i), n))
        already.add((name, i))
    # module-nested vs later top-level: rename the NESTED declaration
    seen_any = {}
    for i, l in enumerate(lines):
        d = decl_any.match(l)
        if not d:
            continue
        name = d.group(2)
        if name in KEYWORDS:
            continue
        if name not in seen_any:
            seen_any[name] = (i, len(d.group(1)))
            continue
        pi, pind = seen_any[name]
        if len(d.group(1)) == 0 and pind > 0 and not any(r[0] == name for r in renames):
            enc = enclosing(pi, pind)
            if enc is not None:
                dp = decl_any.match(lines[pi])
                n = 1 + lines[pi][dp.end():].split(">")[0].count(",") if "<" in lines[pi][dp.end():dp.end()+2] else 0
                renames.append((name, enc[0] + "_" + name, enc[1], enc[2], n))

    def arity_at(line, k):
        depth, commas, j = 0, 0, k
        while j < len(line):
            c = line[j]
            if c == "<":
                depth += 1
            elif c == ">":
                depth -= 1
                if depth == 0:
                    return commas + 1
            elif c == "," and depth == 1:
                commas += 1
            j += 1
        return None

    for old, new_name, a, b, decl_arity in renames:
        pat = re.compile(r"(?<![A-Za-z0-9_.])" + re.escape(old) + r"\b")
        for i in range(a, min(b, len(lines))):
            def sub(m):
                # the GLOBAL type of this name may appear in the same module
                # at a DIFFERENT arity — `static let trace : Traceable<'S,'D>`
                # inside the renamed cache class means the record, not the
                # cache. The written argument count says which.
                line = lines[i]
                j = m.end()
                while j < len(line) and line[j] == " ":
                    j += 1
                if j < len(line) and line[j] == "<":
                    n = arity_at(line, j)
                    if n is not None and n != decl_arity:
                        return m.group(0)
                return new_name
            lines[i] = pat.sub(sub, lines[i])
    return "\n".join(lines)


def rewrite_keyvalue_binders(src):
    """`for (KeyValue(k, v)) in d do` — the KeyValue view as a BINDER. F++
    has no single-case active patterns, so the port binds the pair itself
    and destructures in two lets, which is the same program."""
    out = []
    counter = [0]
    pat = re.compile(r"^(\s*)for\s*\(KeyValue\s*\((.*)\)\)\s+in\s+(.*?)\s+do\s*(//.*)?$")
    for line in src.split("\n"):
        m = pat.match(line)
        if not m:
            out.append(line)
            continue
        ind, inner, source = m.group(1), m.group(2), m.group(3)
        # split the pair pattern at the TOP-level comma
        depth, cut = 0, -1
        for i, c in enumerate(inner):
            if c in "([<":
                depth += 1
            elif c in ")]>":
                depth -= 1
            elif c == "," and depth == 0:
                cut = i
                break
        kp, vp = inner[:cut].strip(), inner[cut+1:].strip()
        counter[0] += 1
        kv = "kvp%d" % counter[0]
        out.append("%sfor %s in %s do" % (ind, kv, source))
        if kp != "_":
            out.append("%s    let %s = %s.Key" % (ind, kp, kv))
        if vp != "_":
            # a parenthesised pair over a STRUCT payload needs F#'s own
            # `let struct (...)` spelling; Cache.fs's is the one such site
            if vp == "(v,_)":
                out.append("%s    let struct (v, _) = %s.Value" % (ind, kv))
            else:
                out.append("%s    let %s = %s.Value" % (ind, vp, kv))
    return chr(10).join(out)


EXCISED = ["AdaptiveSynchronizationContext"]

# Targeted spot-rewrites, applied verbatim. Each is a documented divergence.
SPOT = [
    # VolatileSetData is [<Struct>] purely as a .NET optimization ("~10%
    # faster transactions than unbox", says its comment). Here a class with
    # F++'s synthesized zero-init unit constructor is the same program:
    # `data` has exactly one owner and is only ever mutated through it.
    ("and [<Struct>] private VolatileSetData =",
     "and private VolatileSetData() ="),
    ("Unchecked.defaultof<VolatileSetData>",
     "VolatileSetData()"),
    # ConcurrentDictionary minus the concurrency IS the prelude Dictionary
    # (single-threaded wasm); TryAdd/TryRemove exist there with the same
    # shapes. Callbacks.fs is the only user.
    ("System.Collections.Concurrent.ConcurrentDictionary",
     "Dictionary"),
    # `List<T>()` constructs through a type ABBREVIATION, which F++ cannot
    # emit; the target's own name can. One site (Index garbage collection).
    ("let all = List<IndexNode>()",
     "let all = ResizeArray<IndexNode>()"),
    # the prelude Dictionary/MutableHashSet hash structurally and IGNORE a
    # passed comparer (see the prelude's comparer ctor); passing
    # DefaultEqualityComparer — itself the structural default — is the
    # identity, and the property-as-argument shape trips ctor selection
    ("Dictionary<'Key, 'Value>(DefaultEqualityComparer<'Key>.Instance)",
     "Dictionary<'Key, 'Value>()"),
    ("MutableHashSet<'T>(DefaultEqualityComparer<'T>.Instance)",
     "MutableHashSet<'T>()"),
    # fully qualified .NET collection names resolve to nothing here — the
    # prelude's types answer to their BARE names only
    ("System.Collections.Generic.Dictionary",
     "Dictionary"),
    ("System.Collections.Generic.MutableHashSet",
     "MutableHashSet"),
    # the .NET comparer factory, as the Ordered typeclass: same decision,
    # made at compile time
    # a generic class's static-let initializer runs ONCE at program start
    # with the parameter unresolved (see DIVERGENCES.md on generic values),
    # so the comparer becomes a FUNCTION and every read a call
    ("static let defaultComparer = LanguagePrimitives.FastGenericComparer<'Key>",
     "static let defaultComparer () = { new IComparer<'Key> with member __.Compare(a : 'Key, b : 'Key) = compare a b }"),
    ("static let empty = MapExt<'Key, 'Value>(defaultComparer, null)",
     "static let empty () = MapExt<'Key, 'Value>(defaultComparer (), null)"),
    ("let cmp = defaultComparer\n",
     "let cmp = defaultComparer ()\n"),
    # only MapExt's Empty reads the THUNKED empty; the FromSeq neighbour
    # makes the site unique
    ("    static member Empty = empty\n    static member FromSeq",
     "    static member Empty = empty ()\n    static member FromSeq"),
    # the other in-class reads of MapExt's thunked statics
    ("            empty, None, x",
     "            empty (), None, x"),
    ("            x, None, empty\n",
     "            x, None, empty ()\n"),
    ("    static let empty = IndexList<'T>(Index.zero, Index.zero, MapExt.empty)",
     "    static let empty () = IndexList<'T>(Index.zero, Index.zero, MapExt.empty)"),
    ("    static member Empty = empty\n\n    /// The smallest Index",
     "    static member Empty = empty ()\n\n    /// The smallest Index"),
    ("    static let empty = IndexListDelta<'T>(MapExt.empty)\n    static member Empty = empty",
     "    static let empty () = IndexListDelta<'T>(MapExt.empty)\n    static member Empty = empty ()"),
    # typeof<'T>.IsValueType picks the null test; here a value type is
    # boxed the moment it is 'T1, and a boxed value is never null — the
    # reference arm is right for both
    ("""    static let isNull =
        if typeof<'T1>.IsValueType then fun (_o : 'T1) -> false
        else fun (o : 'T1) -> isNull (o :> obj)""",
     """    static let isNull = fun (o : 'T1) -> isNull (o :> obj)"""),
    # IsAssignableFrom is reflection; the identity cast stands in, and a
    # genuinely wrong cast surfaces at the use instead of as None here
    ("""        static let cast =
            if typeof<'b>.IsAssignableFrom typeof<'a> then
                Some (fun (a : 'a) -> unbox<'b> a)
            else
                None""",
     """        static let cast =
            Some (fun (a : 'a) -> unbox<'b> a)"""),
    # the generic zero, as the prelude's own class member
    ("LanguagePrimitives.GenericZero", "Zero"),
    ("LanguagePrimitives.GenericOne", "One"),
    # `static val mutable` storage, as a static let: AdaptiveObject is not
    # generic, so the once-per-program initializer is exactly right
    ("    static val mutable private CurrentEvaluationDepth : int",
     "    static let mutable CurrentEvaluationDepth = 0"),
    ("LanguagePrimitives.FastGenericComparer<'Key>",
     "{ new IComparer<'Key> with member __.Compare(a : 'Key, b : 'Key) = compare a b }"),
    ("LanguagePrimitives.FastGenericComparer<Index>",
     "{ new IComparer<Index> with member __.Compare(a : Index, b : Index) = compare a b }"),
    ("LanguagePrimitives.FastGenericComparer<'T2>",
     "{ new IComparer<'T2> with member __.Compare(a : 'T2, b : 'T2) = compare a b }"),
    ("LanguagePrimitives.FastGenericComparer",
     "{ new IComparer<_> with member __.Compare(a, b) = compare a b }"),
    ("MutableHashSet<'T>(ReferenceEqualityComparer<'T>.Instance)",
     "MutableHashSet<'T>()"),
]

# F++ has no user exception TYPES (exn is the prelude's closed DU), so
# LevelChangedException rides in a Failure with an encoded message. The level
# survives as "!level:N"; the catch sites decode it. See DIVERGENCES.md.
LEVEL_EXC = [
    # the Cache's dictionary stores STRUCT tuples; say so in the patterns —
    # a plain comma pattern relies on a deferred struct mark that the parked
    # TryGetValue view resolves too late inside a template
    ("| (true, (r, ref)) ->", "| (true, struct (r, ref)) ->"),
    ("cache.[v] <- (r, ref 1)", "cache.[v] <- struct (r, ref 1)"),

    # ctor property-initializer syntax with a POSITIONAL argument mixed in is
    # not lowered; say the writes out loud
    ("""            let res = IndexNode(x.Root, Prev = x, Next = next, Tag = key)""",
     """            let res = IndexNode(x.Root)
            res.Prev <- x
            res.Next <- next
            res.Tag <- key"""),

    # the flexible-return widening picks a wrong pairing for this one ctor;
    # the explicit upcast says what F# would have inserted
    ("ofReader (fun () -> SortWithReader(list, compare))",
     "ofReader (fun () -> SortWithReader(list, compare) :> IOpReader<IndexListDelta<_>>)"),

    # Index and the comparer wrappers need their class instances said in
    # F++'s own words: MinMax has no derivation from Ordered, and
    # ReversedCompare's ordering lives in interface impls the auto
    # CompareTo->Ordered rule does not read
    ("""/// internal type used for properly handling of decorator objects (as introduced in AVal.mapNonAdaptive)""",
     """instance MinMax<Index>
    static min (a : Index) (b : Index) = if compare a b < 0 then a else b
    static max (a : Index) (b : Index) = if compare a b > 0 then a else b

/// internal type used for properly handling of decorator objects (as introduced in AVal.mapNonAdaptive)"""),

    # an override's parameter types are not yet taken from the base abstract
    # signature; the dirty-set parameter needs its type said out loud
    ("override x.Compute(token, dirty) =",
     "override x.Compute(token, dirty : MutableHashSet<_>) ="),
    ("override x.Compute(token,dirty) =",
     "override x.Compute(token, dirty : MutableHashSet<_>) ="),

    # the BCL HashSet IS the prelude's MutableHashSet; qualified spellings too
    ("System.Collections.Generic.HashSet<", "MutableHashSet<"),
    ("FSharp.Data.Traceable.", ""),
    # F# 6 dotless indexers parse as application of a list
    ("cache[struct(r, i)] <-", "cache.[struct(r, i)] <-"),
    ("cache[n] <-", "cache.[n] <-"),
    # range slices on keyed collections go through GetSlice explicitly
    ("reader.State.[newMin .. newMax]",
     "reader.State.GetSlice(Some newMin, Some newMax)"),
    ("ops.Content.[sharedMin .. sharedMax]",
     "ops.Content.GetSlice(Some sharedMin, Some sharedMax)"),

    # the prelude Dictionary has no comparer-taking constructor (F++ has no
    # secondary ctors) and hashes structurally anyway
    ("Dictionary<'B, int>(DefaultEqualityComparer<'B>.Instance)",
     "Dictionary<'B, int>()"),

    # RuntimeHelpers.GetHashCode is the reference-identity hash; F++'s `hash`
    # on a class with no GetHashCode override IS the identity hash
    ("let hash = RuntimeHelpers.GetHashCode value |> uint32",
     "let hash = hash value |> uint32"),
    # ... so an override SAYING identity is the default spelled out: drop it
    ("        override x.GetHashCode() = System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode(x)\n",
     ""),
    ("        System.Runtime.CompilerServices.RuntimeHelpers.GetHashCode (obj :> obj)",
     "        hash obj"),

    # a static let is in scope BARE inside its own class; the qualified spelling
    # (AdaptiveObject.CurrentEvaluationDepth) lowers to an unknown field
    ("with get() = AdaptiveObject.CurrentEvaluationDepth",
     "with get() = CurrentEvaluationDepth"),
    ("and set v = AdaptiveObject.CurrentEvaluationDepth <- v",
     "and set v = CurrentEvaluationDepth <- v"),
    # F++ has no reraise(); the catch binds the exception and raises it back
    ("""            with _ ->
                AdaptiveObject.UnsafeEvaluationDepth <- depth
                Monitor.Exit x
                reraise()""",
     """            with e ->
                AdaptiveObject.UnsafeEvaluationDepth <- depth
                Monitor.Exit x
                raise e"""),

    ("""exception LevelChangedException of 
    /// The new level for the top-level object.
    newLevel : int""",
     """// exception LevelChangedException -> encoded as Failure "!level:N": F++
// has no user exception types; raise/catch sites decode the level.
let internal isLevelMsg (msg : string) = msg.StartsWith "!level:"
let internal levelOfMsg (msg : string) = int (msg.Substring 7)"""),
    ("raise <| LevelChangedException(x.Level + depth)",
     'raise (Failure ("!level:" + string (x.Level + depth)))'),
    ("""                            with LevelChangedException newLevel ->""",
     """                            with Failure msg when isLevelMsg msg ->
                                let newLevel = levelOfMsg msg"""),
    ("""                with :? LevelChangedException ->""",
     """                with Failure msg when isLevelMsg msg ->"""),
]


def rewrite_lazy_keyword(src):
    """`lazy expr` is a keyword F++ does not lower; the prelude's Lazy class
    says the same thing as a constructor call."""
    out, i = [], 0
    while True:
        k = src.find("lazy (", i)
        if k < 0:
            out.append(src[i:])
            break
        if k > 0 and (src[k - 1].isalnum() or src[k - 1] == "_"):
            out.append(src[i:k + 6])
            i = k + 6
            continue
        j = _portref.matchto(src, k + 6, "(", ")")
        inner = src[k + 6:j - 1]
        out.append(src[i:k])
        out.append("Lazy(fun () -> (" + inner + "))")
        i = j
    return "".join(out)


def rewrite_bare_list(src):
    """`List<...>` (System.Collections.Generic.List) IS ResizeArray, which is
    the name the prelude declares it under -- one spelling, everywhere."""
    return re.sub(r"\bList<", "ResizeArray<", src)


def rewrite_static_val_mutable(src):
    """`static val mutable private X : T` has no F++ lowering; a
    `static let mutable X = Unchecked.defaultof<T>` is the same zero-initialized
    slot. The private qualified self-references (Owner.X) become bare reads --
    private means no reference exists outside the class. See DIVERGENCES.md."""
    lines = src.split(chr(10))
    renames = []
    cur_type = None
    for i, l in enumerate(lines):
        m = re.match(r"\s*type\s+(?:internal\s+|private\s+)?(\w+)", l)
        if m:
            cur_type = m.group(1)
        m = re.match(r"(\s*)static val mutable private (\w+) : (.+?)\s*$", l)
        if m and cur_type:
            ind, name, ty = m.groups()
            # a NULL default falls through an exhaustive ValueSome/ValueNone
            # match -- a DU-typed slot needs its real empty case
            init = "ValueNone" if ty.startswith("ValueOption") else "Unchecked.defaultof<" + ty + ">"
            lines[i] = ind + "static let mutable " + name + " : " + ty + " = " + init
            renames.append((cur_type, name))
    src = chr(10).join(lines)
    for owner, name in renames:
        src = re.sub(r"\b" + owner + r"\." + name + r"\b", name, src)
    return src


def inject_after_type(src, type_header, block):
    """Insert `block` after the extent of the type declared by `type_header`
    (the first following non-blank line at an indent <= the header's)."""
    i = src.index(type_header)
    lines = src[i:].split(chr(10))
    ind = len(lines[0]) - len(lines[0].lstrip())
    end = len(lines)
    for j in range(1, len(lines)):
        l = lines[j]
        if l.strip() and (len(l) - len(l.lstrip())) <= ind and not l.lstrip().startswith("//"):
            end = j
            break
    pos = i + sum(len(l) + 1 for l in lines[:end])
    return src[:pos] + block + chr(10) + src[pos:]


# CallbackDisposable pins itself with a GCHandle so a weakly-referenced
# subscription outlives collection. This runtime's WeakReference IS strong
# (prelude), so there is nothing to pin — the handle becomes a flag.
SPOT.append((
    "    let mutable gc = if makeGCRoot then GCHandle.Alloc(this) else Unchecked.defaultof<GCHandle>",
    "    let mutable gc = makeGCRoot"))
SPOT.append((
    """            if gc.IsAllocated then 
                gc.Free()
                gc <- Unchecked.defaultof<GCHandle>""",
    """            if gc then
                gc <- false"""))

REGEX_SPOTS = [
    # ValueOption's intrinsic .Value has no equivalent here (adding a Value
    # member to the union stole every deferred `.Value` by-name pick)
    (r"let t = Transaction\.Running\.Value",
     'let t = (match Transaction.Running with ValueSome tt -> tt | ValueNone -> failwith "no running transaction")'),
    # a bare obj() exists only to be a LOCK TOKEN; lock here is a no-op
    # (single-threaded), any reference value serves
    (r"= obj\(\)", r"= box 0"),
    # HashMapEnumerator's Mapping field is a PLAIN curried function; F#
    # tolerates .Invoke on it, this language applies it
    (r"x\.Mapping\.Invoke\(([^,]+), ([^)]+)\)",
     r"x.Mapping \1 \2"),
    # MapExt enumerated as KeyValuePairs: go through ToSeq and plain tuples
    (r"GetChanges\(token\)\.Content\s*\n(\s*)\|> Seq\.collect \(fun \(KeyValue\((\w+), (\w+)\)\) ->",
     r"GetChanges(token).Content.ToSeq()\n\1|> Seq.collect (fun (\2, \3) ->"),
    # HashSetDelta enumerated by Seq.*: through toSeq (the port dropped the
    # BCL enumerator interfaces)
    (r"reader\.GetChanges token \|> Seq\.choose \(fun op ->",
     r"reader.GetChanges token |> HashSetDelta.toSeq |> Seq.choose (fun op ->"),
]


def rewrite_regex_spots(src):
    for pat, rep in REGEX_SPOTS:
        src2 = re.sub(pat, rep, src)
        assert src2 != src or re.search(pat, src) is None, "REGEX_SPOT missing: " + pat[:50]
        src = src2
    return src


def rewrite_level_exception(src):
    for old, new in LEVEL_EXC:
        assert old in src, "LEVEL_EXC pattern missing: " + old[:60]
        src = src.replace(old, new)
    src = inject_after_type(src,
        "type internal ReversedCompare<'a when 'a : comparison>(value : 'a) =",
        """instance Ordered<ReversedCompare<'a>> when Ordered<'a>
    static compare (a : ReversedCompare<'a>) (b : ReversedCompare<'a>) = compare b.Value a.Value
""")
    return src


def spot_rewrites(src):
    for old, new in SPOT:
        src = src.replace(old, new)
    return src


def excise_types(src):
    """Types that exist to interoperate with a .NET runtime service — an
    AdaptiveSynchronizationContext IS a System.Threading
    SynchronizationContext — have nothing to attach to here. Dropped whole,
    with their doc comments; nothing else in the library refers to them
    (Install() is a static on the type itself)."""
    lines = src.split("\n")
    out, i = [], 0
    while i < len(lines):
        l = lines[i]
        m = re.match(r"^(\s*)type\s+(?:internal\s+|private\s+)*([A-Za-z_][A-Za-z0-9_]*)", l)
        if m and m.group(2) in EXCISED:
            ind = len(m.group(1))
            while out and out[-1].lstrip().startswith("///"):
                out.pop()
            i += 1
            while i < len(lines):
                nxt = lines[i]
                if nxt.strip() and (len(nxt) - len(nxt.lstrip())) <= ind:
                    break
                i += 1
            continue
        out.append(l)
        i += 1
    return chr(10).join(out)


def call_thunked_statics(src):
    """Inside a class whose `static let empty` became a THUNK (a generic
    class's static initializer cannot run at program start — see
    DIVERGENCES.md), every remaining bare read becomes a call. Scoped to the
    class extent; dotted names (MapExt.empty) and members (.IsEmpty) are
    other things and excluded by the boundaries."""
    lines = src.split("\n")
    out = []
    in_extent = False
    ind = 0
    for l in lines:
        if "static let empty () =" in l or "static let defaultComparer () =" in l:
            in_extent = True
            ind = len(l) - len(l.lstrip()) - 4
            out.append(l)
            continue
        if in_extent and l.strip() and not l.lstrip().startswith("//"):
            cur = len(l) - len(l.lstrip())
            if cur <= ind and (l.lstrip().startswith("type ") or l.lstrip().startswith("and ") or l.lstrip().startswith("module ")):
                in_extent = False
        if in_extent:
            l = re.sub(r"(?<![.\w'])empty(?![\w(\)])", "empty ()", l)
            l = re.sub(r"(?<![.\w'])defaultComparer(?![\w(\)])", "defaultComparer ()", l)
            l = l.replace("empty () ()", "empty ()")
            l = l.replace("defaultComparer () ()", "defaultComparer ()")
        out.append(l)
    return chr(10).join(out)


THUNKED_MODULE_VALUES = ["HashSet", "HashMap", "MapExt", "IndexList",
                         "HashMapDelta", "IndexListDelta", "MultiSetMap",
                         "HashSetDelta", "ASet", "AMap", "AList"]


def thunk_module_generic_values(src):
    """A module-level GENERIC value (`let empty<'T> = ...`) compiles to ONE
    shared global whose initializer runs at program start AT THE UNIFORM
    REPRESENTATION -- where a `'Key : comparison` body has no instance to
    call and traps. Thunk them (`let empty<'T> () = ...`) so every read is a
    call the monomorphizer stamps at its own instantiation. See
    DIVERGENCES.md."""
    lines = src.split(chr(10))
    out = []
    in_module = None   # name of a THUNKED module whose extent we are in
    for l in lines:
        m = re.match(r"module (?:internal )?(\w+) =\s*$", l)
        if m:
            in_module = m.group(1) if m.group(1) in THUNKED_MODULE_VALUES else None
        elif l and not l[0].isspace() and not l.startswith("//"):
            in_module = None
        thunked = False
        if in_module:
            m = re.match(r"(    let (?:inline )?empty<[^=>]*>)( : [^=]*)?( =\s*)$|(    let (?:inline )?empty<[^=>]*>)( : [^=]*)?( = .*)$", l)
            if m:
                g = m.groups()
                head, ann, eq = (g[0], g[1], g[2]) if g[0] else (g[3], g[4], g[5])
                l = head + " ()" + (ann or "") + eq
                thunked = True
        if in_module and not thunked:
            # bare reads inside the module extent become calls
            l2 = re.sub(r"(?<![.\w'])empty(?![\w(<])(?! ?\(\))", "(empty ())", l)
            if l2 != l and "let empty" not in l:
                l = l2
        out.append(l)
    # qualified reads, everywhere: Module.empty / Module.empty<args>
    src = chr(10).join(out)
    src = re.sub(r"\b(" + "|".join(THUNKED_MODULE_VALUES) + r")\.empty(<[^<>=]*>)?(?! ?\(\))",
                 lambda m: "(" + m.group(1) + ".empty" + (m.group(2) or "") + " ())", src)
    src = src.replace("empty () ()", "empty ()")
    src = src.replace("(empty ()) ()", "(empty ())")
    return src


def main():
    root, out = sys.argv[1], sys.argv[2]
    proj = os.path.join(root, "FSharp.Data.Adaptive.fsproj")
    files = re.findall(r'Include="([^"]*\.fs)"', open(proj, encoding="utf-8-sig").read())
    files = [f.replace("\\", "/") for f in files if not f.startswith("AssemblyInfo")]
    # AdaptiveFileSystem.fs is SKIPPED, and it is the only file that is.
    # It is a leaf — nothing else in the library refers to anything it
    # defines — and it is not adaptive machinery at all: it is a tool that
    # watches a directory. What it needs is a FileSystemWatcher, a
    # BlockingCollection and a Thread, none of which exist here and none of
    # which say anything about whether this compiler can build the library.
    # See DIVERGENCES.md.
    files = [f for f in files if not f.endswith("AdaptiveFileSystem.fs")]
    # ComputationExpressions.fs is the aset{}/alist{} builder SUGAR — heavy
    # inline overload families, nothing the core machinery calls. Parked
    # until the test suite demands it; see DIVERGENCES.md.
    files = [f for f in files if not f.endswith("ComputationExpressions.fs")]
    chunks = ["module Adaptive"]
    shims = os.path.join(os.path.dirname(os.path.abspath(__file__)), "adaptive-shims")
    for i, f in enumerate(files):
        base = os.path.basename(f)
        chunks.append("\n// ==== " + f + " " + "=" * max(0, 60 - len(f)))
        if base in REPLACED:
            chunks.append(open(os.path.join(shims, REPLACED[base])).read())
        else:
            chunks.append(port(os.path.join(root, f), i == 0))
    text = thunk_module_generic_values(call_thunked_statics(rewrite_lazy_keyword(rewrite_bare_list(rewrite_static_val_mutable(rewrite_regex_spots(rewrite_level_exception(spot_rewrites(excise_types(rewrite_keyvalue_binders(qualify_colliding_types("\n".join(chunks))))))))))))
    open(out, "w").write(text + "\n")
    print(str(len(files)) + " files ported to " + out)


if __name__ == "__main__":
    main()
