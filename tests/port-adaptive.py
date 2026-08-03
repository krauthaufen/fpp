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
REPLACED = {"ShallowEquality.fs": "ShallowEquality.fpp"}


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
    return "\n".join(out)


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
            if m and len(m.group(1)) >= ind:
                return None
        return None

    # `and` opens a property accessor too (`and inline set v = ...`); these
    # are never type names, and renaming one rewrites the KEYWORD
    KEYWORDS = {"set", "get", "inline", "new", "val", "member", "this", "static",
                "mutable", "rec", "of", "with", "abstract", "override", "default"}
    seen, renames = {}, []
    for i, l in enumerate(lines):
        d = decl.match(l)
        if not d:
            continue
        name = d.group(2)
        if name in KEYWORDS:
            continue
        if name not in seen:
            seen[name] = i
            continue
        enc = enclosing(i, len(d.group(1)))
        if enc is not None:
            renames.append((name, enc[0] + "_" + name, enc[1], enc[2]))

    for old, new_name, a, b in renames:
        pat = re.compile(r"(?<![A-Za-z0-9_.])" + re.escape(old) + r"\b")
        for i in range(a, min(b, len(lines))):
            lines[i] = pat.sub(new_name, lines[i])
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
            out.append("%s    let %s = %s.Value" % (ind, vp, kv))
    return "\n".join(out)


EXCISED = ["AdaptiveSynchronizationContext"]

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
    return "\n".join(out)


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
    chunks = ["module Adaptive"]
    shims = os.path.join(os.path.dirname(os.path.abspath(__file__)), "adaptive-shims")
    for i, f in enumerate(files):
        base = os.path.basename(f)
        chunks.append("\n// ==== " + f + " " + "=" * max(0, 60 - len(f)))
        if base in REPLACED:
            chunks.append(open(os.path.join(shims, REPLACED[base])).read())
        else:
            chunks.append(port(os.path.join(root, f), i == 0))
    text = excise_types(rewrite_keyvalue_binders(qualify_colliding_types("\n".join(chunks))))
    open(out, "w").write(text + "\n")
    print(str(len(files)) + " files ported to " + out)


if __name__ == "__main__":
    main()
