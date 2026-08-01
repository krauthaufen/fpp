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
    src = strip_namespace_headers(src, first)
    return src


def main():
    root, out = sys.argv[1], sys.argv[2]
    proj = os.path.join(root, "FSharp.Data.Adaptive.fsproj")
    files = re.findall(r'Include="([^"]*\.fs)"', open(proj, encoding="utf-8-sig").read())
    files = [f.replace("\\", "/") for f in files if not f.startswith("AssemblyInfo")]
    chunks = ["module Adaptive"]
    shims = os.path.join(os.path.dirname(os.path.abspath(__file__)), "adaptive-shims")
    for i, f in enumerate(files):
        base = os.path.basename(f)
        chunks.append("\n// ==== " + f + " " + "=" * max(0, 60 - len(f)))
        if base in REPLACED:
            chunks.append(open(os.path.join(shims, REPLACED[base])).read())
        else:
            chunks.append(port(os.path.join(root, f), i == 0))
    open(out, "w").write("\n".join(chunks) + "\n")
    print(str(len(files)) + " files ported to " + out)


if __name__ == "__main__":
    main()
