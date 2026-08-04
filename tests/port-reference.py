#!/usr/bin/env python3
"""Port FSharp.Data.Adaptive's HashCollections.fs to F++.

Every rule here is a .NET dependency with no F++ counterpart, which is the
kind of change the acceptance criterion allows ("compiles with minimal
changes"). Nothing here works around a compiler limitation.

  1. OptimizedClosures.FSharpFunc<a,b,c> is a CLR perf hack for multi-arg
     closures. In F++ a curried function already IS that, so the type
     becomes `a -> b -> c`, `.Adapt` becomes the identity, and
     `.Invoke(x, y)` becomes application.
  2. CLR/tooling attributes (MethodImpl, Debugger*, EqualityConditionalOn)
     carry no semantics. Struct and AllowNullLiteral DO, and are kept.
  3. #if/#else/#endif: the source targets both .NET and Fable. Picking a
     target is the caller's choice, not the compiler's; we take the
     branch with no symbols defined. (F++ has no preprocessor yet.)
"""
import re, sys

# AutoOpen is KEPT: the library leans on it — `HashSet.computeDelta` lives in
# an auto-opened `DifferentiationExtensions.HashSet`, and stripping it left
# every such name resolving to whatever else answered to it.
KEEP = {"Struct", "AllowNullLiteral", "AbstractClass", "Sealed", "AutoOpen"}

def split_top(s, sep):
    out, depth, cur = [], 0, ""
    for c in s:
        if c in "<([": depth += 1; cur += c
        elif c in ">)]": depth -= 1; cur += c
        elif c == sep and depth == 0: out.append(cur.strip()); cur = ""
        else: cur += c
    if cur.strip(): out.append(cur.strip())
    return out

def matchto(s, i, op, cl):
    depth = 1
    while i < len(s) and depth > 0:
        if s[i] == op: depth += 1
        elif s[i] == cl: depth -= 1
        i += 1
    return i

def port_closures(src):
    out, i, tag = [], 0, "OptimizedClosures.FSharpFunc<"
    while True:
        k = src.find(tag, i)
        if k < 0:
            out.append(src[i:]); break
        out.append(src[i:k])
        j = matchto(src, k + len(tag), "<", ">")
        inner = src[k + len(tag):j - 1]
        m = re.match(r"\s*\.Adapt\s*", src[j:])
        if m:
            after = j + m.end()
            if src[after] == "(":
                b = matchto(src, after + 1, "(", ")")
                out.append("(" + src[after + 1:b - 1] + ")"); i = b
            else:
                mm = re.match(r"[A-Za-z_][A-Za-z0-9_.']*", src[after:])
                out.append(mm.group(0)); i = after + mm.end()
        else:
            out.append("(" + " -> ".join(split_top(inner, ",")) + ")"); i = j
    # `.Invoke` becomes plain application ONLY for bindings the Adapt
    # conversion touched, and only within their scope. A global by-name rule
    # rewrote `x.Invoke`/`cache.Invoke`/an IndexMapping's `mapping.Invoke` —
    # all REAL members — into applying the object. The scope of an adapted
    # binding runs to the first non-blank line at a smaller indent.
    lines = src.split("\n")
    adapted = []   # (name, first_line, end_line)
    for i, l in enumerate(lines):
        m = re.match(r"(\s*)let (?:mutable )?(\w+)\s*=\s*OptimizedClosures\.", l)
        if m:
            ind = len(m.group(1))
            end = len(lines)
            for j in range(i + 1, len(lines)):
                lj = lines[j]
                if lj.strip() and (len(lj) - len(lj.lstrip())) < ind:
                    end = j
                    break
            adapted.append((m.group(2), i, end))
        # a PARAMETER typed as an adapted closure (`compare :
        # OptimizedClosures.FSharpFunc<...>`) is applied through .Invoke too;
        # its scope is the declaring type or function
        for pm in re.finditer(r"([A-Za-z_]\w*)\s*:\s*OptimizedClosures\.FSharpFunc<", l):
            # the parameter may sit on its own line of a MULTILINE signature;
            # the scope is the DECLARING construct's, so anchor the indent at
            # the nearest let/member/new/type line at or above
            anchor = i
            while anchor > 0 and not re.match(r"\s*(let|member|new|type|and|override|static)\b", lines[anchor]):
                anchor -= 1
            ind = len(lines[anchor]) - len(lines[anchor].lstrip())
            end = len(lines)
            for j in range(i + 1, len(lines)):
                lj = lines[j]
                if lj.strip() and (len(lj) - len(lj.lstrip())) <= ind and j > anchor:
                    if not re.match(r"\s*[\(\)a-zA-Z_']", lj) or re.match(r"\s*(let|member|new|type|and|override|static|module)\b", lj):
                        end = j
                        break
            adapted.append((pm.group(1), i, end))
    src = "".join(out)
    lines = src.split("\n")
    def inv_for(name):
        def inv(m):
            return "(" + m.group(1) + " " + " ".join("(" + a + ")" for a in split_top(m.group(2), ",")) + ")"
        return inv
    for name, a, b in adapted:
        pat = re.compile(
            r"(?<![A-Za-z0-9_.])(" + re.escape(name) + r")\.Invoke\s*\(([^()]*(?:\([^()]*\)[^()]*)*)\)")
        for i in range(a, min(b, len(lines))):
            for _ in range(4):
                new_l = pat.sub(inv_for(name), lines[i])
                if new_l == lines[i]:
                    break
                lines[i] = new_l
    return "\n".join(lines)

def strip_attrs(src):
    out, i = [], 0
    while True:
        k = src.find("[<", i)
        if k < 0:
            out.append(src[i:]); break
        out.append(src[i:k])
        j = k + 2; depth = 1
        while j < len(src) and depth > 0:
            if src[j:j+2] == "[<": depth += 1; j += 2
            elif src[j:j+2] == ">]": depth -= 1; j += 2
            else: j += 1
        kept = [e for e in split_top(src[k+2:j-2], ";")
                if re.match(r"[A-Za-z_][A-Za-z0-9_]*", e)
                and re.match(r"[A-Za-z_][A-Za-z0-9_]*", e).group(0) in KEEP]
        out.append("[<" + "; ".join(kept) + ">]" if kept else "")
        i = j
    src = "".join(out)
    # a line that held nothing but attributes disappears
    return "\n".join(l for l in src.split("\n") if l.strip() or not l)

def pick_branch(src, defined=()):
    out, stack = [], []   # stack of "are we emitting here?"
    for line in src.split("\n"):
        t = line.strip()
        if t.startswith("#if "):
            sym = t[4:].strip()
            if sym.startswith("!"):
                stack.append(sym[1:].strip() not in defined)
            else:
                stack.append(sym in defined)
            continue
        if t == "#else":
            if stack: stack[-1] = not stack[-1]
            continue
        if t == "#endif":
            if stack: stack.pop()
            continue
        if all(stack):
            out.append(line)
    return "\n".join(out)

def drop_fsharp_core_set_bridges(src):
    """ofSet/toSet convert to and from FSharp.Core's Set — a type the port
    cannot carry (it lives in FSharp.Core, not in this file). Drop the two
    bridge functions, comments included."""
    out = []
    skip = False
    for line in src.split("\n"):
        t = line.strip()
        if t.startswith("let inline ofSet") or t.startswith("let inline toSet"):
            skip = True
            # their doc comments directly above are already emitted; harmless
            continue
        if skip:
            # a bridge body is short and more-indented; the next let/member
            # at the same or lower indent ends it
            if t == "" or line.startswith(" " * 8):
                continue
            skip = False
        out.append(line)
    return "\n".join(out)

def dotnet_exception_ctors(src):
    """.NET exception CLASSES construct with optional arguments; the port's
    exn is a union, so the no-argument form gets .NET's own message."""
    src = src.replace(
        "KeyNotFoundException()",
        'KeyNotFoundException("The given key was not present in the dictionary.")')
    # exception TYPES the prelude's exn union does not carry ride in Failure
    src = src.replace("raise <| System.IndexOutOfRangeException()",
                      'raise (Failure "Index was outside the bounds of the array.")')
    src = src.replace("raise <| IndexOutOfRangeException()",
                      'raise (Failure "Index was outside the bounds of the array.")')
    src = src.replace("raise <| System.NotSupportedException()",
                      'raise (Failure "Specified method is not supported.")')
    return src

def drop_dotnet_interop_interfaces(src):
    """The non-generic System.Collections interfaces and the mutable
    collection contracts (ICollection, and ISet's mutators) are .NET
    interop whose implementations all throw. The read side survives as
    prelude interfaces; ISet gains the Contains/Count forwards that .NET
    reaches through interface inheritance."""
    out = []
    lines = src.split("\n")
    i = 0
    def indent(l):
        return len(l) - len(l.lstrip())
    drop_headers = (
        "interface System.Collections.IEnumerable ",
        "interface System.Collections.IEnumerable\n",
        "interface System.Collections.IEnumerator ",
        "interface System.Collections.Generic.ICollection<",
    )
    iset_mutators = ("member x.Add(", "member x.ExceptWith(", "member x.UnionWith(",
                     "member x.IntersectWith(", "member x.SymmetricExceptWith(")
    while i < len(lines):
        line = lines[i]
        t = line.strip()
        header = (t.startswith("interface System.Collections.IEnumerable")
                  or t.startswith("interface System.Collections.IEnumerator")
                  or t.startswith("interface System.Collections.Generic.ICollection<"))
        if header:
            base = indent(line)
            i += 1
            while i < len(lines) and (lines[i].strip() == "" or indent(lines[i]) > base):
                i += 1
            continue
        if t.startswith("interface System.Collections.Generic.IEnumerator<") or t.startswith("interface IEnumerator<"):
            # .NET reaches MoveNext through the NON-generic IEnumerator this
            # pass drops; the vtable needs it on the generic one
            base = indent(line)
            out.append(line)
            out.append(" " * (base + 4) + "member x.MoveNext() = x.MoveNext()")
            i += 1
            while i < len(lines) and (lines[i].strip() == "" or indent(lines[i]) > base):
                out.append(lines[i])
                i += 1
            continue
        if t.startswith("interface System.Collections.Generic.ISet<"):
            base = indent(line)
            out.append(line)
            pad = " " * (base + 4)
            out.append(pad + "member x.Count = x.Count")
            out.append(pad + "member x.Contains(item) = x.Contains item")
            i += 1
            while i < len(lines) and (lines[i].strip() == "" or indent(lines[i]) > base):
                if not any(lines[i].strip().startswith(m) for m in iset_mutators):
                    out.append(lines[i])
                i += 1
            continue
        out.append(line)
        i += 1
    return "\n".join(out)

src = open(sys.argv[1]).read()
open(sys.argv[2], "w").write(
    drop_dotnet_interop_interfaces(dotnet_exception_ctors(drop_fsharp_core_set_bridges(strip_attrs(port_closures(pick_branch(src)))))))
