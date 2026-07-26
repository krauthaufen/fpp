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

KEEP = {"Struct", "AllowNullLiteral", "AbstractClass", "Sealed"}

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
    src = "".join(out)
    def inv(m):
        return "(" + m.group(1) + " " + " ".join("(" + a + ")" for a in split_top(m.group(2), ",")) + ")"
    for _ in range(4):
        src = re.sub(r"([A-Za-z_][A-Za-z0-9_.]*)\.Invoke\(([^()]*(?:\([^()]*\)[^()]*)*)\)", inv, src)
    return src

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

def pick_branch(src):
    out, stack = [], []   # stack of "are we emitting here?"
    for line in src.split("\n"):
        t = line.strip()
        if t.startswith("#if "):
            sym = t[4:].strip()
            stack.append(sym.startswith("!"))   # no symbols are defined
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

src = open(sys.argv[1]).read()
open(sys.argv[2], "w").write(strip_attrs(port_closures(pick_branch(src))))
