#!/usr/bin/env python3
"""Second-guess the compiler's instance picks.

`fpp picks <files>` prints one line per instance selection the checker
made over fully concrete arguments: verdict, class, arguments, the chosen
candidate, and every candidate's head. This script re-derives the winner
from scratch — its own term parser, its own matcher, its own
"accepts strictly fewer types" comparison, sharing no code with the
compiler — and flags every line where the two disagree.

What each verdict must mean:
  solved     exactly one candidate is best, and it is the chosen one
  ambiguous  at least two candidates fit and none beats the rest
  none       no candidate fits
  deferred   IMPOSSIBLE for concrete arguments — waiting is only for
             arguments that still contain a variable (a concrete
             `deferred` was exactly the shape of the repeated-variable
             bug, where P2<'a,'a> counted as forever-possible at
             (int, string))
  improve    impossible for concrete arguments, same reasoning

Exit 0 when every line checks out, 1 otherwise.
"""
import sys

# ---- term parser: name | name(a,b) | ?7 ---------------------------------

def parse(s):
    term, rest = _term(s, 0)
    if rest != len(s):
        raise ValueError("trailing input in %r" % s)
    return term

def _term(s, i):
    if s[i] == "?":
        j = i + 1
        while j < len(s) and s[j].isdigit():
            j += 1
        return ("var", s[i + 1 : j]), j
    j = i
    while j < len(s) and s[j] not in "(),":
        j += 1
    name = s[i:j]
    if j < len(s) and s[j] == "(":
        args = []
        j += 1
        while s[j] != ")":
            a, j = _term(s, j)
            args.append(a)
            if s[j] == ",":
                j += 1
        return ("con", name, tuple(args)), j + 1
    return ("con", name, ()), j

# ---- one-way matching: a candidate's variable may bind, consistently ----

def match_one(pat, tgt, sub):
    if pat[0] == "var":
        v = pat[1]
        if v in sub:
            return equal(sub[v], tgt)
        sub[v] = tgt
        return True
    if tgt[0] == "var":
        return False  # a concrete argument never contains one; a head's
                      # variable on the target side only equals itself
    if pat[1] != tgt[1] or len(pat[2]) != len(tgt[2]):
        return False
    return all(match_one(p, t, sub) for p, t in zip(pat[2], tgt[2]))

def equal(a, b):
    return a == b  # tuples of tuples: structural

def matches(head, args):
    sub = {}
    return len(head) == len(args) and all(
        match_one(p, t, sub) for p, t in zip(head, args))

# ---- "accepts strictly fewer types" -------------------------------------
# b_covers_a: everything a's head accepts, b's also accepts — b's
# variables free to bind (consistently), a's variables stand only for
# themselves (tagged so a var never equals a same-numbered b var).

def cover_one(pat, tgt, sub):
    if pat[0] == "var":
        v = pat[1]
        if v in sub:
            return sub[v] == tgt
        sub[v] = tgt
        return True
    if tgt[0] == "var":
        return False
    if pat[1] != tgt[1] or len(pat[2]) != len(tgt[2]):
        return False
    return all(cover_one(p, t, sub) for p, t in zip(pat[2], tgt[2]))

def tag(term, mark):
    if term[0] == "var":
        return ("con", "$rigid" + mark + term[1], ())
    return ("con", term[1], tuple(tag(a, mark) for a in term[2]))

def covers(b, a):
    sub = {}
    ta = [tag(t, "A") for t in a]
    return len(b) == len(a) and all(
        cover_one(p, t, sub) for p, t in zip(b, ta))

def morespec(a, b):
    return covers(b, a) and not covers(a, b)

# ---- the check -----------------------------------------------------------

def main():
    lines = [l.rstrip("\n") for l in sys.stdin if l.strip()]
    bad = 0
    for ln in lines:
        parts = ln.split("|")
        verdict, cls, argss, chosens = parts[0], parts[1], parts[2], parts[3]
        args = [parse(a) for a in argss.split(";")] if argss else []
        cands = [[parse(a) for a in c.split(";")] if c else []
                 for c in parts[4:]]
        fitting = [i for i, h in enumerate(cands) if matches(h, args)]
        best = [i for i in fitting
                if not any(j != i and morespec(cands[j], cands[i])
                           for j in fitting)]
        def flag(msg):
            nonlocal bad
            bad += 1
            print("DISAGREE %s: %s" % (msg, ln))
        if verdict == "solved":
            if chosens == "-" or best != [int(chosens)]:
                flag("best=%r chosen=%s" % (best, chosens))
        elif verdict == "ambiguous":
            if len(best) < 2:
                flag("best=%r, not ambiguous" % best)
        elif verdict == "none":
            if fitting:
                flag("candidates fit: %r" % fitting)
        else:  # deferred / improve over concrete arguments
            flag("verdict %r impossible for concrete arguments" % verdict)
    print("%d picks checked, %d disagreements" % (len(lines), bad))
    return 1 if bad else 0

if __name__ == "__main__":
    sys.exit(main())
