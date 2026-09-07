#!/usr/bin/env bash
# IMPLICIT AND EXPLICIT YIELDS MIX, and what a bare `()` means.
#
# F# refuses the mix — a body that names a value anywhere reads its other
# bare expressions as statements and DISCARDS them (warning FS0020). Two
# things bought that rule: backwards compatibility, and one real ambiguity —
# a bare `()` could be Zero or a Yield of the unit value. Neither buys enough
# to be worth the silent drop here: it folded fpp.dom's scene CE to an empty
# Shader (~/claude/fpp-base-snags.md #51), after the same shape had cost the
# wombat.dom port once, and this compiler has no warnings to soften it with.
#
# So the mix is allowed and means what it looks like, and the ambiguity is
# decided by the BUILDER: a bare `()` yields where some `Yield` overload
# accepts unit, and stays the statement it always was where none does.
#
# A gate rather than a conformance suite: the fsi oracle answers F#'s reading
# by construction, so there is nothing to diff against.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
wt="$root/.wasmtime/bin/wasmtime"; [ -x "$wt" ] || wt="$HOME/.wasmtime/bin/wasmtime"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT

cat > "$out/p.fpp" <<'FPP'
module YieldMix
type Node = { Tag : string; Kids : Node list }
let rec render (n : Node) : string =
    n.Tag + "[" + String.concat "," (List.map render n.Kids) + "]"

// a builder with NO unit-taking Yield: a bare `()` is Zero, statements stay
// statements
type ElemBuilder(tag : string) =
    member _.Yield (s : string) : Node list = [ { Tag = s; Kids = [] } ]
    member _.Yield (n : Node) : Node list = [ n ]
    member _.Combine (a : Node list, b : Node list) : Node list = a @ b
    member _.Delay (f : unit -> Node list) : Node list = f ()
    member _.Zero () : Node list = []
    member _.Run (kids : Node list) : Node = { Tag = tag; Kids = kids }
let div = ElemBuilder "div"

// the mix: a bare value beside an explicit yield keeps BOTH, in order
let a = div { "bare"
              yield "explicit" }
let r1 = printfn "%s" (render a)

// the reverse order, and two bare values around one explicit yield
let b = div { yield "first"
              "second"
              "third" }
let r2 = printfn "%s" (render b)

// a genuine STATEMENT beside an explicit yield still runs and yields nothing
let c = div { printfn "ran"
              yield "only" }
let r3 = printfn "%s" (render c)

// a bare `()` with no unit-taking Yield: Zero
let d = div { () }
let r4 = printfn "%d" (List.length d.Kids)

// a builder that DOES take unit: the same `()` yields
type UB() =
    member _.Yield (u : unit) : int list = [ 0 ]
    member _.Yield (n : int) : int list = [ n ]
    member _.Combine (x : int list, y : int list) : int list = x @ y
    member _.Delay (f : unit -> int list) : int list = f ()
    member _.Zero () : int list = []
let ub = UB()
let e = ub { () }
let f = ub { 1
             ()
             yield 2 }
let r5 = printfn "%d %d" (List.length e) (List.length f)
FPP

"$fpp" build --strict -o "$out/x.wasm" "$out/p.fpp"
"$wt" run -W gc=y,exceptions=y "$out/x.wasm" > "$out/got.txt" 2>&1

cat > "$out/want.txt" <<'EXP'
div[bare[],explicit[]]
div[first[],second[],third[]]
ran
div[only[]]
0
1 3
EXP
if diff -u "$out/want.txt" "$out/got.txt"; then
    echo "CE-YIELDMIX OK (mix keeps both; bare () yields only where Yield takes unit)"
else
    echo "CE-YIELDMIX MISMATCH"; exit 1
fi
