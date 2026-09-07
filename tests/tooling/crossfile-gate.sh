#!/usr/bin/env bash
# WHAT ONE FILE CAN SEE OF ANOTHER.
#
# Every case here works when the two files are CONCATENATED and failed when
# they were compiled as separate files of one project — which is why the
# ports (fpp.adaptive, fpp.rendering, fpp.dom) all ended up concatenating
# their sources, an undocumented workaround for a compiler bug rather than a
# choice. A conformance suite cannot hold these: it is one file by
# construction, and one file is exactly the case that always worked.
#
#   * a GENERIC CLASS constructed through a type ABBREVIATION declared with
#     it (`type cval<'T> = ChangeableValue<'T>`). A primary constructor is
#     keyed by the type name's own offset and only an explicit `new` reached
#     the project member table, so the construction lowered as a read of the
#     alias NAME: the consumer file's whole init was dropped in silence, and
#     later — once that became loud — "the body is not available for
#     stamping" (~/claude/fpp-base-snags.md #42).
#   * `[<AutoOpen>]` on a type, whose statics must come into scope with the
#     module that declares it (#49).
#   * a cross-file ACTIVE PATTERN returning a tuple (#32) and a cross-file
#     `[<CustomOperation>]` builder (#37) — both fixed earlier, both regression
#     -prone: they ride project-wide SEEDS that a per-file parse cannot have.
set -e
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
fpp="$root/src/Fpp.Cli/bin/Release/net10.0/fpp"
wt="$root/.wasmtime/bin/wasmtime"; [ -x "$wt" ] || wt="$HOME/.wasmtime/bin/wasmtime"
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT

cat > "$out/lib.fpp" <<'FPP'
module XLib
type ChangeableValue<'T>(value : 'T) =
    let mutable v = value
    member x.Value with get () = v and set (nv : 'T) = v <- nv
// the abbreviation in the SAME `and` group as the class, which is how
// fpp.adaptive writes it — and the shape whose `and` the set accessor ate
and cval<'T> = ChangeableValue<'T>

[<AutoOpen; Sealed>]
type Dom =
    static member Cls (s : string) : string = "class=" + s

type Ex = | EInt of int | EPair of int * Ex
let (|PairP|_|) (e : Ex) =
    match e with
    | EPair (n, b) -> Some (n, b)
    | _ -> None

type SB() =
    member x.Yield (u : unit) = ("", "")
    [<CustomOperation "texture">]
    member x.Texture ((s, f), t : string) = (t, f)
    [<CustomOperation "filter">]
    member x.Filter ((t, s), f : string) = (t, f)
    member x.Run (p : string * string) = p
let sam = SB()
FPP

cat > "$out/use.fpp" <<'FPP'
module XUse
open XLib
// the class through its abbreviation, at a SCALAR instantiation (the one
// that demands a stamp)
let c = cval 7
let cs = cval "s"
let t1 = printfn "%d %s" c.Value cs.Value
// a static of an auto-opened type, unqualified
let t2 = printfn "%s" (Cls "x")
// a tuple-returning active pattern
let t3 =
    match EPair (5, EInt 1) with
    | PairP (n, _) -> printfn "pair %d" n
    | _ -> printfn "MISS"
// a custom-operation builder
let r = sam { texture "Diffuse"
              filter "Linear" }
let t4 = printfn "ce %s %s" (fst r) (snd r)
FPP

"$fpp" build --strict -o "$out/x.wasm" "$out/lib.fpp" "$out/use.fpp"
"$wt" run -W gc=y,exceptions=y "$out/x.wasm" > "$out/got.txt" 2>&1

cat > "$out/want.txt" <<'EXP'
7 s
class=x
pair 5
ce Diffuse Linear
EXP
if diff -u "$out/want.txt" "$out/got.txt"; then
    echo "CROSSFILE OK (alias ctor, autoopen type, active pattern, custom op)"
else
    echo "CROSSFILE MISMATCH"; exit 1
fi
