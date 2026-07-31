# Known issues, with the smallest program that shows each

Each file here FAILS something today. They are not run by the suite; they are
the reproduction, kept so the next attempt starts from a fact rather than a
memory.

## a.fs.txt, b.fs.txt, c.fs.txt, d.fs.txt — a tuple pattern takes its type from the wrong option

Inference reports a mismatch that is not there:

    let outer (e : int) : ((string * string * string) list * string) option =
        let rec root (x : int) : ((string * int) * string) option = None
        match root e with
        | Some (k, path) -> None
        | None -> None

    type mismatch: string * int vs list<string * string * string>

Those two types are the FIRST components of the scrutinee's payload and of the
result's payload, so the tuple pattern is being typed against the function's
result instead of against what is being matched.

What is ruled out, each by its own file:
  * the arm does not need to build anything    — a.fs.txt has `None` in the arm
  * `root` does not need to be nested          — c.fs.txt lifts it to the top level
  * the shape does not need to be deep         — d.fs.txt is `(int * string)` vs
                                                 `(string * string)`

It needs the union case to be UNRESOLVED, which is why it shows up in the
dogfooding gate (`inference self-application`, which infers each compiler
source with an empty prelude) and not in a real build: the same code compiles
and runs correctly, and the self-host fixpoint over it is byte-identical.

So this is a false positive in inference, not a miscompilation. It was found
by writing `((string * string * string) list * string) option` in
`Backend/BinDriver.fs`; that code was rewritten with flatter types to keep the
gate green, which is a workaround and not a fix.

(The `.txt` suffix keeps them out of the dogfooding gate, which globs `*.fs`
across the whole repo — these files would otherwise fail it by design.)
