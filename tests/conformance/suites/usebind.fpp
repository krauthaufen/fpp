// USE BINDINGS AND IDisposable, ported from dotnet/fsharp's
// tests/fsharp/core/control (the `use`/`using` cases) and the UseBindings
// cases of Conformance/Expressions/BindingExpressions.
//
// `use x = e` is `let` plus a disposal that runs when the SCOPE ends —
// however it ends. So the whole content of this suite is WHEN Dispose runs
// and in WHAT ORDER: at the end of a function, at the end of a loop body,
// before the return value is observed, on the way out of an exception, and
// innermost-first when several are live. A trace string records the order,
// because the order is the behaviour.
//
// DROPPED: `use!` (a computation-expression binding, and the custom-builder
// gate owns those), IAsyncDisposable, and disposal on a finalizer thread —
// there is no finalization here, only scope exit.
module Core_usebind

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "NO: %s got %s want %s" name got want

let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

// the trace every case reads back
let mutable trace = ""
let note (s : string) : unit = trace <- trace + s
let reset () : unit = trace <- ""

// a resource that implements IDisposable the ORDINARY way — through an
// interface implementation, which is the spelling F# programs actually use
type Res(name : string) =
    member _.Name = name
    interface System.IDisposable with
        member _.Dispose () = note ("-" + name)

let res (name : string) : Res =
    note ("+" + name)
    // `new` rather than a bare call: F# warns (FS0760) when a type
    // implementing IDisposable is constructed without it
    new Res(name)

// ---- disposal happens at the end of the SCOPE -------------------------------

let single () : unit =
    use a = res "a"
    note "!"

reset ()
single ()
eq "disposed-at-end-of-function" trace "+a!-a"

// the body runs BEFORE the disposal, not after
let ordered () : unit =
    use a = res "a"
    note "1"
    note "2"

reset ()
ordered ()
eq "body-runs-before-disposal" trace "+a12-a"

// ---- several in one scope dispose INNERMOST FIRST ---------------------------

let nested () : unit =
    use a = res "a"
    use b = res "b"
    use c = res "c"
    note "!"

reset ()
nested ()
eq "innermost-disposes-first" trace "+a+b+c!-c-b-a"

// a nested SCOPE disposes at its own end, not the outer one's
let innerScope () : unit =
    use a = res "a"
    (let inner () : unit =
        use b = res "b"
        note "in"
     inner ())
    note "out"

reset ()
innerScope ()
eq "inner-scope-disposes-first" trace "+a+bin-bout-a"

// ---- the RESULT is computed before disposal, and observed after -------------

let withResult () : int =
    use a = res "a"
    note "compute"
    7

reset ()
let r1 = withResult ()
note ("=" + string r1)
eq "result-computed-then-disposed" trace "+acompute-a=7"

// the result may even read the resource, since disposal is after the body
let readsResource () : string =
    use a = res "a"
    a.Name + "!"

reset ()
let r2 = readsResource ()
eq "result-may-read-the-resource" r2 "a!"
eq "and-still-disposes" trace "+a-a"

// ---- disposal on the way out of an EXCEPTION --------------------------------

exception Boom of string

let throws () : unit =
    use a = res "a"
    note "before"
    raise (Boom "x")

reset ()
(try throws () with
 | Boom m -> note ("caught" + m))
eq "disposed-when-an-exception-leaves" trace "+abefore-acaughtx"

// the INNER one still goes first when an exception unwinds several
let throwsNested () : unit =
    use a = res "a"
    use b = res "b"
    raise (Boom "y")

reset ()
(try throwsNested () with
 | Boom _ -> note "caught")
eq "unwind-disposes-innermost-first" trace "+a+b-b-acaught"

// a `use` inside a `try` disposes before the handler runs
let insideTry () : unit =
    try
        use a = res "a"
        raise (Boom "z")
    with
    | Boom _ -> note "handler"

reset ()
insideTry ()
eq "disposed-before-the-handler" trace "+a-ahandler"

// and it disposes on the ordinary path out of a try too
let tryNoThrow () : unit =
    try
        use a = res "a"
        note "ok"
    with
    | Boom _ -> note "handler"

reset ()
tryNoThrow ()
eq "disposed-leaving-try-normally" trace "+aok-a"

// a `finally` and a `use` in the same scope both run
let withFinally () : unit =
    use a = res "a"
    try
        note "body"
    finally
        note "fin"

reset ()
withFinally ()
eq "finally-then-dispose" trace "+abodyfin-a"

// ---- inside LOOPS: once per iteration ---------------------------------------

let inLoop () : unit =
    for i in 1 .. 3 do
        use a = res (string i)
        note "."

reset ()
inLoop ()
eq "loop-body-disposes-each-iteration" trace "+1.-1+2.-2+3.-3"

let inWhile () : unit =
    let mutable i = 0
    while i < 2 do
        use a = res (string i)
        note "."
        i <- i + 1

reset ()
inWhile ()
eq "while-body-disposes-each-iteration" trace "+0.-0+1.-1"

// ---- a resource disposed through an explicit upcast -------------------------

let upcast1 () : unit =
    use a = (res "a") :> System.IDisposable
    note "!"

reset ()
upcast1 ()
eq "upcast-to-the-interface" trace "+a!-a"

// and Dispose called BY HAND through the interface is just a call
let byHand () : unit =
    let a = res "a"
    note "!"
    (a :> System.IDisposable).Dispose ()

reset ()
byHand ()
eq "manual-dispose-through-the-interface" trace "+a!-a"

// disposing twice really does call it twice — nothing here is idempotent
// unless the resource makes it so
let twice () : unit =
    let a = res "a"
    (a :> System.IDisposable).Dispose ()
    (a :> System.IDisposable).Dispose ()

reset ()
twice ()
eq "dispose-is-not-idempotent-by-itself" trace "+a-a-a"

// ---- a resource that COUNTS its disposals -----------------------------------

type Counted() =
    let mutable n = 0
    member _.Count = n
    interface System.IDisposable with
        member _.Dispose () = n <- n + 1

let counted = new Counted()

let useCounted () : unit =
    use c = counted
    ()

eq "not-yet-disposed" (string counted.Count) "0"
useCounted ()
eq "disposed-once" (string counted.Count) "1"
useCounted ()
eq "disposed-again" (string counted.Count) "2"

// DROPPED: `use` on a type with a plain `member Dispose` and no IDisposable.
// F++ accepts it and calls the member; F# requires the interface and rejects
// the binding, so the oracle cannot compile the case.

// ---- the value is still an ordinary binding ---------------------------------

let readsFields () : string =
    use a = res "keep"
    a.Name

reset ()
eq "use-binds-a-normal-value" (readsFields ()) "keep"
eq "and-disposed-it" trace "+keep-keep"

// several resources, of which one is returned-from before the others bind
let earlyReturn (stop : bool) : string =
    use a = res "a"
    if stop then "early"
    else
        use b = res "b"
        "late"

reset ()
eq "early-path-value" (earlyReturn true) "early"
eq "early-path-trace" trace "+a-a"

reset ()
eq "late-path-value" (earlyReturn false) "late"
eq "late-path-trace" trace "+a+b-b-a"

printfn "DONE tests=%d failures=%d" ntests failures
