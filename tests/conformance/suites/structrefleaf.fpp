// A [<Struct>] RECORD HOLDING A REFERENCE, nested inside another record.
//
// An inline struct's leaves are laid out in the enclosing record's own bytes,
// and a leaf need not be a scalar: `{ Name : string; Key : int }` contributes
// a POINTER at its offset. Every path that moved those leaves asked for the
// leaf's scalar storage type and UNWRAPPED the answer, so a struct holding a
// string, an option or any other reference crashed the compiler outright —
// "optGet: None" naming a load in the backend, nothing naming the type.
//
// It cost two port shapes their struct spelling (fpp.rendering's SamplerState
// and RenderPass became plain records) and is #40 and #41 in
// ~/claude/fpp-base-snags.md. A reference leaf is one uniform word now, which
// the pod builder roots across its allocation — so the cases below also read
// the reference back AFTER allocation has run over the shape.
module Core_structrefleaf

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" name got want

// a string leaf, read through a static member (the shape whose literal is
// lifted to a binding, so the leaves are copied rather than spelled out)
[<Struct>]
type RP = { Name : string; Key : int }
type RO = { Id : int; Pass : RP; Active : bool }
let topLevel () : RO = { Id = 1; Pass = ({ Name = "main"; Key = 7 } : RP); Active = true }
type RO with
    static member Create () : RO = { Id = 2; Pass = ({ Name = "second"; Key = 8 } : RP); Active = false }

let a = topLevel ()
eq "string-leaf-from-a-function" (string a.Id + " " + a.Pass.Name + " " + string a.Pass.Key + " " + string a.Active) "1 main 7 True"
let b = RO.Create ()
eq "string-leaf-from-a-static-member" (string b.Id + " " + b.Pass.Name + " " + string b.Pass.Key + " " + string b.Active) "2 second 8 False"

// the whole struct field read out as a VALUE, then read through
let p = a.Pass
eq "the-struct-field-as-a-value" (p.Name + " " + string p.Key) "main 7"

// an OPTION leaf, struct inside struct
type FM = | Point = 0 | Linear = 1
[<Struct>]
type TF = { Mini : FM; Mip : FM option }
[<Struct>]
type SS = { Filter : TF; MaxAniso : int }
let d = ({ Filter = ({ Mini = FM.Linear; Mip = Some FM.Linear } : TF); MaxAniso = 16 } : SS)
eq "option-leaf-of-a-nested-struct"
   (string (int d.Filter.Mini) + " " + (match d.Filter.Mip with Some m -> string (int m) | None -> "none") + " " + string d.MaxAniso)
   "1 1 16"
let dn = ({ Filter = ({ Mini = FM.Point; Mip = None } : TF); MaxAniso = 1 } : SS)
eq "none-leaf-of-a-nested-struct"
   (string (int dn.Filter.Mini) + " " + (match dn.Filter.Mip with Some m -> string (int m) | None -> "none") + " " + string dn.MaxAniso)
   "0 none 1"

// copy-update over a record whose struct field holds a reference
let c = { a with Id = 9 }
eq "copy-update-keeps-the-reference-leaf" (string c.Id + " " + c.Pass.Name + " " + string c.Pass.Key) "9 main 7"
let c2 = { a with Pass = ({ Name = "third"; Key = 3 } : RP) }
eq "copy-update-assigns-a-reference-leaf" (string c2.Id + " " + c2.Pass.Name + " " + string c2.Pass.Key) "1 third 3"

// the reference leaves must survive collection: build many, keep the first
let many : RO[] = Array.init 2000 (fun i -> { Id = i; Pass = ({ Name = "n" + string (i % 10); Key = i } : RP); Active = true })
eq "reference-leaves-survive-allocation" (many.[0].Pass.Name + " " + many.[1999].Pass.Name + " " + string many.[1999].Pass.Key) "n0 n9 1999"
eq "and-the-first-record-is-intact" (a.Pass.Name + " " + string a.Pass.Key) "main 7"

printfn "DONE tests=%d failures=%d" ntests failures
