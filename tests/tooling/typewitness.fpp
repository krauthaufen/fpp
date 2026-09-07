// A TYPE PARAMETER'S WITNESS CARRIES WHAT THE TYPE IS, not only how it is
// represented. `typeName<'a>` and `sizeof<'a>` are the observable part, so
// this file is what says the plumbing reaches each place a witness can come
// from — a caller's argument, a class' own slots read off `self`, and the
// SLOT WITNESS ABI, where a vtable member generic beyond its class had no
// channel for its own arguments at all.
//
// A gate rather than a conformance suite: F# spells these `typeof<'a>.Name`
// and answers "Int32"/"String", so `dotnet fsi` is no oracle here.

let mutable tests = 0
let mutable failures = 0
let check (what : string) (got : string) (want : string) : unit =
    tests <- tests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" what got want

// 1. concrete
check "concrete int" typeName<int> "int"
check "concrete string" typeName<string> "string"
check "concrete bool" typeName<bool> "bool"
check "concrete float" typeName<float> "float"
check "sizeof int" (string sizeof<int>) "4"
check "sizeof float" (string sizeof<float>) "8"
check "sizeof int64" (string sizeof<int64>) "8"

// 2. a plain generic function: the witness is the caller's argument
let nameOf (x : 'a) : string = typeName<'a>
let sizeOf (x : 'a) : int = sizeof<'a>
check "generic int" (nameOf 1) "int"
check "generic string" (nameOf "s") "string"
check "generic float" (nameOf 1.0) "float"
check "generic bool" (nameOf true) "bool"
check "generic size int" (string (sizeOf 1)) "4"
check "generic size float" (string (sizeOf 1.0)) "8"

// 3. a generic CLASS' own parameter, recovered off self
type Box<'a>(v : 'a) =
    member x.Value = v
    member x.Name = typeName<'a>
    member x.Size = sizeof<'a>
check "class int" (Box<int> 3).Name "int"
check "class string" (Box<string> "s").Name "string"
check "class float" (Box<float> 1.0).Name "float"
check "class size float" (string (Box<float> 1.0).Size) "8"

// 4. the same through a VTABLE row
type INamed<'a> =
    abstract Named : unit -> string

type NBox<'a>(v : 'a) =
    interface INamed<'a> with
        member x.Named () = typeName<'a>
check "iface int" ((NBox<int> 3 :> INamed<int>).Named ()) "int"
check "iface string" ((NBox<string> "s" :> INamed<string>).Named ()) "string"

// 5. THE SLOT WITNESS ABI: a member generic BEYOND its class. The row's
// signature is fixed and `self` carries only 'a, so 'b rides the hidden
// witness parameters the slot declares.
type IMapper<'a> =
    abstract MapName : ('a -> 'b) -> string

type MBox<'a>(v : 'a) =
    interface IMapper<'a> with
        member x.MapName (f : 'a -> 'b) : string = typeName<'a> + "->" + typeName<'b>
let ms = MBox<string> "s" :> IMapper<string>
check "slot string->int" (ms.MapName (fun s -> s.Length)) "string->int"
check "slot string->float" (ms.MapName (fun s -> float s.Length)) "string->float"
check "slot string->string" (ms.MapName (fun s -> s)) "string->string"

printfn "DONE tests=%d failures=%d" tests failures
