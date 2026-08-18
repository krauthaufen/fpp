// Casts, type tests and boxing over USER types — the portable themes of
// dotnet/fsharp tests/fsharp/core/subtype/test.fsx (that suite itself is
// BCL-heavy: ICollection/System.Array/measures). Dropped: boxed-SCALAR
// type tests (`match box 1 with :? int`) — F++ scalars share one boxed
// representation, so the exact scalar type is not testable at runtime
// (recorded as a known issue in the status doc).
module Core_casts

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

type IAnimal =
    abstract member Noise : unit -> string
type Dog() =
    interface IAnimal with
        member x.Noise () = "woof"
type Cat() =
    interface IAnimal with
        member x.Noise () = "meow"

// upcast, dispatch through the interface
let a : IAnimal = Dog() :> IAnimal
test "up1" (a.Noise () = "woof")

// downcast back to the concrete class
let back = a :?> Dog
test "down1" (not (isNull (box back)))

// heterogeneous list through the interface
let animals : IAnimal list = [ Dog() :> IAnimal; Cat() :> IAnimal ]
test "list1" ((animals |> List.map (fun x -> x.Noise ())) = [ "woof"; "meow" ])

// :? patterns pick the concrete class
let kind (x : IAnimal) =
    match x with
    | :? Dog -> "dog"
    | :? Cat -> "cat"
    | _ -> "?"
test "pat1" (kind (Dog() :> IAnimal) = "dog")
test "pat2" (kind (Cat() :> IAnimal) = "cat")

// :? with a binder
let noiseOf (x : IAnimal) =
    match x with
    | :? Dog as d -> (d :> IAnimal).Noise ()
    | _ -> "?"
test "pat3" (noiseOf (Dog() :> IAnimal) = "woof")

// box / unbox round-trips
let o : obj = box 42
test "box1" (unbox<int> o = 42)
let os : obj = box "hi"
test "box2" (unbox<string> os = "hi")

// abstract base class: override dispatches through the base type
[<AbstractClass>]
type Shape() =
    abstract member Area : unit -> int
    member x.Doubled () = 2 * x.Area ()
type Sq(n : int) =
    inherit Shape()
    override x.Area () = n * n
type Rect(w : int, h : int) =
    inherit Shape()
    override x.Area () = w * h
let s : Shape = Sq(3) :> Shape
test "abs1" (s.Area () = 9)
test "abs2" (s.Doubled () = 18)
let shapes : Shape list = [ Sq(2) :> Shape; Rect(3, 4) :> Shape ]
test "abs3" ((shapes |> List.map (fun x -> x.Area ())) = [ 4; 12 ])

// object expression over the abstract base
let anon =
    { new Shape() with
        member x.Area () = 7 }
test "obj1" (anon.Area () = 7)
test "obj2" (anon.Doubled () = 14)

// object expression over an interface
let parrot =
    { new IAnimal with
        member x.Noise () = "polly" }
test "obj3" (parrot.Noise () = "polly")
test "obj4" (kind parrot = "?")

// class test also answers for subclasses
let isShape (x : obj) =
    match x with
    | :? Shape -> true
    | _ -> false
test "sub1" (isShape (box (Sq(1))))
test "sub2" (isShape (box (Rect(1, 1))))
test "sub3" (not (isShape (box (Dog()))))

printfn "DONE tests=%d failures=%d" ntests failures
