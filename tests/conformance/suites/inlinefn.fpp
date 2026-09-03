// `let inline` / `member inline`: the body is copied to every call site —
// same answers as the out-of-line form, which is what this suite pins.
// (SRTP is out of scope; inline here is the copy-to-call-site half.)
module InlineFn

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "WRONG %s: %s exp..got %s" name want got

let inline square (x : int) = x * x
let inline compose2 (f : int -> int) (g : int -> int) (x : int) = f (g x)

// large enough that only the inline keyword gets it copied
let inline poly (x : float) : float =
    let a = x * 1.5 + 2.0
    let b = a * 2.5 + 3.0
    let c = b * 3.5 + 4.0
    let d = c * 4.5 + 5.0
    a + b + c + d

type Vec2 = { X : float; Y : float }
type Vec2 with
    member inline v.Dot (o : Vec2) : float = v.X * o.X + v.Y * o.Y
    static member inline Scale (v : Vec2, k : float) : Vec2 = { X = v.X * k; Y = v.Y * k }

eq "square" (string (square 7)) "49"
eq "compose" (string (compose2 square (fun n -> n + 1) 3)) "16"
eq "poly" (sprintf "%.3f" (poly 1.25)) "287.797"
let a = { X = 1.0; Y = 2.0 }
let b = { X = 3.0; Y = 4.0 }
eq "dot" (sprintf "%.1f" (a.Dot b)) "11.0"
eq "scale" (sprintf "%.1f" ((Vec2.Scale (a, 2.5)).Y)) "5.0"

printfn "DONE tests=%d failures=%d" ntests failures
