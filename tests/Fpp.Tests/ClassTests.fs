module Fpp.Tests.ClassTests

open Expecto
open Fpp

// The class layer, end to end. The oracle cannot arbitrate these: `class`
// and `instance` are not F#, so the expected output is written out here.
// What IS oracle-checked is that the primitive instances did not change any
// arithmetic — that is the rest of the suite still passing.

let private wasmtime =
    System.Environment.GetFolderPath System.Environment.SpecialFolder.UserProfile
    + "/.wasmtime/bin/wasmtime"

let private compile (lines : string list) : string * string list =
    let ws = Workspace()
    ws.SetFileText "prog.fpp" (String.concat "\n" ("module M" :: lines) + "\n")
    ws.EmitProgram ()

let private diagnostics (lines : string list) : string list =
    let ws = Workspace()
    ws.SetFileText "prog.fpp" (String.concat "\n" ("module M" :: lines) + "\n")
    ws.Diagnostics "prog.fpp" |> List.map (fun d -> d.Message)

let private run (lines : string list) : string =
    let wat, errors = compile lines
    Expect.isEmpty errors "emission errors"
    let tmp = System.IO.Path.GetTempFileName() + ".wat"
    System.IO.File.WriteAllText(tmp, wat)
    let psi = System.Diagnostics.ProcessStartInfo(wasmtime, "-W exceptions=y " + tmp)
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    use p = System.Diagnostics.Process.Start psi
    let out = p.StandardOutput.ReadToEnd()
    p.StandardError.ReadToEnd() |> ignore
    p.WaitForExit()
    System.IO.File.Delete tmp
    Expect.equal p.ExitCode 0 "wasmtime failed"
    out

let private typeOf (lines : string list) (name : string) : string option =
    let ws = Workspace()
    let src = String.concat "\n" ("module M" :: lines) + "\n"
    ws.SetFileText "prog.fpp" src
    let inf = ws.TypeCheck "prog.fpp"
    let at = src.IndexOf ("let " + name + " ")
    inf.DefTypes
    |> List.tryPick (fun (off, _, ty) -> if off = at + 4 then Some ty else None)

let private v2d =
    [ "[<Struct>]"
      "type V2d = { X : float; Y : float }"
      "instance Add<V2d, V2d>"
      "    type Result = V2d"
      "    static (+) a b = { X = a.X + b.X; Y = a.Y + b.Y }"
      "instance Sub<V2d, V2d>"
      "    type Result = V2d"
      "    static (-) a b = { X = a.X - b.X; Y = a.Y - b.Y }"
      "instance Mul<V2d, V2d>"
      "    type Result = V2d"
      "    static (*) a b = { X = a.X * b.X; Y = a.Y * b.Y }"
      "instance Num<V2d>"
      "    static Zero = { X = 0.0; Y = 0.0 }"
      "    static One = { X = 1.0; Y = 1.0 }" ]

[<Tests>]
let primitiveInstanceTests =
    testList "classes: primitive instances" [
        test "every primitive numeric type has the operator zoo" {
            let out =
                run [ "let a = print (7 + 3)"
                      "let b = print (7 - 3)"
                      "let c = print (7 * 3)"
                      "let d = print (7 / 3)"
                      "let e = print (7 % 3)"
                      "let f = print (7.5 + 2.5)"
                      "let g = print (7.5 / 2.5)"
                      "let h = print (7L * 3L)"
                      "let i = print (7u + 3u)"
                      "let j = print (7.5f - 2.5f)"
                      "let k = print (\"ab\" + \"cd\")" ]
            Expect.equal out "10\n4\n21\n2\n1\n10\n3\n21\n10\n5\nabcd\n" "the whole zoo"
        }
        test "Zero and One exist at every numeric type" {
            let out =
                run [ "let a = print (Zero + One)"
                      "let b : float = Zero"
                      "let c = print (b + One)"
                      "let d : int64 = One"
                      "let e = print (d + One)" ]
            // an unconstrained Zero/One defaults to int, as F# does
            Expect.equal out "1\n1\n2\n" "Zero and One resolve by the type they are used at"
        }
        test "an operator with no instance names the missing one" {
            let msgs = diagnostics [ "let a = 1 + \"x\"" ]
            Expect.contains msgs "no instance Add<int, string>" "the operator, its operands, the missing instance"
        }
        test "float remainder works, though wasm has no instruction for it" {
            // the instance supplies a BODY (a - b * truncate (a / b)) where
            // the backend has nothing to emit
            Expect.equal (run [ "let a = print (7.5 % 2.0)"; "let b = print (-7.5 % 2.0)" ])
                "1.5\n-1.5\n" "same sign as the dividend, as in F#"
        }
        test "an operator with no instance at all is still an error" {
            let msgs = diagnostics [ "let a = 1 % \"x\"" ]
            Expect.contains msgs "no instance Rem<int, string>" "named, with both operands"
        }
    ]

[<Tests>]
let genericMathTests =
    testList "classes: generic math" [
        test "an unannotated operator generalizes over its operands" {
            Expect.equal (typeOf [ "let add a b = a + b" ] "add") (Some "'a -> 'b -> 'c")
                "the result is the instance's, not the left operand's"
        }
        test "a known result narrows the operands" {
            // only Add<int,int> has Result = int, so the choice is forced
            Expect.equal (typeOf [ "let add a b = a + b + 1" ] "add") (Some "int -> int -> int")
                "improvement runs backwards from the result too"
        }
        test "a generic operator is stamped per instantiation" {
            // before the class layer this emitted i32.add for every type and
            // trapped on the float call
            let out =
                run [ "let add a b = a + b"
                      "let a = print (add 1 2)"
                      "let b = print (add 1.5 2.5)"
                      "let c = print (add \"x\" \"y\")" ]
            Expect.equal out "3\n4\nxy\n" "one body, three specializations"
        }
        test "comparison and unary minus are class members too" {
            // both used to run the INTEGER instruction at every type once the
            // body was generic, and trap on a float
            let out =
                run [ "let mx a b = if a > b then a else b"
                      "let neg (x : 'a) : 'a when Num<'a> = -x"
                      "let a = print (mx 3 4)"
                      "let b = print (mx 2.5 1.5)"
                      "let c = print (mx \"a\" \"b\")"
                      "let d = print (neg 3)"
                      "let e = print (neg 2.5)" ]
            Expect.equal out "4\n2.5\nb\n-3\n-2.5\n" "Ordered and Neg stamp like the rest"
        }
        test "a generic operator inside a match guard is stamped" {
            // the guard is as much part of the body as the result is; it was
            // not being walked when deciding what to specialize
            let out =
                run [ "let classify t ="
                      "    match t with"
                      "    | a, b when a > b -> \"first\""
                      "    | a, b when a < b -> \"second\""
                      "    | _ -> \"same\""
                      "let a = print (classify (2, 1))"
                      "let b = print (classify (1.5, 2.5))" ]
            Expect.equal out "first\nsecond\n" "guards specialize with their clause"
        }
        test "a closed class carries the genericity" {
            let out =
                run [ "let sum3 (a : 'a) (b : 'a) (c : 'a) : 'a when Num<'a> = a + b + c"
                      "let a = print (sum3 1 2 3)"
                      "let b = print (sum3 1.5 2.5 3.5)" ]
            Expect.equal out "6\n7.5\n" "Num<'a> discharges the operator constraints"
        }
    ]

/// Run and parse one float per line, then compare to what F# computes.
/// The transcendentals are OUR implementation, not a binding to libm, so
/// they are checked to a tolerance rather than byte-exactly.
let private floats (lines : string list) : float list =
    run lines |> fun out ->
        out.Split '\n'
        |> Array.filter (fun l -> l.Trim() <> "")
        |> Array.map (fun l ->
            // the printer emits .NET's own glyphs for the special values
            match l.Trim() with
            | "\u221e" -> System.Double.PositiveInfinity
            | "-\u221e" -> System.Double.NegativeInfinity
            | "NaN" -> nan
            | t -> System.Double.Parse (t, System.Globalization.CultureInfo.InvariantCulture))
        |> Array.toList

let private closeTo (name : string) (got : float) (want : float) =
    // print gives 15 decimal places, so tiny values are limited by the
    // FORMAT rather than the computation; compare relative where possible
    let rel = if want = 0.0 then abs got else abs ((got - want) / want)
    Expect.isLessThan rel 1e-11 (name + ": got " + string got + ", want " + string want)

[<Tests>]
let mathSurfaceTests =
    testList "classes: the math surface" [
        test "sqrt, abs, truncate and min/max are machine instructions" {
            let out =
                run [ "let a = print (sqrt 16.0)"
                      "let b = print (truncate 3.7)"
                      "let c = print (truncate (0.0 - 3.7))"
                      "let d = print (abs (0 - 7))"
                      "let e = print (abs (0.0 - 2.5))"
                      "let f = print (min 3 4)"
                      "let g = print (max 2.5 1.5)"
                      "let h = print (min \"b\" \"a\")" ]
            Expect.equal out "4\n3\n-3\n7\n2.5\n3\n2.5\na\n" "the exact ones"
        }
        test "exp, log and the trigonometric functions match F#" {
            let got =
                floats [ "let a = print (exp 1.0)"
                         "let b = print (exp 10.0)"
                         "let c = print (log 100.0)"
                         "let d = print (log 0.5)"
                         "let e = print (sin 0.5)"
                         "let f = print (cos 0.5)"
                         "let g = print (tan 0.5)"
                         "let h = print (sin 10.0)"
                         "let i = print (cos 10.0)" ]
            let want =
                [ exp 1.0; exp 10.0; log 100.0; log 0.5
                  sin 0.5; cos 0.5; tan 0.5; sin 10.0; cos 10.0 ]
            List.iteri (fun i (g, w) -> closeTo ("term " + string i) g w) (List.zip got want)
        }
        test "hyperbolic and inverse trigonometric functions match F#" {
            let got =
                floats [ "let a = print (sinh 0.5)"
                         "let b = print (cosh 0.5)"
                         "let c = print (tanh 0.5)"
                         "let d = print (sinh 3.0)"
                         "let e = print (cosh 3.0)"
                         "let f = print (tanh 3.0)"
                         "let g = print (asin 0.5)"
                         "let h = print (acos 0.5)"
                         "let i = print (atan 0.5)"
                         "let j = print (atan 2.0)"
                         "let k = print (atan2 1.0 2.0)"
                         "let l = print (atan2 (0.0 - 1.0) (0.0 - 2.0))" ]
            let want =
                [ sinh 0.5; cosh 0.5; tanh 0.5; sinh 3.0; cosh 3.0; tanh 3.0
                  asin 0.5; acos 0.5; atan 0.5; atan 2.0
                  atan2 1.0 2.0; atan2 -1.0 -2.0 ]
            List.iteri (fun i (g, w) -> closeTo ("term " + string i) g w) (List.zip got want)
        }
        test "an integer exponent is exact, not exp (b log a)" {
            let out =
                run [ "let a = print (2.0 ** 10.0)"
                      "let b = print ((0.0 - 2.0) ** 3.0)"
                      "let c = print (2.0 ** (0.0 - 2.0))" ]
            Expect.equal out "1024\n-8\n0.25\n" "repeated squaring, so the answer is exact"
        }
        test "a fractional exponent goes through exp and log" {
            let got = floats [ "let a = print (2.0 ** 0.5)"; "let b = print (10.0 ** 1.5)" ]
            List.iteri (fun i (g, w) -> closeTo ("term " + string i) g w)
                (List.zip got [ 2.0 ** 0.5; 10.0 ** 1.5 ])
        }
        test "float32 has the surface too" {
            let out = run [ "let a = print (sqrt 16.0f)"; "let b = print (abs (0.0f - 2.5f))" ]
            Expect.equal out "4\n2.5\n" "same classes, narrower instances"
        }
        test "the surface is generic over the float width" {
            // one body, both widths — what the class layer is for
            let out =
                run [ "let hyp (a : 'a) (b : 'a) : 'a when Floating<'a> = sqrt (a * a + b * b)"
                      "let a = print (hyp 3.0 4.0)"
                      "let b = print (hyp 3.0f 4.0f)" ]
            Expect.equal out "5\n5\n" "stamped per width"
        }
    ]

[<Tests>]
let float16Tests =
    testList "float16" [
        test "halves round exactly as System.Half does" {
            // normals, subnormals, exact ties, and the 65520 overflow edge
            let vals =
                [ "0.0"; "1.0"; "1.5"; "2.25"; "3.75"; "-1.0"; "-0.5"
                  "65504.0"; "65519.0"
                  "6.103515625e-05"; "6.0e-05"; "5.96046448e-08"
                  // just above the tie between zero and the smallest
                  // subnormal — it disagrees if the conversion rounds twice
                  "2.98023224e-08"; "2.9802322387695312e-08"
                  "1.5e-08"; "1.0009765625"; "1.00048828125"
                  "0.1"; "0.2"; "0.3"; "12345.0"; "-12345.0" ]
            let got =
                floats (vals |> List.mapi (fun i v -> "let v" + string i + " = print (float32 (float16 (" + v + ")))"))
            let want =
                vals |> List.map (fun v ->
                    let d = System.Double.Parse (v, System.Globalization.CultureInfo.InvariantCulture)
                    float (float32 (System.Half.op_Explicit d : System.Half)))
            // `print` emits 15 decimal places, so a subnormal half is
            // limited by the FORMAT, not by the conversion. Adjacent halves
            // are 6e-8 apart at their closest, so this still pins the
            // rounding to the correct neighbour.
            List.iteri
                (fun i (g, w : float) ->
                    Expect.isLessThan (abs (g - w)) (1e-15 + 1e-9 * abs w)
                        ("value " + string i + ": got " + string g + ", want " + string w))
                (List.zip got want)
        }
        test "overflow saturates to infinity, and printing it does not trap" {
            // 65520 is exactly halfway between the largest half and 65536,
            // so ties-to-even rounds it UP and out of range
            Expect.equal (run [ "let a = print (float32 (float16 65520.0))"
                                "let b = print (float32 (float16 70000.0))"
                                "let c = print (float32 (float16 (0.0 - 70000.0)))" ])
                "\u221e\n\u221e\n-\u221e\n" "saturates, and prints as .NET does"
        }
        test "arithmetic is the correctly-rounded half, not an approximation" {
            // f32 carries 24 significand bits and a half needs 11; double
            // rounding is innocuous at 2p+2, so computing in f32 and rounding
            // ONCE gives exactly what native f16 hardware would
            let pairs = [ 1.0, 3.0; 1.5, 2.25; 0.1, 0.2; 1000.0, 0.001; 65504.0, 65504.0; -3.5, 1.25 ]
            let ops = [ "+"; "-"; "*"; "/" ]
            let lit (v : float) =
                let s = v.ToString ("R", System.Globalization.CultureInfo.InvariantCulture)
                if s.Contains "." || s.Contains "E" then s else s + ".0"
            let lines =
                [ for i, (a, b) in List.indexed pairs do
                    for j, op in List.indexed ops do
                      yield "let v" + string i + "_" + string j
                            + " = print (float32 (" + lit a + "h " + op + " " + lit b + "h))" ]
            let got = floats lines
            let half (v : float) : System.Half = System.Half.op_Explicit v
            let want =
                [ for a, b in pairs do
                    for op in ops do
                      let x, y = half a, half b
                      let r = match op with
                              | "+" -> x + y
                              | "-" -> x - y
                              | "*" -> x * y
                              | _ -> x / y
                      yield float (float32 r) ]
            Expect.equal got want "every operation matches System.Half"
        }
        test "a half is an i31 at runtime, so it costs no allocation" {
            let wat, errors = compile [ "let a = print (float32 (1.5h + 2.25h))" ]
            Expect.isEmpty errors "compiles"
            // the literal is folded to its bit pattern at compile time
            Expect.stringContains wat "(ref.i31 (i32.const 15872))" "1.5h is its 16 bits, unboxed"
        }
        test "halves get the whole class surface" {
            let out =
                run [ "let a = print (float32 (sqrt 16.0h))"
                      "let b = print (float32 (abs (0.0h - 3.5h)))"
                      "let c = print (float32 (min 1.5h 2.5h))"
                      "let d = print (float32 (max 1.5h 2.5h))"
                      "let e = print (if 1.5h < 2.5h then 1 else 0)"
                      "let f = print (compare 2.5h 1.5h)"
                      "let g = print (float32 (Zero + One : float16))" ]
            Expect.equal out "4\n3.5\n1.5\n2.5\n1\n1\n1\n" "same classes, an f32-backed instance"
        }
        test "generic code runs at the half width too" {
            let out =
                run [ "let hyp (a : 'a) (b : 'a) : 'a when Floating<'a> = sqrt (a * a + b * b)"
                      "let a = print (hyp 3.0 4.0)"
                      "let b = print (hyp 3.0f 4.0f)"
                      "let c = print (float32 (hyp 3.0h 4.0h))" ]
            Expect.equal out "5\n5\n5\n" "one body, three widths"
        }
        test "a half array is PACKED: i16 elements, 2 bytes each" {
            let wat, errors =
                compile [ "let xs = [| 1.5h; 2.25h; 3.0h |]"
                          "let a = print (float32 xs.[1])"
                          "let b ="
                          "    xs.[2] <- 0.5h"
                          "    print (float32 xs.[2])"
                          "let c = print xs.Length" ]
            Expect.isEmpty errors "compiles"
            // the size win is the point — assert the representation itself
            Expect.stringContains wat "$parr_h (array (mut i16))" "packed element type"
            Expect.stringContains wat "array.new_fixed $parr_h" "the literal builds it"
        }
        test "packed half arrays read, write and fold correctly" {
            let out =
                run [ "let xs = [| 1.5h; 2.25h; 3.0h |]"
                      "let a = print (float32 xs.[1])"
                      "let b ="
                      "    xs.[2] <- 0.5h"
                      "    print (float32 xs.[2])"
                      "let big = Array.create 1000 1.0h"
                      "let sum (a : 'a[]) (z : 'a) : 'a when Num<'a> ="
                      "    let mutable acc = z"
                      "    let mutable i = 0"
                      "    while i < a.Length do"
                      "        acc <- acc + a.[i]"
                      "        i <- i + 1"
                      "    acc"
                      "let c = print (float32 (sum big Zero))"
                      "let d = print (float32 (sum xs Zero))" ]
            // 1000 ones: integers are exact in f16 up to 2048
            Expect.equal out "2.25\n0.5\n1000\n4.25\n" "packed storage behaves like storage"
        }
        test "an E-exponent literal survives emission" {
            // the emitter dropped `E` and `+` from float literals, turning
            // 1.0E5 into 1.05
            Expect.equal (run [ "let a = print 1.0E5"; "let b = print 2.0e+3" ]) "100000\n2000\n" "exponent kept"
        }
    ]

[<Tests>]
let qualificationTests =
    testList "classes: qualified members" [
        test "a member can always be named through its class" {
            let out =
                run [ "let a = print (Num.Zero + Num.One)"
                      "let b = print (Add.(+) 3 4)"
                      "let c = print (Mul.(*) 2.5 4.0)" ]
            // the qualification says which CLASS; the instance is still
            // whatever the operand types select
            Expect.equal out "1\n7\n10\n" "class-qualified names resolve like bare ones"
        }
        test "qualification survives at a user instance" {
            let out =
                run (v2d @
                     [ "let z : V2d = Num.One"
                       "let a = print (Add.(+) z z).X" ])
            Expect.equal out "2\n" "the operator member is the instance's body"
        }
        test "a qualified member still picks the instance by type" {
            let out = run (v2d @ [ "let z : V2d = Num.Zero"; "let a = print z.Y" ])
            Expect.equal out "0\n" "Num.Zero at V2d is the user instance's Zero"
        }
    ]

[<Tests>]
let userInstanceTests =
    testList "classes: user instances" [
        test "a type gains the operators by declaring instances" {
            let out =
                run (v2d @
                     [ "let p = { X = 1.0; Y = 2.0 } + { X = 3.0; Y = 4.0 }"
                       "let a = print p.X"
                       "let b = print p.Y" ])
            Expect.equal out "4\n6\n" "the instance body is what runs"
        }
        test "an operator may leave its operand type" {
            // the shape Num cannot express: scalar * vector = vector
            let out =
                run (v2d @
                     [ "instance Mul<float, V2d>"
                       "    type Result = V2d"
                       "    static (*) s v = { X = s * v.X; Y = s * v.Y }"
                       "let q = 2.0 * { X = 1.0; Y = 2.5 }"
                       "let a = print q.X"
                       "let b = print q.Y" ])
            Expect.equal out "2\n5\n" "Mul<float, V2d> resolves heterogeneously"
        }
        test "generic code runs at a user type" {
            let out =
                run (v2d @
                     [ "let sum3 (a : 'a) (b : 'a) (c : 'a) : 'a when Num<'a> = a + b + c"
                       "let x = sum3 { X = 1.0; Y = 2.0 } { X = 3.0; Y = 4.0 } { X = 5.0; Y = 6.0 }"
                       "let a = print x.X"
                       "let b = print x.Y"
                       "let c = print (sum3 1 2 3)" ])
            Expect.equal out "9\n12\n6\n" "one generic body, a user instance and a builtin one"
        }
        test "Zero comes from the user instance" {
            let out = run (v2d @ [ "let z : V2d = Zero"; "let a = print z.X"; "let b = print (z + One).X" ])
            Expect.equal out "0\n1\n" "a class member is a name for what the instance provides"
        }
        test "min and max are componentwise on a vector, with no total order" {
            // the point of keeping MinMax off Ordered: a vector has a
            // componentwise minimum but no `compare`, and asking for one
            // would have been a lie
            let out =
                run (v2d @
                     [ "instance MinMax<V2d>"
                       "    static min a b = { X = min a.X b.X; Y = min a.Y b.Y }"
                       "    static max a b = { X = max a.X b.X; Y = max a.Y b.Y }"
                       "let p = { X = 1.0; Y = 5.0 }"
                       "let q = { X = 4.0; Y = 2.0 }"
                       "let a = print (min p q).X"
                       "let b = print (min p q).Y"
                       "let c = print (max p q).X"
                       "let d = print (max p q).Y" ])
            Expect.equal out "1\n2\n4\n5\n" "each component taken separately"
        }
        test "generic code over MinMax alone runs at both a scalar and a vector" {
            let out =
                run (v2d @
                     [ "instance MinMax<V2d>"
                       "    static min a b = { X = min a.X b.X; Y = min a.Y b.Y }"
                       "    static max a b = { X = max a.X b.X; Y = max a.Y b.Y }"
                       "let clamp (lo : 'a) (hi : 'a) (v : 'a) : 'a when MinMax<'a> = max lo (min hi v)"
                       "let a = print (clamp 0 10 42)"
                       "let b = print (clamp { X = 1.0; Y = 5.0 } { X = 4.0; Y = 2.0 } { X = 9.0; Y = 9.0 }).X" ])
            Expect.equal out "10\n4\n" "one body, a scalar instance and a vector one"
        }
        test "an instance must implement its class" {
            let msgs =
                diagnostics
                    [ "[<Struct>]"
                      "type P = { A : int }"
                      "instance Add<P, P>"
                      "    type Result = P" ]
            Expect.contains msgs "instance Add must implement (+)" "an empty instance is not a primitive one"
        }
    ]

[<Tests>]
let overloadTests =
    testList "member overloading" [
        test "overloads select by arity" {
            let out =
                run [ "type Calc(bias : int) ="
                      "    member x.Add(a : int) = a + bias"
                      "    member x.Add(a : int, b : int) = a + b + bias"
                      "let c = Calc(100)"
                      "let p = print (c.Add 5)"
                      "let q = print (c.Add(5, 6))" ]
            Expect.equal out "105\n111\n" "one and two arguments reach different bodies"
        }
        test "overloads select by argument type" {
            let out =
                run [ "type Printer() ="
                      "    member x.Show(v : int) = print v"
                      "    member x.Show(v : string) = print v"
                      "let p = Printer()"
                      "let a = p.Show 42"
                      "let b = p.Show \"hi\"" ]
            Expect.equal out "42\nhi\n" "the argument's type picks the body"
        }
        test "overloads distinguish tuple flavours — the acceptance-file case" {
            let out =
                run [ "type Sink() ="
                      "    member x.CopyTo(dst : (int * int)[], i : int) = print 1"
                      "    member x.CopyTo(dst : struct(int * int)[], i : int) = print 2"
                      "let s = Sink()"
                      "let refArr : (int * int)[] = [| (1, 2) |]"
                      "let a = s.CopyTo(refArr, 0)"
                      "let structArr = Array.zeroCreate<struct(int * int)> 1"
                      "let b = s.CopyTo(structArr, 0)" ]
            Expect.equal out "1\n2\n" "a ref tuple array and a struct tuple array are different overloads"
        }
        test "an exact overload beats one that fits by widening" {
            // Equals(obj) fits EVERY call once obj widens; without ranking it
            // always won and Equals(Box) was unreachable
            let out =
                run [ "type Box(v : int) ="
                      "    member x.V = v"
                      "    member x.Same(o : obj) = print 0"
                      "    member x.Same(o : Box) = print o.V"
                      "let b = Box(7)"
                      "let a = b.Same (Box 42)" ]
            Expect.equal out "42\n" "the specific overload wins"
        }
        test "STATIC overloads select too" {
            let out =
                run [ "type Make() ="
                      "    static member Of(v : int) = v + 1"
                      "    static member Of(v : string, k : int) = k"
                      "let a = print (Make.Of 41)"
                      "let b = print (Make.Of(\"x\", 9))" ]
            Expect.equal out "42\n9\n" "statics park and select like instance members"
        }
        test ".Length works where the element type is not statically known" {
            // the generic length helper was CALLED but never DEFINED, so any
            // module reaching it failed validation
            let out =
                run [ "let xs : (int * int)[] = [| (1, 2); (3, 4) |]"
                      "let a = print xs.Length" ]
            Expect.equal out "2\n" "ref-element arrays answer Length"
        }
    ]

[<Tests>]
let enumeratorTests =
    testList "the enumerator protocol" [
        test "for-in is structural: any GetEnumerator/MoveNext/Current shape" {
            let out =
                run [ "type Counter(n : int) ="
                      "    let mutable i = 0"
                      "    member x.MoveNext() ="
                      "        i <- i + 1"
                      "        i <= n"
                      "    member x.Current = i * 10"
                      "type Counting(n : int) ="
                      "    member x.GetEnumerator() = Counter(n)"
                      "let go ="
                      "    for v in Counting(3) do"
                      "        print v" ]
            Expect.equal out "10\n20\n30\n" "no interface required, as in F#"
        }
        test "a seq parameter enumerates through the vtable" {
            let out =
                run [ "type RngEn(n : int) ="
                      "    let mutable i = 0"
                      "    interface IEnumerator<int> with"
                      "        member e.MoveNext() ="
                      "            i <- i + 1"
                      "            i <= n"
                      "        member e.Current = i * 7"
                      "type Rng(n : int) ="
                      "    interface IEnumerable<int> with"
                      "        member x.GetEnumerator() = RngEn(n) :> IEnumerator<int>"
                      "let total (xs : seq<int>) ="
                      "    let mutable s = 0"
                      "    for v in xs do"
                      "        s <- s + v"
                      "    s"
                      "let a = print (total (Rng 3 :> IEnumerable<int>))" ]
            Expect.equal out "42\n" "the concrete type is unknown at the loop"
        }
        test "for-in walks lists, destructuring included" {
            let out =
                run [ "let xs = [ 3; 4; 5 ]"
                      "let go ="
                      "    for x in xs do print x"
                      "let pairs = [ (1, 10); (2, 20) ]"
                      "let go2 ="
                      "    for (a, b) in pairs do print (a * b)" ]
            Expect.equal out "3\n4\n5\n10\n40\n" "a cons walk, and the binder may destructure"
        }
        test "for-in destructures tuple-element arrays" {
            let out =
                run [ "let xs : (int * int)[] = [| (2, 30); (4, 50) |]"
                      "let go ="
                      "    for (a, b) in xs do print (a + b)" ]
            Expect.equal out "32\n54\n" "a uniform-reference element array indexes plainly"
        }
        test "new-expressions have the type they construct" {
            // `new X<T>(args)` typed as a fresh variable, which left every
            // new-built enumerator opaque to the protocol
            let out =
                run [ "type Box<'a>(v : 'a) ="
                      "    member x.V = v"
                      "let b = new Box<int>(41)"
                      "let a = print (b.V + 1)" ]
            Expect.equal out "42\n" "new X(...) IS X(...)"
        }
        test "a member declared LATER in the class binds from an earlier body" {
            let out =
                run [ "type T() ="
                      "    member x.UseIt() = x.Later() + 1"
                      "    member x.Later() = 41"
                      "let t = T()"
                      "let a = print (t.UseIt())" ]
            Expect.equal out "42\n" "resolution waits for the fields table to be complete"
        }
    ]

[<Tests>]
let stdlibCoreTests =
    testList "stdlib as core" [
        test "lazy Seq combinators over a user enumerable" {
            let out =
                run [ "type RngEn(n : int) ="
                      "    let mutable i = 0"
                      "    interface IEnumerator<int> with"
                      "        member e.MoveNext() ="
                      "            i <- i + 1"
                      "            i <= n"
                      "        member e.Current = i"
                      "type Rng(n : int) ="
                      "    interface IEnumerable<int> with"
                      "        member x.GetEnumerator() = RngEn(n) :> IEnumerator<int>"
                      "let src = Rng 6 :> seq<int>"
                      "let a = printfn \"%d\" (Seq.length src)"
                      "let b = printfn \"%d\" (src |> Seq.map (fun v -> v * 10) |> Seq.fold (fun s v -> s + v) 0)"
                      "let c = printfn \"%d\" (src |> Seq.filter (fun v -> v % 2 = 0) |> Seq.length)"
                      "let d = printfn \"%d\" (src |> Seq.truncate 3 |> Seq.length)"
                      "let e = printfn \"%b\" (src |> Seq.exists (fun v -> v = 5))"
                      "let f = printfn \"%b\" (src |> Seq.forall (fun v -> v < 5))" ]
            Expect.equal out "6\n210\n3\n3\ntrue\nfalse\n" "the pipeline is lazy and correct"
        }
        test "a partially applied format flows through a lazy map" {
            // the acceptance file does exactly this to render its elements
            let out =
                run [ "let s = [ 1; 2; 3 ] |> Seq.map (sprintf \"%A\") |> String.concat \"; \""
                      "let a = printfn \"[%s]\" s" ]
            Expect.equal out "[1; 2; 3]\n" "sprintf with missing arguments is a function"
        }
        test "the String module" {
            let out =
                run [ "let a = printfn \"%s\" (String.concat \"-\" [ \"x\"; \"y\"; \"z\" ])"
                      "let b = printfn \"%s\" (String.replicate 3 \"ab\")"
                      "let c = printfn \"%s\" (String.map (fun ch -> if ch = 'a' then 'A' else ch) \"banana\")"
                      "let d = printfn \"%d\" (String.length \"hello\")"
                      "let e = printfn \"%b\" (String.exists (fun ch -> ch = 'n') \"banana\")"
                      "let f = printfn \"%b\" (String.forall (fun ch -> ch = 'n') \"banana\")" ]
            Expect.equal out "x-y-z\nababab\nbAnAnA\n5\ntrue\nfalse\n" "the module surface"
        }
        test "KeyValuePair is a struct with Key and Value" {
            Expect.equal (run [ "let kv = KeyValuePair(1, \"one\")"
                                "let a = printfn \"%d=%s\" kv.Key kv.Value" ])
                "1=one\n" "constructs and reads"
        }
        test "Object.ReferenceEquals is the identity primitive" {
            let out =
                run [ "type Box(v : int) ="
                      "    member x.V = v"
                      "let b1 = Box(1)"
                      "let b2 = Box(1)"
                      "let a = printfn \"%b\" (System.Object.ReferenceEquals(b1, b1))"
                      "let b = printfn \"%b\" (System.Object.ReferenceEquals(b1, b2))" ]
            Expect.equal out "true\nfalse\n" "identity, not structure"
        }
        test "raising the collections exception carries its message" {
            let out =
                run [ "let f () ="
                      "    try"
                      "        raise (KeyNotFoundException \"missing!\")"
                      "    with"
                      "    | KeyNotFoundException m -> printfn \"caught %s\" m"
                      "let a = f ()" ]
            Expect.equal out "caught missing!\n" "throw and catch"
        }
    ]

[<Tests>]
let userClassTests =
    testList "user-defined typeclasses" [
        test "a declared class folds three types from one body" {
            // the playground's Monoid, end to end: mempty is a value-like
            // member (unit-lifted, applied at the name), combine a function,
            // and the generic body stamps per instance
            let out =
                run [ "class Monoid<'a>"
                      "    static mempty : 'a"
                      "    static combine : 'a -> 'a -> 'a"
                      "instance Monoid<int>"
                      "    static mempty = 0"
                      "    static combine a b = a + b"
                      "instance Monoid<string>"
                      "    static mempty = \"\""
                      "    static combine a b = a + b"
                      "let mconcat (xs : 'a list) : 'a when Monoid<'a> ="
                      "    let mutable acc = mempty"
                      "    for x in xs do"
                      "        acc <- combine acc x"
                      "    acc"
                      "let a = print (mconcat [ 1; 2; 3 ])"
                      "let b = print (mconcat [ \"x\"; \"y\" ])" ]
            Expect.equal out "6\nxy\n" "one fold, two instances"
        }
        test "an associated type decides the result at the instance" {
            let out =
                run [ "class Norm<'v>"
                      "    type Scalar"
                      "    static norm : 'v -> Scalar"
                      "instance Norm<float>"
                      "    type Scalar = float"
                      "    static norm v = abs v"
                      "instance Norm<int>"
                      "    type Scalar = int"
                      "    static norm v = abs v"
                      "let a = print (norm (0.0 - 2.5))"
                      "let b = print (norm (0 - 7))" ]
            Expect.equal out "2.5\n7\n" "Scalar comes from the instance"
        }
        test "a mutable binding does not generalize" {
            // the value restriction: quantifying a cell hands every read a
            // fresh variable the writes can no longer reach — `let mutable
            // acc = mempty` silently went int-only this way
            let ws = Fpp.Workspace()
            ws.SetFileText "t.fpp" (String.concat "\n" [
                "module M"
                "class Monoid<'a>"
                "    static mempty : 'a"
                "    static combine : 'a -> 'a -> 'a"
                "instance Monoid<int>"
                "    static mempty = 0"
                "    static combine a b = a + b"
                "let mconcat (xs : 'a list) : 'a when Monoid<'a> ="
                "    let mutable acc = mempty"
                "    for x in xs do"
                "        acc <- combine acc x"
                "    acc"
                "" ])
            let inf = ws.TypeCheck "t.fpp"
            let src = System.String.Join ("\n", [| "module M" |])
            ignore src
            let hover = ws.HoverAt "t.fpp" ((ws.FileText "t.fpp").IndexOf "mconcat" + 1)
            match hover with
            | Some h -> Expect.stringContains h "Monoid<'a>" "stays generic under its class"
            | None -> failtest "no hover"
            ignore inf
        }
    ]

[<Tests>]
let typeTestTests =
    testList "type tests against builtins and interfaces" [
        test "builtin collections answer :? by representation" {
            let out =
                run [ "let show (o : obj) ="
                      "    if o :? list<int> then \"list\""
                      "    elif o :? array<int> then \"array\""
                      "    elif o :? string then \"string\""
                      "    else \"other\""
                      "let a = print (show ([ 1; 2 ] :> obj))"
                      "let b = print (show ([| 1 |] :> obj))"
                      "let c = print (show (\"s\" :> obj))"
                      "let d = print (show (42 :> obj))"
                      "let e = print (show (([] : int list) :> obj))" ]
            // nil is a null reference, so the empty list still answers list
            Expect.equal out "list\narray\nstring\nother\nlist\n" "representation tests"
        }
        test "a class test on a non-object answers false, not a trap" {
            let out =
                run [ "type Box(v : int) ="
                      "    member x.V = v"
                      "let test (o : obj) = if o :? Box then 1 else 0"
                      "let a = print (test (Box 1 :> obj))"
                      "let b = print (test (5 :> obj))"
                      "let c = print (test (\"s\" :> obj))" ]
            Expect.equal out "1\n0\n0\n" "a question, not a crash"
        }
        test "an interface test checks the implementors" {
            let out =
                run [ "type IShape ="
                      "    abstract member Area : float"
                      "type Circle(r : float) ="
                      "    interface IShape with"
                      "        member x.Area = 3.0 * r * r"
                      "type Other() ="
                      "    member x.Nope = 1"
                      "let test (o : obj) = if o :? IShape then 1 else 0"
                      "let a = print (test (Circle 1.0 :> obj))"
                      "let b = print (test (Other() :> obj))"
                      "let c = print (test (7 :> obj))" ]
            Expect.equal out "1\n0\n0\n" "classes implementing it, and nothing else"
        }
        test "pattern-position tests match the expression form" {
            let out =
                run [ "let classify (o : obj) ="
                      "    match o with"
                      "    | :? list<int> -> \"list\""
                      "    | :? string as s -> s"
                      "    | :? array<int> -> \"array\""
                      "    | _ -> \"other\""
                      "let a = print (classify ([ 1 ] :> obj))"
                      "let b = print (classify (\"hi\" :> obj))"
                      "let c = print (classify ([| 2 |] :> obj))"
                      "let d = print (classify (9 :> obj))" ]
            Expect.equal out "list\nhi\narray\nother\n" "same answers in a match"
        }
        test "a parenthesized destructure binds ALL its names" {
            // `let (k, v) = e` parses as one FLAT ParenPat — no TuplePat,
            // just a comma — and every phase treated it as a simple binding
            // named k: v was never bound, and the mistyping silently
            // corrupted enclosing type variables
            let out =
                run [ "let f () ="
                      "    let (k, v) = (1, \"a\")"
                      "    v + string k"
                      "let a = print (f ())" ]
            Expect.equal out "a1\n" "both names, correctly typed"
        }
        test "destructuring an indexed tuple element" {
            // the index site records the ELEMENT type; tuples are uniform refs
            let out =
                run [ "let f (elements : (int * string)[]) ="
                      "    let (k, v) = elements.[0]"
                      "    v"
                      "let a = print (f [| (1, \"won\") |])" ]
            Expect.equal out "won\n" "$ref element indexing"
        }
    ]

[<Tests>]
let interopSurfaceTests =
    testList "read contracts and chained calls" [
        test "high-precedence application: C(1).Get() chains" {
            let out =
                run [ "type C(v : int) ="
                      "    member x.Get() = v + 1"
                      "    member x.Plus(k : int) = v + k"
                      "let a = print (C(1).Get())"
                      "let b = print (C(1).Plus 5)"
                      "let c = print (C(9).Get() + C(1).Get())" ]
            Expect.equal out "2\n6\n12\n" "the dot chains onto the call"
        }
        test "a static member is usable above its declaration" {
            let out =
                run [ "type HS(v : int) ="
                      "    member x.UseIt(o : seq<int>) = (HS.Build o).V"
                      "    member x.V = v"
                      "    static member Build(o : seq<int>) ="
                      "        let mutable n = 0"
                      "        for e in o do n <- n + e"
                      "        HS(n)"
                      "let h = HS(0)"
                      "let a = print (h.UseIt [ 1; 2; 3 ])" ]
            Expect.equal out "6\n" "forward references park until the class is complete"
        }
        test "ISet is a read contract the type test can find" {
            let out =
                run [ "type Tiny(v : int) ="
                      "    member x.Has(k : int) = k = v"
                      "    interface ISet<int> with"
                      "        member x.Count = 1"
                      "        member x.Contains(item) = x.Has item"
                      "        member x.Overlaps(o : seq<int>) = false"
                      "        member x.SetEquals(o : seq<int>) = false"
                      "        member x.IsSubsetOf(o : seq<int>) = false"
                      "        member x.IsProperSubsetOf(o : seq<int>) = false"
                      "        member x.IsSupersetOf(o : seq<int>) = false"
                      "        member x.IsProperSupersetOf(o : seq<int>) = false"
                      "let probe (o : obj) ="
                      "    match o with"
                      "    | :? ISet<int> as s -> if s.Contains 7 then 1 else 0"
                      "    | _ -> -1"
                      "let a = print (probe (Tiny 7 :> obj))"
                      "let b = print (probe (Tiny 8 :> obj))"
                      "let c = print (probe (5 :> obj))" ]
            Expect.equal out "1\n0\n-1\n" "dispatches Contains through the interface"
        }
    ]

[<Tests>]
let genericArrayTests =
    testList "generic arrays and the value restriction" [
        test "a generic module function can build and fill arrays at any element type" {
            // `let a = Array.zeroCreate n` is an APPLICATION: the value
            // restriction keeps it monomorphic, tied to the enclosing 'a, so
            // the stamper knows every array op's element type per copy
            let out =
                run [ "module A ="
                      "    let ofList (xs : 'a list) : 'a[] ="
                      "        let mutable n = 0"
                      "        for _ in xs do n <- n + 1"
                      "        let a = Array.zeroCreate n"
                      "        let mutable i = 0"
                      "        for x in xs do"
                      "            a.[i] <- x"
                      "            i <- i + 1"
                      "        a"
                      "let a = A.ofList [ 1; 2; 3 ]"
                      "let p = print a.[2]"
                      "let b = A.ofList [ \"x\"; \"y\" ]"
                      "let q = print b.[1]"
                      "let c = A.ofList [ 1.5; 2.5 ]"
                      "let r = print c.[0]" ]
            Expect.equal out "3\ny\n1.5\n" "int, string and float element stamps all run"
        }
        test "string arrays and string char access do not collide" {
            // `b.[i]` on string[] reads an ELEMENT; `s.[i]` on string reads
            // a CHAR — the marker for the receiver-is-string case is a
            // sentinel precisely so these two stay apart
            let out =
                run [ "let b = [| \"hello\"; \"world\" |]"
                      "let s = b.[1]"
                      "let p = print s"
                      "let q = print s.[0]"
                      "let r = print b.Length"
                      "let t = print s.Length" ]
            Expect.equal out "world\nw\n2\n5\n" "element read, char read, both lengths"
        }
        test "local non-values stay monomorphic, local values still generalize" {
            let out =
                run [ "let go () ="
                      "    let empty = []"          // a VALUE: generalizes
                      "    let one = 1 :: empty"
                      "    let s = \"a\" :: empty"  // same empty, other type
                      "    print (Seq.length one + Seq.length s)"
                      "let a = go ()" ]
            Expect.equal out "2\n" "the [] literal is still polymorphic locally"
        }
    ]

[<Tests>]
let stdlibModuleTests =
    testList "stdlib: List, Array and Seq as real modules" [
        test "List: sort, fold with an operator section, sum, contains" {
            let out =
                run [ "let a = print (List.head (List.sort [ 3; 1; 2 ]))"
                      "let b = print (List.fold (+) 0 [ 1; 2; 3 ])"
                      "let c = print (List.sum [ 1.5; 2.5 ])"
                      "let d = print (if List.contains \"x\" [ \"y\"; \"x\" ] then 1 else 0)"
                      "let e = print (List.last (List.sortBy (fun x -> -x) [ 3; 1; 2 ]))"
                      "let f = print (List.item 2 (List.append [ 1 ] [ 2; 3 ]))" ]
            Expect.equal out "1\n6\n4\n1\n1\n3\n" "list surface"
        }
        test "Array: sort, map, unzip round-trips at multiple element types" {
            let out =
                run [ "let a = print ((Array.sort [| 3; 1; 2 |]).[0])"
                      "let b = print (Array.sum (Array.map (fun x -> x * x) [| 1; 2; 3 |]))"
                      "let c = print ((Array.rev [| \"x\"; \"y\" |]).[0])"
                      "let d = print ((Array.sortBy (fun s -> String.length s) [| \"ccc\"; \"a\"; \"bb\" |]).[0])"
                      "let e ="
                      "    let x, y = Array.unzip (Array.zip [| 1; 2 |] [| \"a\"; \"b\" |])"
                      "    print (x.[1] + String.length y.[1])" ]
            Expect.equal out "1\n14\ny\na\n3\n" "array surface"
        }
        test "Seq: lazy combinators compose and materialize" {
            let out =
                run [ "let a = print (Seq.length (Seq.append [ 1; 2 ] [| 3 |]))"
                      "let b = print (Seq.head (Seq.skip 2 [ 1; 2; 3; 4 ]))"
                      "let c = print (Seq.length (Seq.collect (fun x -> Seq.replicate x x) [ 1; 2; 3 ]))"
                      "let d = print (Seq.head (Seq.sort [ \"b\"; \"a\" ]))"
                      "let e = print (Seq.reduce (+) (Seq.mapi (fun i x -> i * x) [ 1; 2; 3 ]))"
                      "let f = print ((Seq.toArray (Seq.singleton 5)).[0])"
                      "let g = print (Seq.last (Seq.rev [ 3; 1; 2 ]))" ]
            Expect.equal out "3\n3\n6\na\n8\n5\n3\n" "seq surface"
        }
        test "an operator section is the operator as a function" {
            let out =
                run [ "let f = (+)"
                      "let a = print (f 1 2)"
                      "let b = print ((*) 3 4)"
                      "let c = print (List.fold (+) 0.5 [ 1.0; 2.0 ])"
                      "let d = print (if (<) 1 2 then 1 else 0)" ]
            Expect.equal out "3\n12\n3.5\n1\n" "sections at int, float and comparison"
        }
        test "assignment constrains the target: an option cell learns its payload" {
            let out =
                run [ "let f (xs : seq<int>) (b : bool) ="
                      "    let mutable inner = None"
                      "    if b then inner <- Some (xs.GetEnumerator())"
                      "    match inner with"
                      "    | Some en ->"
                      "        en.MoveNext() |> ignore"
                      "        en.Current"
                      "    | None -> -1"
                      "let a = print (f [ 7; 8 ] true)"
                      "let b = print (f [ 7; 8 ] false)" ]
            Expect.equal out "7\n-1\n" "the enumerator dispatches through the learned interface"
        }
        test "a property setter does not corrupt the constructor's generality" {
            // the class-level value variable and the setter parameter unify;
            // the representative must stay the one the ctor scheme quantifies,
            // or every ctor use shares one raw variable and the first
            // concrete use grounds them ALL (map became int-only)
            let out =
                run [ "[<AllowNullLiteral>]"
                      "type Linked<'K, 'V>(key : 'K, value : 'V, next : Linked<'K, 'V>) ="
                      "    let mutable value = value"
                      "    member x.Key = key"
                      "    member x.Next = next"
                      "    member x.Value"
                      "        with get() = value"
                      "        and set v = value <- v"
                      "let rec map (mapping : ('K -> 'V -> 'T)) (node : Linked<'K, 'V>) ="
                      "    if isNull node then null"
                      "    else Linked(node.Key, (mapping (node.Key) (node.Value)), map mapping node.Next)"
                      "let one = Linked(1, 2, Linked(3, 4, null))"
                      "let r = map (fun k v -> string (k + v)) one"
                      "let p = print r.Value"
                      "let q = print r.Next.Value" ]
            Expect.equal out "3\n7\n" "map stays generic in its result type"
        }
    ]

[<Tests>]
let halfEqualityTests =
    testList "float16 equality is IEEE, not the bit pattern" [
        test "negative zero equals zero; NaN equals nothing" {
            let out =
                run [ "let nz = -0.0h"
                      "let z = 0.0h"
                      "let a = print (if nz = z then 1 else 0)"
                      "let nan = 0.0h / 0.0h"
                      "let b = print (if nan = nan then 1 else 0)"
                      "let c = print (if nan <> nan then 1 else 0)"
                      "let d = print (if 1.5h = 1.5h then 1 else 0)"
                      "let e = print (if 1.5h <> 2.5h then 1 else 0)" ]
            Expect.equal out "1\n0\n1\n1\n1\n" "IEEE semantics at half width"
        }
    ]
