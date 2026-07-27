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
        test "float has no remainder, and says so" {
            // wasm has no float rem; declaring no instance turns that into a
            // type error instead of a backend failure
            let msgs = diagnostics [ "let a = 1.5 % 2.0" ]
            Expect.contains msgs "no instance Rem<float, float>" "reported as a missing instance"
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
