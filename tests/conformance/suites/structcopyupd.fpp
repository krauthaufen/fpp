// COPY-UPDATE OVER A RECORD WITH [<Struct>]-TYPED FIELDS.
//
// A record's `[<Struct>]` field is laid out INLINE — its leaves occupy their
// own bytes inside the record, which is what makes `s.Turn.X` one load. The
// construction path knew that; the copy-update path did not, and copied each
// field as ONE uniform word. So `{ s with Turn = v }` stored a POINTER over
// the first four bytes of an inline value and left the rest as it found it:
// the assigned field came back as a garbage bit pattern and every OTHER
// struct field of the record read zero. `--strict` said nothing, because
// nothing was missing — the wrong bytes were written.
//
// It shipped a broken demo (a camera controller whose state was wiped on
// every update while its Enabled flag stayed true) and is #56 in
// ~/claude/fpp-base-snags.md. Scale is irrelevant: the twelve lines of the
// first case reproduce it.
//
// The variants below are the narrowing that found it — assigning a NON-struct
// field wipes the struct fields just the same, so the trigger was never the
// assignment; an explicit full literal is correct; and the same shape with a
// plain inner record is correct, which is what named the inline layout.
module Core_structcopyupd

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" name got want

[<Struct>]
type V2 = { X : float; Y : float }

type St =
    { Enabled : bool
      Turn : V2
      Pos : V2
      Speed : float }

let showV (v : V2) : string = string v.X + "," + string v.Y
let showSt (s : St) : string =
    showV s.Turn + " " + showV s.Pos + " " + string s.Speed + " " + string s.Enabled

let s0 = { Enabled = true; Turn = { X = 0.0; Y = 0.0 }; Pos = { X = 2.0; Y = 3.0 }; Speed = 1.5 }

// the field assigned is a struct: it must arrive, and the OTHER struct field
// must survive untouched
let s1 = { s0 with Turn = { X = 1.5; Y = 0.25 } }
eq "assign-a-struct-field" (showSt s1) "1.5,0.25 2,3 1.5 True"

// assigning a SCALAR field: every struct field is copied, none is wiped
let s2 = { s0 with Speed = 2.5 }
eq "assign-a-scalar-field" (showSt s2) "0,0 2,3 2.5 True"

// assigning the flag alone
let s3 = { s0 with Enabled = false }
eq "assign-a-bool-field" (showSt s3) "0,0 2,3 1.5 False"

// two struct fields at once
let s4 = { s0 with Turn = { X = 7.0; Y = 8.0 }; Pos = { X = 9.0; Y = 10.0 } }
eq "assign-both-struct-fields" (showSt s4) "7,8 9,10 1.5 True"

// a struct field assigned from ANOTHER record's field, not from a literal
let s5 = { s0 with Turn = s4.Pos }
eq "assign-from-a-field" (showSt s5) "9,10 2,3 1.5 True"

// chained: the result of one copy-update is the base of the next, both
// through a binding and with the brace expression written inline (the base
// of a copy-update is any EXPRESSION — a call, another copy-update — and
// only a dotted NAME parsed as one; anything else reached lowering as a
// computation body)
let s6a = { s0 with Speed = 3.0 }
let s6 = { s6a with Turn = { X = 1.0; Y = 2.0 } }
let s6b = { { s0 with Speed = 3.0 } with Turn = { X = 1.0; Y = 2.0 } }
eq "chained-inline" (showSt s6b) "1,2 2,3 3 True"
let mkSt () : St = s0
let s6c = { mkSt () with Speed = 4.0 }
eq "the-base-is-a-call" (showSt s6c) "0,0 2,3 4 True"
eq "chained-copy-updates" (showSt s6) "1,2 2,3 3 True"

// the control: an explicit full literal was always right
let s7 = { Enabled = s0.Enabled; Turn = { X = 1.5; Y = 0.25 }; Pos = s0.Pos; Speed = s0.Speed }
eq "explicit-full-literal" (showSt s7) "1.5,0.25 2,3 1.5 True"

// the OUTER record a struct too
[<Struct>]
type SSt = { STurn : V2; SSpeed : float }
let q0 = { STurn = { X = 4.0; Y = 5.0 }; SSpeed = 1.0 }
let q1 = { q0 with SSpeed = 2.0 }
let q2 = { q0 with STurn = { X = 6.0; Y = 7.0 } }
eq "struct-outer-assign-scalar" (showV q1.STurn + " " + string q1.SSpeed) "4,5 2"
eq "struct-outer-assign-struct" (showV q2.STurn + " " + string q2.SSpeed) "6,7 1"

// a struct INSIDE a struct, updated at both levels
[<Struct>]
type Cam = { Location : V2; Sky : V2 }
type World = { Cam : Cam; Frame : int }
let w0 = { Cam = { Location = { X = 1.0; Y = 2.0 }; Sky = { X = 0.0; Y = 1.0 } }; Frame = 0 }
let w1 = { w0 with Cam = { w0.Cam with Location = { X = 8.0; Y = 9.0 } } }
eq "nested-struct-copy-update" (showV w1.Cam.Location + " " + showV w1.Cam.Sky + " " + string w1.Frame) "8,9 0,1 0"

// the control that named the layout: the same shape with a PLAIN inner record
type P2 = { PX : float; PY : float }
type PSt = { PTurn : P2; PSpeed : float }
let p0 = { PTurn = { PX = 1.0; PY = 2.0 }; PSpeed = 1.0 }
let p1 = { p0 with PSpeed = 2.0 }
eq "plain-inner-record" (string p1.PTurn.PX + "," + string p1.PTurn.PY + " " + string p1.PSpeed) "1,2 2"

// a copy-update inside a LOOP, so the collector runs over the shape
let mutable acc = s0
let loop =
    for i in 1 .. 200 do
        acc <- { acc with Turn = { X = float i; Y = float (i * 2) } }
eq "copy-update-in-a-loop" (showSt acc) "200,400 2,3 1.5 True"

printfn "DONE tests=%d failures=%d" ntests failures
