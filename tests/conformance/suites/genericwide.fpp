// A GENERIC RECORD WITH MANY GENERIC FIELDS.
//
// A construction in the shared (canonical) body picks its heap SHAPE from the
// witnesses at run time — is this slot a pointer or a raw scalar? — and the
// pick was a decision tree over the generic slots: 2^g leaves, each interning
// its own type id. `M44<'a>` has sixteen, so the build asked for 65536 shapes
// and died on the tid table before emitting anything.
//
// That is one of the reasons fpp.base gave up on a scalar-GENERIC design and
// generates a type per scalar instead (~/claude/fpp-base-snags.md #12). Past a
// handful of slots the shape now falls back to the conservative tagged form
// the compiler already uses for an unresolved witness.
module Core_genericwide

let mutable ntests = 0
let mutable failures = 0
let eq (name : string) (got : string) (want : string) : unit =
    ntests <- ntests + 1
    if got <> want then
        failures <- failures + 1
        printfn "FAIL %s: got %s want %s" name got want

type M44<'a> = { M00 : 'a; M01 : 'a; M02 : 'a; M03 : 'a; M10 : 'a; M11 : 'a; M12 : 'a; M13 : 'a; M20 : 'a; M21 : 'a; M22 : 'a; M23 : 'a; M30 : 'a; M31 : 'a; M32 : 'a; M33 : 'a }

let mk (v : 'a) : M44<'a> = { M00 = v; M01 = v; M02 = v; M03 = v; M10 = v; M11 = v; M12 = v; M13 = v; M20 = v; M21 = v; M22 = v; M23 = v; M30 = v; M31 = v; M32 = v; M33 = v }

// the ARITHMETIC is concrete (F# would need `inline` for a generic `+`);
// what stays generic is `mk`, whose construction is the canonical body that
// picks a shape from its witnesses
let addF (a : M44<float>) (b : M44<float>) : M44<float> =
    { M00 = a.M00 + b.M00; M01 = a.M01 + b.M01; M02 = a.M02 + b.M02; M03 = a.M03 + b.M03
      M10 = a.M10 + b.M10; M11 = a.M11 + b.M11; M12 = a.M12 + b.M12; M13 = a.M13 + b.M13
      M20 = a.M20 + b.M20; M21 = a.M21 + b.M21; M22 = a.M22 + b.M22; M23 = a.M23 + b.M23
      M30 = a.M30 + b.M30; M31 = a.M31 + b.M31; M32 = a.M32 + b.M32; M33 = a.M33 + b.M33 }

let addI (a : M44<int>) (b : M44<int>) : M44<int> =
    { M00 = a.M00 + b.M00; M01 = a.M01 + b.M01; M02 = a.M02 + b.M02; M03 = a.M03 + b.M03
      M10 = a.M10 + b.M10; M11 = a.M11 + b.M11; M12 = a.M12 + b.M12; M13 = a.M13 + b.M13
      M20 = a.M20 + b.M20; M21 = a.M21 + b.M21; M22 = a.M22 + b.M22; M23 = a.M23 + b.M23
      M30 = a.M30 + b.M30; M31 = a.M31 + b.M31; M32 = a.M32 + b.M32; M33 = a.M33 + b.M33 }

// three instantiations of the same canonical body: a float (a boxed wide
// scalar), an int (raw under int-stamping) and a string (a pointer)
let mf : M44<float> = mk 1.5
let mi : M44<int> = mk 2
let ms : M44<string> = mk "s"

eq "float-fields" (string (addF mf mf).M33) "3"
eq "int-fields" (string (addI mi mi).M00) "4"
eq "reference-fields" ms.M11 "s"

// the shapes must survive a collection: build many, then read the first back
let many : M44<int> list = List.map (fun i -> mk i) [ 1 .. 300 ]
eq "many-survive-allocation" (string (List.length many) + " " + string (List.head many).M23) "300 1"
eq "and-the-originals-are-intact" (string mf.M00 + " " + string mi.M11 + " " + ms.M32) "1.5 2 s"

printfn "DONE tests=%d failures=%d" ntests failures
