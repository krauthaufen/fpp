// KNOWN ISSUE: slicing a LIST traps at run time.
//
//   let l = [ 1; 2; 3; 4 ]
//   l.[1..2]      // F# = [2; 3]; F++ traps in the module initialiser
//
// Array and string slices are fine. The slice lowering (Lower.sliceRead)
// builds an ARRAY and fills it with indexed reads, which is wrong for a list
// on both counts — the element access and the result type. Supporting it means
// a list sentinel from Infer (like the `$str` one strings already get) and a
// list-shaped lowering (skip/take), not a tweak to the array path.
module ListSlicing

let l = [ 1; 2; 3; 4 ]
printfn "%d" (List.sum l.[1..2])   // F# prints 5; F++ traps
