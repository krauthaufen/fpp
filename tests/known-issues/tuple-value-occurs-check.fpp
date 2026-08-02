// A reference tuple built from two pattern binders inside a `while`, where
// the map it is stored into was bound EMPTY before the loop, reports
//
//   the type 'a * 'a would contain itself
//
// at the tuple expression. It is the first thing standing between the
// FSharp.Data.Adaptive port and the end of IndexList.fs (`Pairwise` and
// `PairwiseV`, both shapes, both lines).
//
// DIAGNOSIS, as far as it goes: the occurs check says the tuple's element
// type IS the variable being bound to `'a * 'a`, so `res`'s value type and
// `v0`'s type have become one variable somewhere. What is NOT the cause:
//
//   * the implicit struct-tuple payload pattern (`ValueSome (i1, v1, r)`).
//     The same shape type checks on its own, at arity two and three, and
//     replacing it here with the explicit `struct(...)` form does not help.
//   * the `let mutable x = x` shadowing on its own.
//
// The trigger needs the whole shape together: reducing it — dropping the
// loop, the outer match, or the shadowing — makes the error disappear or
// turn into an honest mismatch. That is why this file is not smaller.

module M

type Mp<'k, 'v>(n : int) =
    member x.N = n
    static member Empty : Mp<'k, 'v> = Mp<'k, 'v>(0)

module Mp =
    let empty<'k, 'v> : Mp<'k, 'v> = Mp<'k, 'v>.Empty
    let isEmpty (m : Mp<'k, 'v>) = m.N = 0
    let add (k : 'k) (v : 'v) (m : Mp<'k, 'v>) : Mp<'k, 'v> = m
    let tryRemoveMinV (m : Mp<'k, 'v>) : voption<struct('k * 'v * Mp<'k, 'v>)> = ValueNone

type Lst<'T>(l : int) =
    member x.Pairwise () =
        match Mp.tryRemoveMinV (Mp.empty : Mp<int, 'T>) with
        | ValueSome (struct(i0, v0, rest)) ->
            let mutable res = Mp.empty
            let mutable rest = rest
            let mutable i0 = i0
            let mutable v0 = v0
            while not (Mp.isEmpty rest) do
                match Mp.tryRemoveMinV rest with
                | ValueSome (i1, v1, r) ->
                    // reported here: `the type 'a * 'a would contain itself`
                    res <- Mp.add i0 (v0, v1) res
                    i0 <- i1
                    v0 <- v1
                    rest <- r
                | ValueNone -> ()
            res.N
        | ValueNone -> 0

let go = printfn "%d" (Lst<string>(0).Pairwise ())
