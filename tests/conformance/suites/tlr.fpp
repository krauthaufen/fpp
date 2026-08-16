// Ported from dotnet/fsharp tests/fsharp/core/tlr/test.fsx into the common
// F#/F++ subset. Mostly COMPILE tests for top-level-rise (TLR) shapes; the
// only observable output is the MiscDetupleTestFromAndyRay print, kept.
// Dropped: the value-recursion inner1/2/3 record cycles (FS0040 delayed
// init, as in letrec.fpp) and overTLambda (a generalized `raise` return —
// its class of shape is covered by enclosing1/2).
module Core_tlr

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

module CompilationTests =
    let consume x = x

    // not TLR - constant - trivial expr
    let notSinceTrivial1 = 1
    let notSinceTrivial2 = 1.2
    let notSinceTrivial3 = true

    // TLR constants - non-trivial (e.g. allocating)
    type xy<'a, 'b> = { x : 'a; y : 'b }
    let tlrValList = [ 1; 2; 3; 4 ]
    let tlrValTuple = (1, 2, 3, 4)
    let tlrValRecord = { x = 1; y = 2 }

    // TLR constants - transitively
    let tlrValTransitiveList = [ tlrValList; tlrValList ]
    let tlrValTransitiveTuple = ("transitively a TLR constant", tlrValList)
    let tlrValTransitiveRecord = { x = "transitively a TLR constant"; y = tlrValList }

    // TLR constants - polymorphic
    type node<'a> = INT of int | ALPHA of 'a

    let tlrLambdaTests () =
        let tlrNonRecAppliedAll3Args (x : int) (y : int) (z : int) = x + y + z in
        let _ = tlrNonRecAppliedAll3Args 1 2 3 in
        let tlrNonRecApplied2of3Args (x : int) (y : int) (z : int) = x + y + z in
        let _ = tlrNonRecApplied2of3Args 1 2 in
        let rejectNonRecApplied0of3Args (x : int) (y : int) (z : int) = x + y + z in
        let _ = rejectNonRecApplied0of3Args in
        let rec tlrRecAppliedAll3Args (x : bool) (y : int) (z : int) =
            if x then tlrRecAppliedAll3Args false y z else y + z in
        let _ = tlrRecAppliedAll3Args true 2 3 in
        let rec tlrRecApplied2of3Args (x : bool) (y : int) (z : int) =
            if x then let f = tlrRecApplied2of3Args false y in f z else y + z in
        let _ = tlrRecApplied2of3Args true 2 in
        let rec rejectRecApplied0of3Args (x : bool) (y : int) (z : int) =
            if x then let f = rejectRecApplied0of3Args in f false y z else y + z in
        let _ = rejectRecApplied0of3Args in
        ()

    // polymorphic constants: arity 0, in fact type-functions
    let enclosing1 (a : int) =
        let tlrInnerFreePolymorphicConstant = None in
        if tlrInnerFreePolymorphicConstant = None then 0 else 1

    let enclosing2 (a : 'a) =
        let tlrInnerPolymorphicConstant = (None : 'a option) in
        if tlrInnerPolymorphicConstant = None then 0 else 1

    // env tests
    let xC = 1, 2, 3
    let yC = 3, 2, 1

    let envTestFreesUnitArg () = xC, yC
    let envTestFreesNArg (n : int) = xC, yC, n
    let uses = envTestFreesUnitArg (), envTestFreesNArg 1

    let dependent1 id (xa : 'alpha) =
        let envTestFreesUnitArgOpen () = id xC, yC in
        let envTestFreesNArgOpen (n : int) = id xC, yC, n in
        let envPolymorphicSelf arg = if arg = xa then 1 else 2 in
        let envPolymorphicViaCall () = envPolymorphicSelf xa in
        let uses =
            envTestFreesUnitArgOpen (),
            envTestFreesNArgOpen 1,
            envPolymorphicSelf xa,
            envPolymorphicViaCall ()
        12

    // mixed recursion: inner recursing with outer
    let mixedRecursionTest (z : int) =
        let rec mixed_g1 (x1 : int) (x2 : int) =
            let rec mixed_g2 (y2 : int) =
                let r1, r2 = mixed_g1 x2 y2
                r1 + mixed_g2 z
            let res1 = mixed_g2 (x1 + x2)
            let res2 = mixed_g2
            res1, res2
        mixed_g1 1 2

    let innerOuterCallBeforeETpsKnown (xx1 : 'alpha) (y : 'beta) =
        let freeBeta () = let (uses : 'beta) = y in () in
        let rec innerOuter_g (x1 : 'alpha) =
            let innerOuter_g2 (x2 : 'alpha2) = innerOuter_g x1 in
            let (includesBeta : unit) = freeBeta () in
            (innerOuter_g2 12 : int)
        innerOuter_g

    // arity 0 tests, esp with a type closure
    let arityZeroTests (xalpha : 'alpha) (xbeta : 'beta) =
        let arityZeroMono = (1, 2, true) in
        let arityZeroAlpha = (1, 2, (None : 'alpha option)) in
        let arityZeroAlphaBeta = (1, 2, (None : 'alpha option), (None : 'beta option)) in
        arityZeroMono, arityZeroAlpha, arityZeroAlphaBeta

    // free occurrence, but at a type instance
    let freeOccurrenceAtInstanceTest (u : unit) (b : 'beta) =
        let freeOccurrenceTestPolyFun (x : 'alpha) = x in
        let useAtInt = freeOccurrenceTestPolyFun 3 in
        let useAtIntList = freeOccurrenceTestPolyFun [ 3 ] in
        let useAtBool = freeOccurrenceTestPolyFun true in
        let instAtInt = (freeOccurrenceTestPolyFun : int -> int) in
        let instAtIntList = (freeOccurrenceTestPolyFun : int list -> int list) in
        let instAtBeta = (freeOccurrenceTestPolyFun : 'beta -> 'beta) in
        ()

    // DROPPED: inner1/2/3 value-recursion record cycles (FS0040)

    // creates cctor if needed
    let innerConst () =
        let localconst = ("cctor", 0) in
        let capture tag = if tag then localconst else "a3", 3 in
        capture true

    // lifting tests
    let add (x : int) (y : int) = (x + y : int)

    let liftOverLambda =
        fun (x : int) ->
            let liftOverLambdaExpectConst = Some (1, 2, 3, 4) in
            let liftOverLambdaExpectFunc y = add x y, liftOverLambdaExpectConst in
            let res = liftOverLambdaExpectConst, liftOverLambdaExpectFunc 1 in
            res

    // lifting over letrec
    let overLetrec (b : bool) =
        let rec overLetrec_f1 x = overLetrec_f2 x
        and overLetrec_f2 x = overLetrec_f3 x
        and overLetrec_f3 x =
            let overLetrec_expectConst = (7, 8) in
            let overLetrec_expectFunc a = add a x, overLetrec_expectConst in
            overLetrec_expectConst, overLetrec_expectFunc x
        overLetrec_f1 9

    // lifting over let
    let overLet (b : bool) =
        let overlet_x1 = 11 in
        let overlet_x2 =
            let overLet_expectConst2 = (2, 2, 2) in
            12 in
        let overlet_x3 = 13 in
        let overlet_x4 = 14 in
        let overLet_expectFunc a = add a overlet_x1 in
        overlet_x2, overlet_x1

    // let test
    let letTest2 =
        let a = 1 in
        let b = 2 in
        let a = b in
        let b = a in
        a, b   // expect 2,2 after the shadowing swap-that-isn't

    let letTest3 =
        let rec v = fun n -> 1 + w (n - 1)
        and w = fun n -> if n = 0 then 0 else v (n - 1)
        v, w

    let _ = fun x -> let liftOverTopLambda = [ (1, 2, 3) ] in 12

    let _ =
        match [] with
        | [] -> let liftOverNilMatchNil = [ 902 ] in 12
        | x :: xs -> let liftOverNilMatchCons = [ x ] in 12

// exercise the compiled shapes that return values
test "tlr-letTest2" (CompilationTests.letTest2 = (2, 2))
test "tlr-overLet" (CompilationTests.overLet true = (12, 11))
test "tlr-overLetrec" (fst (CompilationTests.overLetrec true) = (7, 8))
test "tlr-enclosing" (CompilationTests.enclosing1 5 = 0 && CompilationTests.enclosing2 "s" = 0)
test "tlr-dependent1" (CompilationTests.dependent1 (fun t -> t) 42 = 12)
test "tlr-innerConst" (CompilationTests.innerConst () = ("cctor", 0))
let lv, lw = CompilationTests.letTest3
test "tlr-letTest3" (lv 3 = 2 && lw 4 = 2)

module MiscDetupleTestFromAndyRay =
    type LutInitAst =
        | LutInput of int
        | LutAnd of LutInitAst * LutInitAst

    let i0, i1 = LutInput 0, LutInput 1

    let rec eval n (s : LutInitAst) =
        match s with
        | LutInput a -> ((n >>> a) &&& 1)
        | LutAnd (a, b) -> (eval n a) &&& (eval n b)

    let eval_lut lut_n (ops : LutInitAst) =
        let rec eval_n n : string =
            if n = (1 <<< lut_n) then ""
            else (eval_n (n + 1)) + (if (eval n ops) = 1 then "1" else "0")
        eval_n 0

    let test2 () =
        let g = eval_lut 2 (LutAnd (i0, i1)) in
        printfn "%s" g

MiscDetupleTestFromAndyRay.test2 ()

printfn "DONE tests=%d failures=%d" ntests failures
