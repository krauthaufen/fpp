namespace Fpp

open Fpp.Prelude
open Fpp.Syntax
open Fpp.Query

/// Offset -> line/column translation (0-based, LSP convention).
module Lines =

    let starts (text : string) : int[] =
        let v = vecNew<int> ()
        vecAdd v 0
        for i in 0 .. strLen text - 1 do
            if charAt text i = '\n' then vecAdd v (i + 1)
        v.ToArray()

    let toLineCol (starts : int[]) (offset : int) : int * int =
        let mutable lo = 0
        let mutable hi = Array.length starts - 1
        while lo < hi do
            let mid = (lo + hi + 1) / 2
            if starts.[mid] <= offset then lo <- mid else hi <- mid - 1
        lo, offset - starts.[lo]

type DiagnosticInfo =
    { Path : string
      Line : int
      Col : int
      EndLine : int
      EndCol : int
      Message : string }

type OutlineItem =
    { Name : string
      /// "module" | "type" | "let"
      Detail : string
      StartLine : int
      StartCol : int
      EndLine : int
      EndCol : int
      Children : OutlineItem list }

module private Outline =

    let span (starts : int[]) (n : GreenNode) : (int * int) * (int * int) =
        match Green.tokens (GNode n) with
        | [] -> (0, 0), (0, 0)
        | ts ->
            let first = List.head ts
            let last = List.last ts
            Lines.toLineCol starts first.Offset,
            Lines.toLineCol starts (last.Offset + strLen last.Text)

    let private firstIdentText (g : Green) : string option =
        Green.tokens g
        |> List.tryFind (fun t -> t.Kind = Ident)
        |> Option.map (fun t -> t.Text)

    /// Dotted name after `module` / `open`: leading Ident/"." token run.
    let private dottedName (n : GreenNode) : string =
        let ts =
            Green.tokens (GNode n)
            |> List.filter (fun t -> t.Kind = Ident || (t.Kind = Operator && t.Text = "."))
        match ts with
        | [] -> "?"
        | _ ->
            let rec take acc (rest : Token list) (wantIdent : bool) =
                match rest with
                | t :: tl when wantIdent && t.Kind = Ident -> take (t.Text :: acc) tl false
                | t :: tl when not wantIdent && t.Text = "." -> take ("." :: acc) tl true
                | _ -> List.rev acc
            take [] ts true |> String.concat ""

    let rec items (starts : int[]) (children : Green list) : OutlineItem list =
        children
        |> List.choose (fun c ->
            match c with
            | GNode n ->
                let (sl, sc), (el, ec) = span starts n
                let make name detail kids =
                    Some { Name = name; Detail = detail
                           StartLine = sl; StartCol = sc; EndLine = el; EndCol = ec
                           Children = kids }
                match n.NodeKind with
                | LetDecl ->
                    let name =
                        n.Children
                        |> List.tryPick (fun ch ->
                            match ch with
                            | GNode p when p.NodeKind = IdentPat || p.NodeKind = ParenPat || p.NodeKind = TuplePat ->
                                firstIdentText ch
                            | _ -> None)
                    make (defaultArg name "let") "let" []
                | TypeDecl ->
                    let name =
                        n.Children
                        |> List.tryPick (fun ch ->
                            match ch with
                            | GToken t when t.Kind = Ident -> Some t.Text
                            | _ -> None)
                    make (defaultArg name "type") "type" []
                | ModuleDef | ModuleHeader ->
                    make (dottedName n) "module" (items starts n.Children)
                | _ -> None
            | GToken _ -> None)

/// The workspace: one query database over a set of files. Both the LSP
/// server and the batch CLI talk to the compiler exclusively through this.
/// The auto-opened builtin prelude (FSharp.Core's role): well-known types
/// every file sees without an `open`. No module header, so its exports live
/// under bare names. `option<'a>` aliases the nominal `Option<'a>` so
/// postfix `'v option` and constructor results unify.
module Builtin =

    /// The numeric tower. Operators are two-parameter classes with an
    /// associated result — the shape that makes `M * v` ordinary rather than
    /// special — and the closed classes on top are what generic code
    /// constrains against so an unannotated routine does not infer a chain
    /// of unreduced projections.
    let private numericClasses =
        let opClass (cls : string) (op : string) =
            [ "class " + cls + "<'a, 'b>"
              "    type Result"
              "    static (" + op + ") : 'a -> 'b -> Result" ]
        List.concat [
            opClass "Add" "+"
            opClass "Sub" "-"
            opClass "Mul" "*"
            opClass "Div" "/"
            opClass "Rem" "%"
            [ "class Num<'a>"
              "    when Add<'a, 'a> = 'a"
              "    when Sub<'a, 'a> = 'a"
              "    when Mul<'a, 'a> = 'a"
              "    static Zero : 'a"
              "    static One : 'a"
              "class Fractional<'a>"
              "    when Num<'a>"
              "    when Div<'a, 'a> = 'a"
              "class Integral<'a>"
              "    when Num<'a>"
              "    when Div<'a, 'a> = 'a"
              "    when Rem<'a, 'a> = 'a"
              // Comparison is ONE operation returning an int, not four
              // predicates: `<` and friends are notation for `compare _ _ < 0`
              // wherever the instance is not primitive. `=`/`<>` are absent on
              // purpose — structural equality is total and needs no instance.
              "class Ordered<'a>"
              "    static compare : 'a -> 'a -> int"
              "class Neg<'a>"
              "    static (~-) : 'a -> 'a"
              "class Abs<'a>"
              "    static abs : 'a -> 'a"
              // min/max deliberately do NOT require Ordered: a vector has no
              // total order but does have a componentwise minimum, and that
              // is the operation graphics code actually wants
              "class MinMax<'a>"
              "    static min : 'a -> 'a -> 'a"
              "    static max : 'a -> 'a -> 'a"
              "class Floating<'a>"
              "    when Fractional<'a>"
              "    static sqrt : 'a -> 'a"
              "    static truncate : 'a -> 'a"
              "    static exp : 'a -> 'a"
              "    static log : 'a -> 'a"
              "    static sin : 'a -> 'a"
              "    static cos : 'a -> 'a"
              "    static tan : 'a -> 'a"
              "    static sinh : 'a -> 'a"
              "    static cosh : 'a -> 'a"
              "    static tanh : 'a -> 'a"
              "    static asin : 'a -> 'a"
              "    static acos : 'a -> 'a"
              "    static atan : 'a -> 'a"
              "    static atan2 : 'a -> 'a -> 'a"
              // `**` is notation for `pow`, not a member spelled `(**)`:
              // that spelling cannot exist, because `(*` opens a comment
              "    static pow : 'a -> 'a -> 'a" ]
        ]

    /// `exp`, `log`, `sin`, `cos`, `tan` and `pow`, written in F++ itself.
    /// wasm has `sqrt`, `abs` and `trunc` as instructions and nothing else,
    /// and there is no libm underneath — so these are the implementation,
    /// not a binding to one.
    ///
    /// Written once, with `~` marking the float-width suffix, and generated
    /// for each width: the algorithms are identical, only the literals differ.
    ///
    /// Accuracy is a few ulp, and NOT bit-identical to .NET: reduction is
    /// Cody-Waite with a three-term split (so it degrades for arguments
    /// past ~1e8), and `pow` goes through `exp (b * log a)`. Recorded in
    /// DIVERGENCES.md.
    let private floatingSource = """
// exact: doubling and halving a float are exact until it goes subnormal,
// which exp's range check has already excluded
let scale2~N~ m k =
    let mutable r = m
    let mutable n = k
    while n > 0.0~ do
        r <- r * 2.0~
        n <- n - 1.0~
    while n < 0.0~ do
        r <- r * 0.5~
        n <- n + 1.0~
    r
let exp~N~ x =
    if x <> x then x
    elif x > 709.782712893384~ then 1.0~ / 0.0~
    elif x < -745.1332191019411~ then 0.0~
    else
        // x = k ln2 + r with |r| <= ln2/2, then Taylor to r^13/13!
        let k = truncate (x * 1.4426950408889634~ + (if x < 0.0~ then -0.5~ else 0.5~))
        let r = (x - k * 0.6931471803691238~) - k * 1.9082149292705877e-10~
        let p =
            1.0~ + r * (1.0~ + r * (0.5~ + r * (0.16666666666666666~
                + r * (0.041666666666666664~ + r * (0.008333333333333333~
                + r * (0.001388888888888889~ + r * (0.0001984126984126984~
                + r * (2.48015873015873e-05~ + r * (2.7557319223985893e-06~
                + r * (2.755731922398589e-07~ + r * (2.5052108385441718e-08~
                + r * 2.08767569878681e-09~)))))))))))
        scale2~N~ p k
let log~N~ x =
    if x <> x then x
    elif x < 0.0~ then 0.0~ / 0.0~
    elif x = 0.0~ then -1.0~ / 0.0~
    else
        // x = m 2^e with m in [sqrt(1/2), sqrt 2), then the atanh series in
        // s = (m-1)/(m+1), where |s| <= 0.1716
        let mutable m = x
        let mutable e = 0.0~
        while m >= 1.4142135623730951~ do
            m <- m * 0.5~
            e <- e + 1.0~
        while m < 0.7071067811865476~ do
            m <- m * 2.0~
            e <- e - 1.0~
        let s = (m - 1.0~) / (m + 1.0~)
        let q = s * s
        let p =
            1.0~ + q * (0.3333333333333333~ + q * (0.2~ + q * (0.14285714285714285~
                + q * (0.1111111111111111~ + q * (0.09090909090909091~
                + q * (0.07692307692307693~ + q * (0.06666666666666667~
                + q * (0.058823529411764705~ + q * 0.05263157894736842~))))))))
        (e * 0.6931471803691238~ + e * 1.9082149292705877e-10~) + 2.0~ * s * p
// pi/2 split three ways, so the reduction keeps its digits for moderately
// large arguments; it degrades past ~1e8
let reduce~N~ x =
    let q = truncate (x * 0.6366197723675814~ + (if x < 0.0~ then -0.5~ else 0.5~))
    ((x - q * 1.5707963267341256~) - q * 6.077100506506192e-11~) - q * 1.2154201862823113e-21~
let quadrant~N~ x =
    let q = truncate (x * 0.6366197723675814~ + (if x < 0.0~ then -0.5~ else 0.5~))
    let m = q - 4.0~ * truncate (q / 4.0~)
    if m < 0.0~ then m + 4.0~ else m
let sinCore~N~ r =
    let q = r * r
    r * (1.0~ + q * (-0.16666666666666666~ + q * (0.008333333333333333~
        + q * (-0.0001984126984126984~ + q * (2.7557319223985893e-06~
        + q * (-2.505210838544172e-08~ + q * (1.6059043836821613e-10~
        + q * -7.647163731819816e-13~)))))))
let cosCore~N~ r =
    let q = r * r
    1.0~ + q * (-0.5~ + q * (0.041666666666666664~ + q * (-0.001388888888888889~
        + q * (2.48015873015873e-05~ + q * (-2.755731922398589e-07~
        + q * (2.08767569878681e-09~ + q * -1.1470745597729725e-11~))))))
let sin~N~ x =
    if x <> x then x
    else
        let n = quadrant~N~ x
        let r = reduce~N~ x
        if n = 0.0~ then sinCore~N~ r
        elif n = 1.0~ then cosCore~N~ r
        elif n = 2.0~ then -(sinCore~N~ r)
        else -(cosCore~N~ r)
let cos~N~ x =
    if x <> x then x
    else
        let n = quadrant~N~ x
        let r = reduce~N~ x
        if n = 0.0~ then cosCore~N~ r
        elif n = 1.0~ then -(sinCore~N~ r)
        elif n = 2.0~ then -(cosCore~N~ r)
        else sinCore~N~ r
// an integer exponent is done by repeated squaring, which is EXACT — the
// exp/log route would return -7.999999999999998 for (-2)^3
let powIntN~N~ a n =
    let mutable r = 1.0~
    let mutable f = a
    let mutable k = n
    while k > 0.0~ do
        let half = truncate (k * 0.5~)
        if k - half - half <> 0.0~ then r <- r * f
        f <- f * f
        k <- half
    r
let pow~N~ a b =
    if b = 0.0~ then 1.0~
    elif b <> b then b
    else
        let k = truncate b
        let mag = if b < 0.0~ then -b else b
        if k = b && mag <= 1024.0~ then
            let r = powIntN~N~ a mag
            if b < 0.0~ then 1.0~ / r else r
        elif a > 0.0~ then exp~N~ (b * log~N~ a)
        elif a = 0.0~ then (if b > 0.0~ then 0.0~ else 1.0~ / 0.0~)
        else
            // a negative base is defined only at an integer exponent, and
            // that case was handled above
            0.0~ / 0.0~
// hyperbolics. Near zero sinh cancels catastrophically in
// (e^x - e^-x)/2, so small arguments take the series instead; cosh has no
// such problem, and tanh saturates rather than overflowing.
let sinh~N~ x =
    if x <> x then x
    else
        let a = if x < 0.0~ then -x else x
        if a < 0.5~ then
            let q = x * x
            x * (1.0~ + q * (0.16666666666666666~ + q * (0.008333333333333333~
                + q * (0.0001984126984126984~ + q * 2.7557319223985893e-06~))))
        else
            let e = exp~N~ x
            (e - 1.0~ / e) * 0.5~
let cosh~N~ x =
    if x <> x then x
    else
        let e = exp~N~ (if x < 0.0~ then -x else x)
        (e + 1.0~ / e) * 0.5~
let tanh~N~ x =
    if x <> x then x
    else
        let a = if x < 0.0~ then -x else x
        if a < 0.5~ then sinh~N~ x / cosh~N~ x
        elif a > 20.0~ then (if x < 0.0~ then -1.0~ else 1.0~)
        else
            let e = exp~N~ (a + a)
            let t = (e - 1.0~) / (e + 1.0~)
            if x < 0.0~ then -t else t
// atan by halving twice — atan y = 2 atan (y / (1 + sqrt (1 + y*y))) — which
// brings the argument under 0.2 before the series, where it converges fast
let atan~N~ x =
    if x <> x then x
    else
        let a = if x < 0.0~ then -x else x
        let big = a > 1.0~
        let y = if big then 1.0~ / a else a
        let y1 = y / (1.0~ + sqrt (1.0~ + y * y))
        let y2 = y1 / (1.0~ + sqrt (1.0~ + y1 * y1))
        let q = y2 * y2
        let s =
            y2 * (1.0~ - q * (0.3333333333333333~ - q * (0.2~ - q * (0.14285714285714285~
                - q * (0.1111111111111111~ - q * (0.09090909090909091~
                - q * (0.07692307692307693~ - q * (0.06666666666666667~
                - q * (0.058823529411764705~ - q * (0.05263157894736842~
                - q * 0.047619047619047616~)))))))))
        let r = 4.0~ * s
        let m = if big then 1.5707963267948966~ - r else r
        if x < 0.0~ then -m else m
let asin~N~ x =
    if x <> x then x
    elif x >= 1.0~ then 1.5707963267948966~
    elif x <= -1.0~ then -1.5707963267948966~
    else atan~N~ (x / sqrt (1.0~ - x * x))
let atan2~N~ y x =
    if x > 0.0~ then atan~N~ (y / x)
    elif x < 0.0~ then
        if y >= 0.0~ then atan~N~ (y / x) + 3.141592653589793~
        else atan~N~ (y / x) - 3.141592653589793~
    elif y > 0.0~ then 1.5707963267948966~
    elif y < 0.0~ then -1.5707963267948966~
    else 0.0~
instance Floating<~T~>
    static exp x = exp~N~ x
    static log x = log~N~ x
    static sin x = sin~N~ x
    static cos x = cos~N~ x
    static tan x = sin~N~ x / cos~N~ x
    static sinh x = sinh~N~ x
    static cosh x = cosh~N~ x
    static tanh x = tanh~N~ x
    static asin x = asin~N~ x
    static acos x = 1.5707963267948966~ - asin~N~ x
    static atan x = atan~N~ x
    static atan2 y x = atan2~N~ y x
    static pow a b = pow~N~ a b
instance Rem<~T~, ~T~>
    type Result = ~T~
    static (%) a b = a - b * truncate (a / b)
"""

    /// `~T~` is the type, `~N~` the helper-name suffix, and a bare `~` the
    /// literal suffix. Order matters: the named markers go first.
    let private floatingInstance (t : string) (nameSuffix : string) (litSuffix : string) : string list =
        floatingSource.Replace("~T~", t).Replace("~N~", nameSuffix).Replace("~", litSuffix).Split '\n'
        |> Array.toList
        |> List.filter (fun l -> l.Trim() <> "")

    /// The primitive instances. They bind their associated type and stop
    /// there: the backend emits these as machine instructions, so there is
    /// no body to write. Only the prelude may declare an instance this way.
    let private numericInstances =
        // (type, zero literal, one literal, has a remainder operation)
        let numerics =
            [ "int", "0", "1", true
              "int64", "0L", "1L", true
              "uint32", "0u", "1u", true
              "float", "0.0", "1.0", false
              "float32", "0.0f", "1.0f", false ]
        List.concat [
            // string concatenation is `+` like any other addition
            [ "instance Add<string, string>"
              "    type Result = string" ]
            numerics |> List.collect (fun (t, zero, one, hasRem) ->
                List.concat [
                    [ "Add"; "Sub"; "Mul"; "Div" ] @ (if hasRem then [ "Rem" ] else [])
                    |> List.collect (fun cls ->
                        [ "instance " + cls + "<" + t + ", " + t + ">"
                          "    type Result = " + t ])
                    [ "instance Num<" + t + ">"
                      "    static Zero = " + zero
                      "    static One = " + one ]
                    (if hasRem then [ "instance Integral<" + t + ">" ]
                     else [ "instance Fractional<" + t + ">" ])
                    [ "instance Ordered<" + t + ">" ]
                    // F# has no unary minus on an unsigned type
                    (if t = "uint32" then [] else [ "instance Neg<" + t + ">" ])
                    (if t = "uint32" then [] else [ "instance Abs<" + t + ">" ])
                    // min/max are written out rather than generated: they are
                    // the definition F# uses, and they must NOT go through
                    // Ordered, so that a componentwise instance stays possible
                    [ "instance MinMax<" + t + ">"
                      "    static min a b = if a < b then a else b"
                      "    static max a b = if a > b then a else b" ]
                ])
            // strings and chars order, they just do not do arithmetic
            [ "instance Ordered<string>"
              "instance Ordered<char>"
              "instance MinMax<string>"
              "    static min a b = if a < b then a else b"
              "    static max a b = if a > b then a else b"
              "instance MinMax<char>"
              "    static min a b = if a < b then a else b"
              "    static max a b = if a > b then a else b" ]
            // the transcendentals, and the float remainder they need
            floatingInstance "float" "F" ""
            floatingInstance "float32" "F32" "f"
            // float16: every operation widens to f32, works there and rounds
            // back once, which is the correctly-rounded half. The backend
            // supplies the arithmetic; the transcendentals borrow float32's.
            [ "instance Add<float16, float16>"
              "    type Result = float16"
              "instance Sub<float16, float16>"
              "    type Result = float16"
              "instance Mul<float16, float16>"
              "    type Result = float16"
              "instance Div<float16, float16>"
              "    type Result = float16"
              "instance Rem<float16, float16>"
              "    type Result = float16"
              "    static (%) a b = a - b * truncate (a / b)"
              "instance Ordered<float16>"
              "instance Neg<float16>"
              "instance Abs<float16>"
              "instance MinMax<float16>"
              "    static min a b = if a < b then a else b"
              "    static max a b = if a > b then a else b"
              "instance Num<float16>"
              "    static Zero = 0.0h"
              "    static One = 1.0h"
              "instance Fractional<float16>"
              "instance Floating<float16>"
              "    static exp x = float16 (exp (float32 x))"
              "    static log x = float16 (log (float32 x))"
              "    static sin x = float16 (sin (float32 x))"
              "    static cos x = float16 (cos (float32 x))"
              "    static tan x = float16 (tan (float32 x))"
              "    static sinh x = float16 (sinh (float32 x))"
              "    static cosh x = float16 (cosh (float32 x))"
              "    static tanh x = float16 (tanh (float32 x))"
              "    static asin x = float16 (asin (float32 x))"
              "    static acos x = float16 (acos (float32 x))"
              "    static atan x = float16 (atan (float32 x))"
              "    static atan2 y x = float16 (atan2 (float32 y) (float32 x))"
              "    static pow a b = float16 (pow (float32 a) (float32 b))" ]
        ]

    let source =
        String.concat "\n" (numericClasses @ numericInstances @ [
            "type Option<'a> ="
            "    | None"
            "    | Some of 'a"
            "type option<'a> = Option<'a>"
            "type Result<'t, 'e> ="
            "    | Ok of 't"
            "    | Error of 'e"
            "type exn ="
            "    | Failure of string"
            "    | InvalidCast of string"
            // FSharp.Core's value option
            "type ValueOption<'a> ="
            "    | ValueNone"
            "    | ValueSome of 'a"
            "type voption<'a> = ValueOption<'a>"
            // struct tuples are nothing special: they ARE these generic
            // structs, reached through `struct(a, b)` syntax
            "[<Struct>]"
            "type StructTuple2<'a, 'b> = { Item1 : 'a; Item2 : 'b }"
            "[<Struct>]"
            "type StructTuple3<'a, 'b, 'c> = { Item1 : 'a; Item2 : 'b; Item3 : 'c }"
            "[<Struct>]"
            "type StructTuple4<'a, 'b, 'c, 'd> = { Item1 : 'a; Item2 : 'b; Item3 : 'c; Item4 : 'd }"
            // the equality-comparer abstraction the hash collections take
            // as a parameter; `hash` and `=` are the structural defaults
            "type IEqualityComparer<'a> ="
            "    abstract member Equals : 'a * 'a -> bool"
            "    abstract member GetHashCode : 'a -> int"
            "type DefaultEqualityComparer<'a> ="
            "    static member Instance ="
            "        { new IEqualityComparer<'a> with"
            "            member _.Equals (a, b) = a = b"
            "            member _.GetHashCode a = hash a }"
            "module Array ="
            "    extern let create : int -> 'a -> 'a[]"
            "    extern let pin : 'a[] -> int"
            "    extern let unpin : 'a[] -> int"
            ""
        ])

    let path = Analysis.Classes.builtinPath

type ProjectResults =
    { Files : Fpp.Prelude.Dict<string, Analysis.Resolve.BindResult * Analysis.Infer.InferResult>
      Schemes : Fpp.Prelude.Dict<string, Analysis.Types.Scheme>
      /// interface name -> its methods as (name, arity), project-wide
      Interfaces : Fpp.Prelude.Dict<string, (string * int) list>
      /// derived class -> (its own type params, its base type), project-wide
      Bases : Fpp.Prelude.Dict<string, Analysis.Types.Var list * Analysis.Types.Type>
      /// "TypeName.MemberName" -> definition, project-wide
      Members : Fpp.Prelude.Dict<string, Analysis.Resolve.Definition>
      /// classes and their instances, project-wide
      Classes : Analysis.Classes.Tables
      /// the prelude's own inference result — it is source like any other
      /// file, and its bodies use the classes it declares
      BuiltinInfer : Analysis.Infer.InferResult }

type Workspace() =
    let db = Db()
    do db.SetInput "project" "" (box ([] : string list))
    do db.SetInput "libs" "" (box ([] : (string * string) list))
    let plugins = vecNew<Fpp.Core.Plugins.Plugin> ()
    let pluginErrors = vecNew<string> ()

    /// Register a compiler plugin (project config, never source annotations).
    member _.AddPlugin (p : Fpp.Core.Plugins.Plugin) : unit = vecAdd plugins p
    member _.PluginErrors : string list = vecToList pluginErrors

    /// Run the per-file plugin pipeline, linting after each stage.
    member private _.RunPerFile (decls : Fpp.Core.Ir.Decl list) : Fpp.Core.Ir.Decl list =
        let mutable cur = decls
        for p in vecToList plugins do
            let out = p.PerFile cur
            match Fpp.Core.Lint.lint out with
            | [] -> cur <- out
            | errs ->
                for e in errs |> List.truncate 3 do
                    vecAdd pluginErrors ("plugin '" + p.Name + "' produced invalid core: " + e)
        cur

    member private _.RunWholeProgram (decls : Fpp.Core.Ir.Decl list) : Fpp.Core.Ir.Decl list =
        let mutable cur = decls
        for p in vecToList plugins do
            let out = p.WholeProgram cur
            match Fpp.Core.Lint.lint out with
            | [] -> cur <- out
            | errs ->
                for e in errs |> List.truncate 3 do
                    vecAdd pluginErrors ("plugin '" + p.Name + "' (whole-program) produced invalid core: " + e)
        cur

    /// Register a fat-IR library (.fppir contents) for linking.
    member this.AddLibrary (name : string) (text : string) : unit =
        let libs = unbox<(string * string) list> (db.GetInput "libs" "")
        db.SetInput "libs" "" (box (libs @ [ name, text ]))

    member private _.Libraries : (string * string) list =
        unbox<(string * string) list> (db.GetInput "libs" "")

    member _.Db = db

    /// Set the compile order explicitly (CLI: argument order).
    member _.SetProjectFiles (paths : string list) : unit =
        db.SetInput "project" "" (box paths)

    member _.ProjectFiles : string list =
        unbox<string list> (db.GetInput "project" "")

    /// Load a `*.fppproj`: its sources become the compile order, its
    /// libraries are linked. Files already open in the editor keep the text
    /// the editor has — an unsaved buffer is the truth, not the file on disk.
    /// Returns the project and any errors in the manifest itself.
    member this.LoadProject (projectPath : string) : Project.Project * (int * string) list =
        let r = Project.read projectPath
        let open_ = this.ProjectFiles |> Set.ofList
        for l in r.Loaded.Libs do
            if System.IO.File.Exists l then this.AddLibrary l (System.IO.File.ReadAllText l)
        db.SetInput "project" "" (box r.Loaded.Sources)
        for s in r.Loaded.Sources do
            if not (Set.contains s open_) then
                let text = if System.IO.File.Exists s then System.IO.File.ReadAllText s else ""
                db.SetInput "text" s (box text)
        r.Loaded, r.Errors

    member this.SetFileText (path : string) (text : string) : unit =
        // unknown files join the project in arrival order (LSP didOpen)
        let files = this.ProjectFiles
        if not (List.contains path files) then
            db.SetInput "project" "" (box (files @ [ path ]))
        db.SetInput "text" path (box text)

    member _.FileText (path : string) : string =
        unbox<string> (db.GetInput "text" path)

    member this.ParseFile (path : string) : Parser.ParseResult =
        db.MemoT "parse" path (fun () -> Parser.parse (this.FileText path))

    /// Whole-project resolution + inference in compile order. Exports and
    /// generalized schemes of earlier files flow into later ones.
    member this.ProjectCheck () : ProjectResults =
        db.MemoT "projectCheck" "" (fun () ->
            let imports = dictNew<string, Analysis.Resolve.Definition> ()
            let schemes = dictNew<string, Analysis.Types.Scheme> ()
            let aliases = dictNew<string, Analysis.Types.Var list * Analysis.Types.Type> ()
            let fields = dictNew<string, Analysis.Infer.FieldInfo> ()
            let ifaces = dictNew<string, (string * int) list> ()
            let bases = dictNew<string, Analysis.Types.Var list * Analysis.Types.Type> ()
            let impls = dictNew<string, string list> ()
            let structTypes = dictNew<string, bool> ()
            let ctors = dictNew<string, (int * Analysis.Types.Scheme) list> ()
            // classes and instances are project-wide: the prelude declares
            // the numeric tower, every later file may extend it
            let classes = Analysis.Classes.newTables ()
            // members are looked up by "Type.Member" across the whole
            // project, not just the file that declares them
            let members = dictNew<string, Analysis.Resolve.Definition> ()
            let results = dictNew<string, Analysis.Resolve.BindResult * Analysis.Infer.InferResult> ()
            // the builtin prelude seeds imports and schemes for every file
            let bp = Parser.parse Builtin.source
            let bb = Analysis.Resolve.resolve Builtin.path imports bp.Root
            for full, d in bb.Exports do dictSet imports full d
            for k, d in bb.Members do dictSet members k d
            let binf =
                Analysis.Infer.infer Builtin.path bp.Root bb schemes aliases fields ifaces bases impls structTypes ctors classes
            // linked libraries: exports feed the resolver, schemes feed inference
            for _, text in this.Libraries do
                let exps, schs, _ = Fpp.Core.Serialize.decodeLib text
                for full, d in exps do dictSet imports full d
                for k, sch in schs do dictSet schemes k sch
            for path in this.ProjectFiles do
                let p = this.ParseFile path
                let b = Analysis.Resolve.resolve path imports p.Root
                for full, d in b.Exports do dictSet imports full d
                for k, d in b.Members do dictSet members k d
                let inf = Analysis.Infer.infer path p.Root b schemes aliases fields ifaces bases impls structTypes ctors classes
                dictSet results path (b, inf)
            // libraries declare their interfaces in their serialized core
            for _, text in this.Libraries do
                let _, _, ds = Fpp.Core.Serialize.decodeLib text
                for d in ds do
                    match d with
                    | Fpp.Core.Ir.DInterface (n, ms) -> dictSet ifaces n ms
                    | Fpp.Core.Ir.DClass (n, bse, _, cimpls) ->
                        (match bse with
                         | Some b -> dictSet bases n ([], Analysis.Types.TCon (b, []))
                         | None -> ())
                        dictSet impls n (cimpls |> List.map fst)
                    | _ -> ()
            { Files = results; Schemes = schemes; Interfaces = ifaces; Bases = bases
              Members = members; Classes = classes; BuiltinInfer = binf })

    member this.TypeCheck (path : string) : Analysis.Infer.InferResult =
        match dictTryFind (this.ProjectCheck ()).Files path with
        | Some (_, i) -> i
        | None ->
            Analysis.Infer.infer path (this.ParseFile path).Root (this.Resolve path)
                (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ()) (dictNew ())
                (Analysis.Classes.newTables ())

    member this.Diagnostics (path : string) : DiagnosticInfo list =
        db.MemoT "diagnostics" path (fun () ->
            let r = this.ParseFile path
            let t = this.TypeCheck path
            let starts = Lines.starts (this.FileText path)
            let at (offset : int) (msg : string) =
                let line, col = Lines.toLineCol starts offset
                { Path = path; Line = line; Col = col
                  EndLine = line; EndCol = col + 1; Message = msg }
            (r.Diagnostics |> List.map (fun d -> at d.Offset d.Message))
            @ (t.Diagnostics |> List.map (fun (off, msg) -> at off msg))
            |> List.sortBy (fun d -> d.Line, d.Col))

    member this.Outline (path : string) : OutlineItem list =
        db.MemoT "outline" path (fun () ->
            let r = this.ParseFile path
            let starts = Lines.starts (this.FileText path)
            Outline.items starts r.Root.Children)

    member this.Resolve (path : string) : Analysis.Resolve.BindResult =
        match dictTryFind (this.ProjectCheck ()).Files path with
        | Some (b, _) -> b
        | None -> Analysis.Resolve.resolve path (dictNew ()) (this.ParseFile path).Root

    /// Lower the whole project (builtin first, then files in compile order)
    /// and emit a wasm module. Returns (wat, all errors incl. diagnostics).
    member this.EmitProgram () : string * string list =
        let r = this.ProjectCheck ()
        let errs = vecNew<string> ()
        let allDecls = vecNew<Fpp.Core.Ir.Decl> ()
        let lowerOne (path : string) (root : Syntax.GreenNode) =
            match dictTryFind r.Files path with
            | Some (b, inf) ->
                let ok = dictNew<int, string> ()
                for off, k in inf.OpKinds do dictSet ok off k
                let ak = dictNew<int, string> ()
                for off, k in inf.ArrKinds do dictSet ak off k
                let ik = dictNew<int, string list> ()
                for off, i in inf.InstSites do dictSet ik off i
                let ms = dictNew<int, string> ()
                for off, o in inf.MemberSites do dictSet ms off o
                let fo = dictNew<int, string> ()
                for off, o in inf.FieldOwners do dictSet fo off o
                let cs = dictNew<int, int> ()
                for off, o in inf.CtorSites do dictSet cs off o
                let cu = dictNew<int, Analysis.Classes.InstMember> ()
                for off, m in inf.ClassUses do dictSet cu off m
                let cp = dictNew<int, string> ()
                for off, t in inf.ClassPending do dictSet cp off t
                let ot = dictNew<int, string> ()
                for off, t in inf.OpTypes do dictSet ot off t
                let low = Fpp.Core.Lower.lower path root b r.Schemes ok ak ik ms fo cs r.Members r.Interfaces cu cp ot
                for d in this.RunPerFile low.Decls do vecAdd allDecls d
                for off, why in low.Notes do
                    vecAdd errs (path + ": not lowerable at offset " + string off + ": " + why)
            | None -> ()
        for path in this.ProjectFiles do
            for d in this.Diagnostics path do
                vecAdd errs (path + ":" + string (d.Line + 1) + ":" + string (d.Col + 1) + ": " + d.Message)
        // builtin decls (Option etc.) come first
        let bp = Parser.parse Builtin.source
        let bb = Analysis.Resolve.resolve Builtin.path (dictNew ()) bp.Root
        // the prelude is source like any other file: its own bodies call the
        // class members it declares, so it needs its own tables
        let bi = r.BuiltinInfer
        let bok = dictNew<int, string> ()
        for k, v in bi.OpKinds do dictSet bok k v
        let bak = dictNew<int, string> ()
        for k, v in bi.ArrKinds do dictSet bak k v
        let bik = dictNew<int, string list> ()
        for k, v in bi.InstSites do dictSet bik k v
        let bms = dictNew<int, string> ()
        for k, v in bi.MemberSites do dictSet bms k v
        let bfo = dictNew<int, string> ()
        for k, v in bi.FieldOwners do dictSet bfo k v
        let bcs = dictNew<int, int> ()
        for k, v in bi.CtorSites do dictSet bcs k v
        let bcu = dictNew<int, Analysis.Classes.InstMember> ()
        for k, v in bi.ClassUses do dictSet bcu k v
        let bcp = dictNew<int, string> ()
        for k, v in bi.ClassPending do dictSet bcp k v
        let bot = dictNew<int, string> ()
        for k, v in bi.OpTypes do dictSet bot k v
        let blow =
            Fpp.Core.Lower.lower Builtin.path bp.Root bb r.Schemes bok bak bik bms bfo bcs
                r.Members r.Interfaces bcu bcp bot
        for d in blow.Decls do vecAdd allDecls d
        // one function per primitive instance member, so `Add.(+)` denotes
        // something callable even where `a + b` is a machine instruction
        for d in Fpp.Core.Link.builtinInstanceWrappers r.Classes do vecAdd allDecls d
        for path in this.ProjectFiles do
            lowerOne path (this.ParseFile path).Root
        // linked library declarations join the program before emission
        let libDecls = vecNew<Fpp.Core.Ir.Decl> ()
        for _, text in this.Libraries do
            let _, _, ds = Fpp.Core.Serialize.decodeLib text
            for d in ds do vecAdd libDecls d
        for pe in this.PluginErrors do vecAdd errs pe
        if vecLen errs > 0 then "", vecToList errs
        else
            let program = this.RunWholeProgram (vecToList libDecls @ vecToList allDecls)
            // tier-1: stamp per struct instantiation, share one body for
            // reference instantiations, error on anything unclassifiable
            let structNames =
                program
                |> List.choose (fun d ->
                    match d with
                    | Fpp.Core.Ir.DRecord (n, _, _, true) -> Some n
                    | _ -> None)
            let isStruct (n : string) = List.contains n structNames
            // an instance member is the operator's implementation once
            // stamping has made the operand type concrete
            let instanceFns = Fpp.Core.Link.instanceFunctions r.Classes
            let mono0, monoErrs = Fpp.Core.Link.monomorphizeWith isStruct instanceFns program
            // stamped clones have concrete instantiations, so record layouts
            // can only be settled once monomorphization has run
            let mono = Fpp.Core.Link.stampRecords mono0
            let linked = Fpp.Core.Link.deadCodeEliminate mono
            if not (List.isEmpty monoErrs) then "", monoErrs
            else
                let res = Fpp.Backend.EmitWasm.emit linked
                res.Wat, res.Errors

    /// Produce a fat-IR library from the current project files.
    member this.BuildLibrary () : string * string list =
        let r = this.ProjectCheck ()
        let errs = vecNew<string> ()
        let decls = vecNew<Fpp.Core.Ir.Decl> ()
        let exports = vecNew<string * Analysis.Resolve.Definition> ()
        for path in this.ProjectFiles do
            for d in this.Diagnostics path do
                vecAdd errs (path + ": " + d.Message)
            match dictTryFind r.Files path with
            | Some (b, inf) ->
                for e in b.Exports do vecAdd exports e
                let ok = dictNew<int, string> ()
                for off, k in inf.OpKinds do dictSet ok off k
                let ak = dictNew<int, string> ()
                for off, k in inf.ArrKinds do dictSet ak off k
                let ik = dictNew<int, string list> ()
                for off, i in inf.InstSites do dictSet ik off i
                let ms = dictNew<int, string> ()
                for off, o in inf.MemberSites do dictSet ms off o
                let fo = dictNew<int, string> ()
                for off, o in inf.FieldOwners do dictSet fo off o
                let cs = dictNew<int, int> ()
                for off, o in inf.CtorSites do dictSet cs off o
                let cu = dictNew<int, Analysis.Classes.InstMember> ()
                for off, m in inf.ClassUses do dictSet cu off m
                let cp = dictNew<int, string> ()
                for off, t in inf.ClassPending do dictSet cp off t
                let ot = dictNew<int, string> ()
                for off, t in inf.OpTypes do dictSet ot off t
                let low = Fpp.Core.Lower.lower path (this.ParseFile path).Root b r.Schemes ok ak ik ms fo cs r.Members r.Interfaces cu cp ot
                for d in low.Decls do vecAdd decls d
            | None -> ()
        let schemes =
            dictPairs r.Schemes
            |> List.filter (fun (k, _) -> not (k.StartsWith "(builtin)"))
        for pe in this.PluginErrors do vecAdd errs pe
        if vecLen errs > 0 then "", vecToList errs
        else Fpp.Core.Serialize.encodeLib (vecToList exports) schemes (vecToList decls), []

    /// Lower a file to typed core (Stage 3). Runs on top of the project check.
    member this.LowerFile (path : string) : Core.Ir.LowerResult =
        let r = this.ProjectCheck ()
        match dictTryFind r.Files path with
        | Some (b, inf) ->
            let ok = dictNew<int, string> ()
            for off, k in inf.OpKinds do dictSet ok off k
            let ak = dictNew<int, string> ()
            for off, k in inf.ArrKinds do dictSet ak off k
            let ik = dictNew<int, string list> ()
            for off, i in inf.InstSites do dictSet ik off i
            let ms = dictNew<int, string> ()
            for off, o in inf.MemberSites do dictSet ms off o
            let fo = dictNew<int, string> ()
            for off, o in inf.FieldOwners do dictSet fo off o
            let cs = dictNew<int, int> ()
            for off, o in inf.CtorSites do dictSet cs off o
            let cu = dictNew<int, Analysis.Classes.InstMember> ()
            for off, m in inf.ClassUses do dictSet cu off m
            let cp = dictNew<int, string> ()
            for off, t in inf.ClassPending do dictSet cp off t
            let ot = dictNew<int, string> ()
            for off, t in inf.OpTypes do dictSet ot off t
            Core.Lower.lower path (this.ParseFile path).Root b r.Schemes ok ak ik ms fo cs r.Members r.Interfaces cu cp ot
        | None -> { Decls = []; Notes = [] }

    /// Definition for the name whose use (or definition) covers the offset.
    member this.DefinitionAt (path : string) (offset : int) : Analysis.Resolve.Definition option =
        let r = this.Resolve path
        let atUse =
            r.Resolutions
            |> List.tryFind (fun u -> offset >= u.UseOffset && offset < u.UseOffset + u.UseLength)
            |> Option.map (fun u -> u.Def)
        match atUse with
        | Some d -> Some d
        | None ->
            r.Definitions
            |> List.tryFind (fun d -> offset >= d.Offset && offset < d.Offset + d.Length)

    member this.HoverAt (path : string) (offset : int) : string option =
        this.DefinitionAt path offset
        |> Option.map (fun d ->
            let basis = Analysis.Resolve.kindLabel d.Kind + " `" + d.Name + "`"
            // the generalized scheme is the better answer where there is one:
            // it carries the class context, which is most of what a reader
            // needs from a signature in this language. It also works when the
            // definition lives in ANOTHER file, where this file's DefTypes
            // has nothing to say.
            let scheme =
                dictTryFind (this.ProjectCheck ()).Schemes (d.Path + ":" + string d.Offset)
            match scheme with
            | Some sch -> basis + " : " + Analysis.Types.schemeString sch
            | None ->
                match (this.TypeCheck d.Path).DefTypes |> List.tryFind (fun (off, _, _) -> off = d.Offset) with
                | Some (_, _, ts) -> basis + " : " + ts
                | None -> basis)
