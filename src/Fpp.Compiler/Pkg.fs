module Fpp.Pkg

open Fpp.Prelude

// Packages: semantic versions, version ranges, and the solver that picks
// one version per package name. Pure — the CLI owns every byte of IO
// (registries, the cache, archives); this module answers questions.
//
// A version is semver 2.0: major.minor.patch, optionally -prerelease.
// Build metadata (+...) is accepted and ignored, as the spec orders it to
// be. A range is one of:
//
//   *                any release
//   1.2.3            exactly that version
//   ^1.2.3           compatible: >=1.2.3 <2.0.0  (the DEFAULT reading:
//                    a bare `1.2` in a manifest means ^1.2)
//   ~1.2.3           close: >=1.2.3 <1.3.0
//   >=1.2 <2 ...     a space-separated conjunction of comparators
//
// Prerelease versions are only ever picked when a comparator NAMES a
// prerelease of the same numeric triple — `^1.0.0-rc.1` admits 1.0.0-rc.2,
// a plain `^1.0.0` never picks 1.1.0-beta. That is npm's rule, and it is
// the one that keeps a prerelease from leaking into an unsuspecting solve.

// ---- versions -------------------------------------------------------------

type Version =
    { Major : int
      Minor : int
      Patch : int
      /// dot-separated prerelease identifiers; [] = a release
      Pre : string list }

let versionString (v : Version) : string =
    string v.Major + "." + string v.Minor + "." + string v.Patch
    + (if List.isEmpty v.Pre then "" else "-" + String.concat "." v.Pre)

let private allDigits (s : string) : bool =
    strLen s > 0
    && (let mutable ok = true
        for c in s do
            if not (c >= '0' && c <= '9') then ok <- false
        ok)

/// Parse `1.2.3`, `1.2.3-rc.1`, `1.2.3+meta`. Missing minor/patch are 0 —
/// `1.2` IS 1.2.0 — so a range shorthand and a full version read the same
/// way. None when it is not a version at all.
let parseVersion (s : string) : Version option =
    let s = s.Trim ()
    // strip build metadata: ordered to be ignored
    let s = (match s.IndexOf "+" with i when i >= 0 -> s.Substring (0, i) | _ -> s)
    let core, pre =
        match s.IndexOf "-" with
        | i when i >= 0 -> s.Substring (0, i), s.Substring (i + 1)
        | _ -> s, ""
    let parts = core.Split '.' |> Array.toList
    let nums = parts |> List.map (fun p -> if allDigits p then Some (int p) else None)
    match nums with
    | [ Some a ] -> Some { Major = a; Minor = 0; Patch = 0; Pre = (if pre = "" then [] else pre.Split '.' |> Array.toList) }
    | [ Some a; Some b ] -> Some { Major = a; Minor = b; Patch = 0; Pre = (if pre = "" then [] else pre.Split '.' |> Array.toList) }
    | [ Some a; Some b; Some c ] -> Some { Major = a; Minor = b; Patch = c; Pre = (if pre = "" then [] else pre.Split '.' |> Array.toList) }
    | _ -> None

/// semver ordering. A release outranks every prerelease of its triple;
/// prerelease identifiers compare numerically when both are numeric,
/// lexically otherwise, numeric below alphanumeric — the spec's rules.
let compareVersion (a : Version) (b : Version) : int =
    if a.Major <> b.Major then compare a.Major b.Major
    elif a.Minor <> b.Minor then compare a.Minor b.Minor
    elif a.Patch <> b.Patch then compare a.Patch b.Patch
    else
        match a.Pre, b.Pre with
        | [], [] -> 0
        | [], _ -> 1
        | _, [] -> -1
        | pa, pb ->
            let rec go (xs : string list) (ys : string list) : int =
                match xs, ys with
                | [], [] -> 0
                | [], _ -> -1        // shorter prerelease is smaller
                | _, [] -> 1
                | x :: xr, y :: yr ->
                    let c =
                        match allDigits x, allDigits y with
                        | true, true -> compare (int x) (int y)
                        | true, false -> -1
                        | false, true -> 1
                        | false, false -> compare x y
                    if c <> 0 then c else go xr yr
            go pa pb

// ---- ranges ---------------------------------------------------------------

type Cmp =
    { Op : string          // ">=", ">", "<=", "<", "="
      V : Version }

type Range =
    { /// the source text, for messages
      Text : string
      /// comparator conjunction; [] with Any=true is `*`
      Cmps : Cmp list
      Any : bool
      /// the numeric triples whose prereleases the range explicitly named
      PreSeats : (int * int * int) list }
    member r.String = r.Text

let private caret (v : Version) : Cmp list =
    // ^0.2.3 is >=0.2.3 <0.3.0 and ^0.0.3 is >=0.0.3 <0.0.4: the leftmost
    // NONZERO number is the compatibility wall, as npm reads it
    let upper =
        if v.Major > 0 then { Major = v.Major + 1; Minor = 0; Patch = 0; Pre = [] }
        elif v.Minor > 0 then { Major = 0; Minor = v.Minor + 1; Patch = 0; Pre = [] }
        else { Major = 0; Minor = 0; Patch = v.Patch + 1; Pre = [] }
    [ { Op = ">="; V = v }; { Op = "<"; V = upper } ]

let private tilde (v : Version) : Cmp list =
    [ { Op = ">="; V = v }
      { Op = "<"; V = { Major = v.Major; Minor = v.Minor + 1; Patch = 0; Pre = [] } } ]

/// Parse a range. A bare version is CARET — `1.2` in a manifest means
/// "1.2 and compatible" — because that is what a dependency edge almost
/// always intends; write `=1.2.3` for exactly one version.
let parseRange (s : string) : Range option =
    let text = s.Trim ()
    if text = "" || text = "*" then
        Some { Text = (if text = "" then "*" else text); Cmps = []; Any = true; PreSeats = [] }
    else
        let parts = text.Split ' ' |> Array.toList |> List.filter (fun p -> p <> "")
        let cmps = vecNew<Cmp> ()
        let seats = vecNew<int * int * int> ()
        let mutable ok = true
        for p in parts do
            let op, rest =
                if p.StartsWith ">=" then ">=", p.Substring 2
                elif p.StartsWith "<=" then "<=", p.Substring 2
                elif p.StartsWith ">" then ">", p.Substring 1
                elif p.StartsWith "<" then "<", p.Substring 1
                elif p.StartsWith "=" then "=", p.Substring 1
                elif p.StartsWith "^" then "^", p.Substring 1
                elif p.StartsWith "~" then "~", p.Substring 1
                else "^", p
            match parseVersion rest with
            | None -> ok <- false
            | Some v ->
                if not (List.isEmpty v.Pre) then vecAdd seats (v.Major, v.Minor, v.Patch)
                match op with
                | "^" -> for c in caret v do vecAdd cmps c
                | "~" -> for c in tilde v do vecAdd cmps c
                | o -> vecAdd cmps { Op = o; V = v }
        if ok && vecLen cmps > 0 then
            Some { Text = text; Cmps = vecToList cmps; Any = false; PreSeats = vecToList seats }
        else None

let satisfies (r : Range) (v : Version) : bool =
    // a prerelease only enters where the range NAMED a prerelease of the
    // same triple; releases are always fair game
    if not (List.isEmpty v.Pre)
       && not (r.PreSeats |> List.exists (fun (a, b, c) -> a = v.Major && b = v.Minor && c = v.Patch)) then false
    elif r.Any then true
    else
        r.Cmps
        |> List.forall (fun c ->
            let d = compareVersion v c.V
            match c.Op with
            | ">=" -> d >= 0
            | ">" -> d > 0
            | "<=" -> d <= 0
            | "<" -> d < 0
            | _ -> d = 0)

// ---- the solver -----------------------------------------------------------

/// What the registries know: for each package name, its versions, and for
/// each version its own dependency edges. The CLI fills this from
/// downloaded indexes; the solver never does IO.
type Universe =
    { /// name -> available versions (any order)
      Versions : Dict<string, Version list>
      /// (name, version-string) -> requires edges
      Requires : Dict<string * string, (string * Range) list> }

let newUniverse () : Universe =
    { Versions = dictNew<string, Version list> ()
      Requires = dictNew<string * string, (string * Range) list> () }

type Solution =
    { /// dependency-ordered: a package comes AFTER everything it requires,
      /// which is the link order fppir libraries need
      Picks : (string * Version) list }

/// Pick one version per reachable package so every edge is satisfied.
/// Newest-first with backtracking: the greedy pick is almost always the
/// answer, and when it is not, the search retreats to the youngest choice
/// with an alternative left. Deterministic. On failure the error names the
/// package and every constraint that boxed it in.
let solve (u : Universe) (roots : (string * Range) list) : Result<Solution, string> =
    // constraints per name accumulate as picks are made; each entry
    // remembers who asked, for the error message
    let mutable picked : (string * Version) list = []
    let mutable failure = ""
    let candidatesFor (name : string) (wanted : (string * Range) list) : Version list =
        match dictTryFind u.Versions name with
        | None -> []
        | Some vs ->
            vs
            |> List.filter (fun v -> wanted |> List.forall (fun (_, r) -> satisfies r v))
            |> List.sortWith (fun a b -> compareVersion b a)
    // all constraints on `name` visible from the current pick set + roots
    let constraintsOn (name : string) : (string * Range) list =
        let fromRoots =
            roots |> List.filter (fun (n, _) -> n = name) |> List.map (fun (_, r) -> "(project)", r)
        let fromPicks =
            picked
            |> List.collect (fun (pn, pv) ->
                match dictTryFind u.Requires (pn, versionString pv) with
                | Some es -> es |> List.filter (fun (n, _) -> n = name) |> List.map (fun (_, r) -> pn + " " + versionString pv, r)
                | None -> [])
        fromRoots @ fromPicks
    // the frontier: names demanded but not yet picked, oldest demand first
    // (deterministic order)
    let rec unpicked () : string option =
        let demanded =
            (roots |> List.map (fun (n, _) -> n))
            @ (picked
               |> List.collect (fun (pn, pv) ->
                   match dictTryFind u.Requires (pn, versionString pv) with
                   | Some es -> es |> List.map (fun (n, _) -> n)
                   | None -> []))
        demanded |> List.tryFind (fun n -> not (picked |> List.exists (fun (pn, _) -> pn = n)))
    // a pick can also INVALIDATE earlier picks (a new edge constrains a
    // name already chosen); check the whole set every time — the sets are
    // small, and correct beats clever here
    let consistent () : bool =
        picked
        |> List.forall (fun (n, v) -> constraintsOn n |> List.forall (fun (_, r) -> satisfies r v))
    let rec go () : bool =
        match unpicked () with
        | None -> true
        | Some name ->
            let wanted = constraintsOn name
            let cands = candidatesFor name wanted
            if List.isEmpty cands then
                failure <-
                    "no version of " + name + " satisfies: "
                    + String.concat ", " (wanted |> List.map (fun (who, r) -> r.String + " (wanted by " + who + ")"))
                    + (match dictTryFind u.Versions name with
                       | None -> " — the registries know no such package"
                       | Some vs -> " — available: " + String.concat ", " (vs |> List.sortWith compareVersion |> List.map versionString))
                false
            else
                let mutable done_ = false
                let mutable rest = cands
                while not done_ && not (List.isEmpty rest) do
                    let v = List.head rest
                    rest <- List.tail rest
                    picked <- picked @ [ name, v ]
                    if consistent () && go () then done_ <- true
                    else picked <- picked |> List.filter (fun (n, _) -> n <> name)
                done_
    if go () then
        // topological order: requires before requirers. Cycles cannot
        // happen (a package cannot depend on itself through any chain the
        // registry would have accepted), but the sort refuses to spin
        // regardless.
        let out = vecNew<string * Version> ()
        let emitted = dictNew<string, bool> ()
        let rec emit (name : string) (v : Version) (fuel : int) : unit =
            if fuel > 0 && not (dictTryFind emitted name).IsSome then
                dictSet emitted name true
                (match dictTryFind u.Requires (name, versionString v) with
                 | Some es ->
                     for dn, _ in es do
                         (match picked |> List.tryFind (fun (n, _) -> n = dn) with
                          | Some (_, dv) -> emit dn dv (fuel - 1)
                          | None -> ())
                 | None -> ())
                vecAdd out (name, v)
        for n, v in picked do emit n v 1000
        Ok { Picks = vecToList out }
    else Error failure

// ---- the package manifest -------------------------------------------------

/// What an `.fpkg` archive's `fpkg` manifest says. The same line format a
/// project file uses: one directive per line, nothing clever.
///
///   name foo
///   version 1.2.3
///   requires bar ^1.0
///   lib wasm foo-wasm.fppir
///   lib native foo-native.fppir
type PkgManifest =
    { Name : string
      Version : Version
      Requires : (string * Range) list
      /// flavor ("wasm" | "native") -> archive-relative fppir file
      Libs : (string * string) list }

let parseManifest (text : string) : Result<PkgManifest, string> =
    let mutable name = ""
    let mutable version = None
    let requires = vecNew<string * Range> ()
    let libs = vecNew<string * string> ()
    let mutable err = ""
    let lines = text.Replace("\r\n", "\n").Split '\n'
    for raw in lines do
        let line = raw.Trim ()
        if line = "" || line.StartsWith "#" then ()
        else
            let parts = line.Split ' ' |> Array.toList |> List.filter (fun p -> p <> "")
            match parts with
            | [ "name"; n ] -> name <- n
            | [ "version"; v ] ->
                (match parseVersion v with
                 | Some pv -> version <- Some pv
                 | None -> err <- "bad version: " + v)
            | "requires" :: n :: rest ->
                (match parseRange (String.concat " " rest) with
                 | Some r -> vecAdd requires (n, r)
                 | None -> err <- "bad range on requires " + n + ": " + String.concat " " rest)
            | [ "lib"; flavor; file ] -> vecAdd libs (flavor, file)
            | _ -> err <- "unknown manifest line: " + line
    if err <> "" then Error err
    elif name = "" then Error "manifest names no package (missing `name`)"
    else
        match version with
        | None -> Error "manifest carries no version (missing `version`)"
        | Some v -> Ok { Name = name; Version = v; Requires = vecToList requires; Libs = vecToList libs }

let manifestText (m : PkgManifest) : string =
    String.concat "\n"
        ([ "name " + m.Name; "version " + versionString m.Version ]
         @ (m.Requires |> List.map (fun (n, r) -> "requires " + n + " " + r.String))
         @ (m.Libs |> List.map (fun (f, p) -> "lib " + f + " " + p)))
    + "\n"
