module Fpp.Tests.PkgTests

open Expecto
open Fpp.Pkg
open Fpp.Prelude

let private v (s : string) = (parseVersion s).Value
let private r (s : string) = (parseRange s).Value

let private uni (pkgs : (string * string * (string * string) list) list) : Universe =
    let u = newUniverse ()
    for name, ver, reqs in pkgs do
        let existing = match dictTryFind u.Versions name with Some vs -> vs | None -> []
        dictSet u.Versions name (existing @ [ v ver ])
        dictSet u.Requires (name, ver) (reqs |> List.map (fun (n, rg) -> n, r rg))
    u

let private picksOf (sol : Result<Solution, string>) : (string * string) list =
    match sol with
    | Ok s -> s.Picks |> List.map (fun (n, pv) -> n, versionString pv)
    | Error e -> failwithf "expected a solution, got: %s" e

[<Tests>]
let tests =
    testList "packages" [
        test "semver ordering" {
            let expectLess (a : string) (b : string) =
                Expect.isTrue (compareVersion (v a) (v b) < 0) (a + " < " + b)
            expectLess "1.2.3" "1.2.4"
            expectLess "1.2.3" "1.3.0"
            expectLess "1.9.9" "2.0.0"
            expectLess "1.0.0-alpha" "1.0.0"
            expectLess "1.0.0-alpha" "1.0.0-alpha.1"
            expectLess "1.0.0-alpha.1" "1.0.0-alpha.beta"
            expectLess "1.0.0-2" "1.0.0-11"       // numeric identifiers compare numerically
            expectLess "1.0.0-11" "1.0.0-alpha"   // numeric below alphanumeric
            Expect.equal (compareVersion (v "1.2.3+build.5") (v "1.2.3")) 0 "build metadata is ignored"
        }
        test "ranges" {
            Expect.isTrue (satisfies (r "*") (v "0.0.1")) "* takes anything released"
            Expect.isTrue (satisfies (r "^1.2.3") (v "1.9.0")) "caret spans the major"
            Expect.isFalse (satisfies (r "^1.2.3") (v "2.0.0")) "caret stops at the major"
            Expect.isFalse (satisfies (r "^1.2.3") (v "1.2.2")) "caret has a floor"
            Expect.isTrue (satisfies (r "^0.2.3") (v "0.2.9")) "0.x caret spans the minor"
            Expect.isFalse (satisfies (r "^0.2.3") (v "0.3.0")) "0.x caret stops at the minor"
            Expect.isFalse (satisfies (r "^0.0.3") (v "0.0.4")) "0.0.x caret is exact-patch"
            Expect.isTrue (satisfies (r "~1.2.3") (v "1.2.9")) "tilde spans the patch"
            Expect.isFalse (satisfies (r "~1.2.3") (v "1.3.0")) "tilde stops at the minor"
            Expect.isTrue (satisfies (r "=1.2.3") (v "1.2.3")) "= is exact"
            Expect.isFalse (satisfies (r "=1.2.3") (v "1.2.4")) "= refuses the next patch"
            Expect.isTrue (satisfies (r ">=1.2 <2") (v "1.9.9")) "conjunction, inside"
            Expect.isFalse (satisfies (r ">=1.2 <2") (v "2.0.0")) "conjunction, at the wall"
            Expect.isTrue (satisfies (r "1.2") (v "1.4.0")) "a bare version reads as caret"
            Expect.isFalse (satisfies (r "*") (v "1.0.0-rc.1")) "a prerelease never leaks into *"
            Expect.isTrue (satisfies (r "^1.0.0-rc.1") (v "1.0.0-rc.2")) "a named prerelease seat admits its own triple"
            Expect.isFalse (satisfies (r "^1.0.0") (v "1.1.0-beta")) "an unnamed prerelease stays out"
        }
        test "solve picks newest and orders dependencies first" {
            let u =
                uni [ "app-base", "1.0.0", []
                      "app-base", "1.2.0", []
                      "app-mid", "2.0.0", [ "app-base", "^1.0" ] ]
            let picks = picksOf (solve u [ "app-mid", r "^2.0" ])
            Expect.equal picks [ "app-base", "1.2.0"; "app-mid", "2.0.0" ] "base first, newest of each"
        }
        test "diamond shares one pick" {
            let u =
                uni [ "d-base", "1.0.0", []
                      "d-base", "1.5.0", []
                      "d-left", "1.0.0", [ "d-base", "^1.0" ]
                      "d-right", "1.0.0", [ "d-base", "~1.0.0" ] ]
            let picks = picksOf (solve u [ "d-left", r "*"; "d-right", r "*" ])
            // ~1.0.0 caps the shared base below 1.5.0
            Expect.contains picks ("d-base", "1.0.0") "the tighter edge wins"
            Expect.equal (picks |> List.filter (fun (n, _) -> n = "d-base") |> List.length) 1 "one pick per name"
        }
        test "backtracking retreats from a greedy dead end" {
            // newest b-top (2.0) needs b-dep ^2, but the root pins b-dep ^1 —
            // the solver must fall back to b-top 1.0
            let u =
                uni [ "b-dep", "1.0.0", []
                      "b-dep", "2.0.0", []
                      "b-top", "1.0.0", [ "b-dep", "^1.0" ]
                      "b-top", "2.0.0", [ "b-dep", "^2.0" ] ]
            let picks = picksOf (solve u [ "b-top", r "*"; "b-dep", r "^1.0" ])
            Expect.contains picks ("b-top", "1.0.0") "greedy 2.0 is abandoned"
            Expect.contains picks ("b-dep", "1.0.0") "the root's pin holds"
        }
        test "a genuine conflict names its constraints" {
            let u =
                uni [ "c-dep", "1.0.0", []
                      "c-dep", "2.0.0", []
                      "c-a", "1.0.0", [ "c-dep", "^1.0" ]
                      "c-b", "1.0.0", [ "c-dep", "^2.0" ] ]
            match solve u [ "c-a", r "*"; "c-b", r "*" ] with
            | Ok s -> failwithf "expected a conflict, got %A" s.Picks
            | Error e ->
                Expect.stringContains e "c-dep" "the fought-over package is named"
                Expect.stringContains e "wanted by" "the demanders are named"
        }
        test "an unknown package says so" {
            let u = uni [ "known", "1.0.0", [] ]
            match solve u [ "unknown", r "*" ] with
            | Ok _ -> failwith "expected an error"
            | Error e -> Expect.stringContains e "no such package" "the miss is explicit"
        }
        test "manifest round-trips" {
            let m =
                { Name = "demo"
                  Version = v "1.2.3"
                  Requires = [ "base", r "^1.0"; "extra", r ">=2.1 <3" ]
                  Libs = [ "wasm", "demo-wasm.fppir"; "native", "demo-native.fppir" ] }
            match parseManifest (manifestText m) with
            | Error e -> failwith e
            | Ok m2 ->
                Expect.equal m2.Name m.Name "name"
                Expect.equal (versionString m2.Version) "1.2.3" "version"
                Expect.equal (m2.Requires |> List.map fst) [ "base"; "extra" ] "requires names"
                Expect.equal m2.Libs m.Libs "libs"
        }
    ]
