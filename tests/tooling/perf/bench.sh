#!/usr/bin/env bash
# Every perf benchmark, in C, F++ and vanilla F#, so the F++ column has both a
# native reference and a managed one. C and F++ run as wasm under wasmtime; F#
# is fsc + .NET on the host.
#
# WARM, best of three: wasmtime caches a module's compilation on disk, so the
# first run of a fresh binary pays the whole Cranelift compile and reads 3-6x
# slower than every run after it. One cold run has been reported as a 400 ms
# "regression" before. The RESULT is printed beside the timing: a module that
# fails to build exits in milliseconds and looks like a spectacular win, and a
# twin that computes something ELSE is not a comparison at all — all three
# print the same checksum, so a mismatched column is visible.
#
# The `floor` row is an empty program in each language. .NET pays ~50 ms of
# startup that wasm does not, so subtract the floor before reading a short
# benchmark's F# column.
#
#   ./bench.sh              # every benchmark
#   ./bench.sh avl          # one
set -u
cd "$(dirname "$0")"
root=$(cd ../../.. && pwd)
out=$(mktemp -d); trap 'rm -rf "$out"' EXIT
wt="${WASMTIME:-$HOME/.wasmtime/bin/wasmtime}"
only="${1:-}"

source /opt/emsdk/emsdk_env.sh >/dev/null 2>&1

# Every twin MANAGES MEMORY. The C twins for avl and trees used to be bump
# arenas — one never freed, the other dropped a whole tree by resetting a
# pointer — and against that the collector looked 2.9x slow while measuring
# something no real program can do. They malloc/free now, with refcounts for
# avl since the tree is persistent and versions share nodes.
#
# A Go twin was tried as "a mature GC" and dropped: `GOOS=wasip1` works and
# answers correctly, but Go's wasm port runs ~10x its native speed (trees
# 8902ms against 1409), so the column measured the port, not the collector.
# For the record its NATIVE numbers against the old arena C were avl 2.51x
# and trees 4.45x — both worse than F++ manages inside a sandbox.

# one Rust crate, its single source file swapped per benchmark
rsdir="$out/rs"
mkdir -p "$rsdir/src"
cat > "$rsdir/Cargo.toml" <<'CARGO'
[package]
name = "bench"
version = "0.0.0"
edition = "2021"

[[bin]]
name = "bench"
path = "src/main.rs"

[profile.release]
opt-level = 3
lto = true
panic = "abort"
CARGO

# one F# project, its single source file swapped per benchmark
fsdir="$out/fs"
mkdir -p "$fsdir"
cat > "$fsdir/bench.fsproj" <<'EOF'
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <OutputType>Exe</OutputType>
    <TargetFramework>net10.0</TargetFramework>
    <Optimize>true</Optimize>
    <ServerGarbageCollection>false</ServerGarbageCollection>
    <ConcurrentGarbageCollection>false</ConcurrentGarbageCollection>
    <InvariantGlobalization>true</InvariantGlobalization>
    <WarningLevel>0</WarningLevel>
    <TreatWarningsAsErrors>false</TreatWarningsAsErrors>
    <NoWarn>FS0025;FS0049;FS0064;FS1182</NoWarn>
  </PropertyGroup>
  <ItemGroup><Compile Include="prog.fs" /></ItemGroup>
</Project>
EOF

# best of three, in milliseconds; echoes "<ms>|<result>"
bestof3 () {
    local best=9999999 res=""
    for _ in 1 2 3; do
        local s e ms
        s=$(date +%s%N)
        res=$("$@" 2>&1 | tail -1)
        e=$(date +%s%N)
        ms=$(( (e - s) / 1000000 ))
        [ "$ms" -lt "$best" ] && best=$ms
    done
    echo "$best|$res"
}

# run_one <name> [source dir]
run_one () {
    local b="$1" d="${2:-.}" cms="-" fms="-" nms="-" gms="-" fres="" cres="" nres="" gres=""
    local src="$d/$b"

    if [ -f "$src.c" ]; then
        emcc -O2 "$src.c" -o "$out/$b.c.wasm" -s STANDALONE_WASM -s PURE_WASI=1 \
             -s TOTAL_MEMORY=1073741824 >/dev/null 2>&1 \
            && { "$wt" run -W gc=y,exceptions=y "$out/$b.c.wasm" >/dev/null 2>&1
                 r=$(bestof3 "$wt" run -W gc=y,exceptions=y "$out/$b.c.wasm")
                 cms="${r%%|*}"; cres="${r#*|}"; }
    fi

    if [ -f "$src.fpp" ]; then
        dotnet run --no-build -c Release --project "$root/src/Fpp.Cli" -- \
            build -o "$out/$b.f.wasm" "$src.fpp" >/dev/null 2>&1 \
            && { "$wt" run -W gc=y,exceptions=y "$out/$b.f.wasm" >/dev/null 2>&1
                 r=$(bestof3 "$wt" run -W gc=y,exceptions=y "$out/$b.f.wasm")
                 fms="${r%%|*}"; fres="${r#*|}"; }
    fi

    if [ -f "$src.fs" ]; then
        cp "$src.fs" "$fsdir/prog.fs"
        rm -rf "$fsdir/obj" "$fsdir/bin"
        dotnet build -c Release -v q --nologo "$fsdir/bench.fsproj" >/dev/null 2>&1 \
            && { dotnet "$fsdir/bin/Release/net10.0/bench.dll" >/dev/null 2>&1
                 r=$(bestof3 dotnet "$fsdir/bin/Release/net10.0/bench.dll")
                 nms="${r%%|*}"; nres="${r#*|}"; }
    fi

    # Rust, to the SAME wasm target under the SAME engine. No GC, but real
    # ownership — and bounds checks ON by default, which is what makes it
    # the useful third point: C says what unchecked manual memory costs,
    # Rust says what CHECKED manual memory costs, F++ says what a collector
    # costs on top of that.
    if [ -f "$src.rs" ]; then
        cp "$src.rs" "$rsdir/src/main.rs"
        ( cd "$rsdir" && cargo build --release --quiet --target wasm32-wasip1 ) >/dev/null 2>&1 \
            && { "$wt" run -W gc=y,exceptions=y "$rsdir/target/wasm32-wasip1/release/bench.wasm" >/dev/null 2>&1
                 r=$(bestof3 "$wt" run -W gc=y,exceptions=y "$rsdir/target/wasm32-wasip1/release/bench.wasm")
                 gms="${r%%|*}"; gres="${r#*|}"; }
    fi

    local ratio="-" nratio="-" gratio="-"
    [ "$cms" != "-" ] && [ "$fms" != "-" ] && \
        ratio=$(awk -v c="$cms" -v f="$fms" 'BEGIN { if (c > 0) printf "%.2fx", f / c; else printf "-" }')
    [ "$cms" != "-" ] && [ "$nms" != "-" ] && \
        nratio=$(awk -v c="$cms" -v n="$nms" 'BEGIN { if (c > 0) printf "%.2fx", n / c; else printf "-" }')
    [ "$cms" != "-" ] && [ "$gms" != "-" ] && \
        gratio=$(awk -v c="$cms" -v g="$gms" 'BEGIN { if (c > 0) printf "%.2fx", g / c; else printf "-" }')

    # a differing checksum means the twins are not the same program
    local flag=""
    for x in "$cres" "$nres" "$gres"; do
        [ -n "$x" ] && [ -n "$fres" ] && [ "$x" != "$fres" ] && flag="  MISMATCH"
    done
    printf "%-10s %9sms %9sms %9sms %9sms %8s %8s %8s   %s%s\n" \
        "$b" "$cms" "$gms" "$fms" "$nms" "$ratio" "$gratio" "$nratio" "$fres" "$flag"
}

printf "%-10s %11s %11s %11s %11s %8s %8s %8s   %s\n" bench C Rust F++ "F#" "F++/C" "Rust/C" "F#/C" result

# the startup floor, so a short benchmark's columns can be read fairly
if [ -z "$only" ]; then
    printf 'module Floor\nlet go = print 1.0\n' > "$out/floor.fpp"
    printf '#include <stdio.h>\nint main(void){printf("1\\n");return 0;}\n' > "$out/floor.c"
    printf '[<EntryPoint>]\nlet main _ =\n    printfn "1"\n    0\n' > "$out/floor.fs"
    run_one floor "$out"
fi

for f in *.fpp; do
    b="${f%.fpp}"
    [ -n "$only" ] && [ "$b" != "$only" ] && continue
    [ -f "$b.c" ] || continue     # gpubench has no C twin
    run_one "$b"
done
