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

# The C column is an ARENA on the allocating benchmarks: avl bump-allocates
# and never frees, trees resets a pointer to drop a whole tree. That is not
# memory management, it is the floor for "what if you never reclaim", and
# reading F++ against it says nothing about the collector. `<name>.mm.c` is
# the same program written the way someone who owns the lifetimes has to
# write it — malloc/free, and REFCOUNTS where the structure is persistent
# and versions share nodes. Read F++/C-mm.
#
# A Go twin was tried here as "a mature GC" and dropped: `GOOS=wasip1` works
# and answers correctly, but Go's wasm port runs ~10x its native speed
# (trees 8902ms against 1409), so the column measured that port and not the
# collector, and running Go native against everyone else's wasm compares
# nothing. For the record, native Go on the arena ratio: avl 2.51x,
# trees 4.45x — both WORSE than F++ manages inside a sandbox.

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

    # <name>.mm.c — the same program with REAL memory management, built and
    # run exactly like the arena twin. This is the column to read F++
    # against on anything that allocates.
    if [ -f "$src.mm.c" ]; then
        emcc -O2 "$src.mm.c" -o "$out/$b.mm.wasm" -s STANDALONE_WASM -s PURE_WASI=1 \
             -s TOTAL_MEMORY=1073741824 >/dev/null 2>&1 \
            && { "$wt" run -W gc=y,exceptions=y "$out/$b.mm.wasm" >/dev/null 2>&1
                 r=$(bestof3 "$wt" run -W gc=y,exceptions=y "$out/$b.mm.wasm")
                 gms="${r%%|*}"; gres="${r#*|}"; }
    fi

    local ratio="-" nratio="-" gratio="-"
    [ "$cms" != "-" ] && [ "$fms" != "-" ] && \
        ratio=$(awk -v c="$cms" -v f="$fms" 'BEGIN { if (c > 0) printf "%.2fx", f / c; else printf "-" }')
    [ "$cms" != "-" ] && [ "$nms" != "-" ] && \
        nratio=$(awk -v c="$cms" -v n="$nms" 'BEGIN { if (c > 0) printf "%.2fx", n / c; else printf "-" }')
    # the ratio that means something on an allocating benchmark: F++ against
    # C that actually frees, not against C that never does
    [ "$gms" != "-" ] && [ "$fms" != "-" ] && \
        gratio=$(awk -v g="$gms" -v f="$fms" 'BEGIN { if (g > 0) printf "%.2fx", f / g; else printf "-" }')

    # a differing checksum means the twins are not the same program
    local flag=""
    for x in "$cres" "$nres" "$gres"; do
        [ -n "$x" ] && [ -n "$fres" ] && [ "$x" != "$fres" ] && flag="  MISMATCH"
    done
    printf "%-10s %9sms %9sms %9sms %9sms %8s %8s %8s   %s%s\n" \
        "$b" "$cms" "$gms" "$fms" "$nms" "$ratio" "$nratio" "$gratio" "$fres" "$flag"
}

printf "%-10s %11s %11s %11s %11s %8s %8s %8s   %s\n" bench C "C-mm" F++ "F#" "F++/C" "F#/C" "F++/C-mm" result

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
