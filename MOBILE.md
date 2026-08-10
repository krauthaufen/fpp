# Mobile

The C backend is the mobile path: `fpp build -o app.c` emits a C
translation unit, and any platform C toolchain compiles it against fpprt.
Nothing about the pipeline is desktop-specific — the runtime is portable C
and a vendored GC.

## Android

Compile the generated C and fpprt with the NDK's clang. Static links avoid
shipping a runtime library:

```bash
fpp build -o app.c app.fpp

NDK=$ANDROID_SDK/ndk/<version>/toolchains/llvm/prebuilt/linux-x86_64/bin
$NDK/aarch64-linux-android24-clang -O2 -static \
    -Iruntime -Iruntime/gc/api -Iruntime/gc/src \
    -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS='"runtime/gc/api/semi-attrs.h"' \
    -DGC_EMBEDDER='"runtime/fpprt-embedder.h"' \
    app.c runtime/fpprt.c runtime/fpprt-lang.c \
    runtime/gc/src/gc-platform-gnu-linux.c runtime/gc/src/gc-stack.c \
    runtime/gc/src/gc-options.c runtime/gc/src/gc-tracepoint.c \
    runtime/gc/src/gc-ephemeron.c runtime/gc/src/gc-finalizer.c \
    runtime/gc/src/semi.c -lm -o app-arm64
```

`semi` is the single-threaded collector; use `mmc` (multi-mutator, real
pinning) and link `runtime/gc/src/mmc.c` for programs that use `Parallel`
or spawn threads — the same recipe the parallel gate uses.

`tests/tooling/cback/mobile-gate.sh` builds this for both `aarch64` and
`x86_64` on every run. The x86_64 static binary is bionic-static and
syscall-compatible with a Linux kernel, so it executes on the build host —
that is the gate's runtime assertion. The aarch64 binary is a real Android
ARM executable; push it with `adb push` and run it in `adb shell`, or link
it into an app's JNI as a native library.

## iOS

Same C, Apple's clang. This needs the iOS SDK, which means a Mac — the
build machine here is Linux, so iOS is documented, not gated:

```bash
fpp build -o app.c app.fpp
xcrun -sdk iphoneos clang -arch arm64 -O2 \
    -Iruntime -Iruntime/gc/api -Iruntime/gc/src \
    -DNDEBUG -DGC_PRECISE_ROOTS=1 \
    -DGC_ATTRS='"runtime/gc/api/semi-attrs.h"' \
    -DGC_EMBEDDER='"runtime/fpprt-embedder.h"' \
    app.c runtime/fpprt.c runtime/fpprt-lang.c \
    runtime/gc/src/gc-platform-gnu-linux.c runtime/gc/src/gc-stack.c \
    runtime/gc/src/gc-options.c runtime/gc/src/gc-tracepoint.c \
    runtime/gc/src/gc-ephemeron.c runtime/gc/src/gc-finalizer.c \
    runtime/gc/src/semi.c -o app
```

`gc-platform-gnu-linux.c` covers Darwin's POSIX surface for the stack and
signal handling fpprt needs; a dedicated `gc-platform-darwin.c` is the
tidy-up, not a blocker. Link the result into an app as a static library
called from Swift or Objective-C.

The point either way: **F++ reaches a phone as a small native binary over
its own GC — no VM, no JIT, no runtime to install** — which is the whole
reason the language exists.
