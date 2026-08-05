# fpprt: the F++ runtime over the vendored Whippet collector.
#   make COLLECTOR=semi test      # simplest, moves everything: root shakeout
#   make COLLECTOR=pcc test       # parallel copying (default)
#   make COLLECTOR=mmc test       # Immix-style mark-region, real pinning
#   make test-all                 # all three
GC_COLLECTOR ?= pcc
GC_BASE      = gc/
GC_EMBEDDER_H = fpprt-embedder.h
GC_OBJDIR    = build/$(GC_COLLECTOR)/
GC_EMBEDDER_CPPFLAGS = -I.

include gc/embed.mk

CFLAGS ?= -O2 -g -Wall

build/$(GC_COLLECTOR)/fpprt.o: fpprt.c fpprt.h fpprt-embedder.h | $(GC_OBJDIR)
	$(GC_CC) $(CFLAGS) $(GC_CPPFLAGS) $(GC_EMBEDDER_CPPFLAGS) -c -o $@ $<

build/$(GC_COLLECTOR)/test_rt: test/test_rt.c build/$(GC_COLLECTOR)/fpprt.o $(GC_OBJDIR)libwhippet.a
	$(GC_CC) $(CFLAGS) $(GC_CPPFLAGS) $(GC_EMBEDDER_CPPFLAGS) -o $@ $^ $(GC_LIBS)

.PHONY: test test-all clean
test: build/$(GC_COLLECTOR)/test_rt
	./$<

test-all:
	$(MAKE) GC_COLLECTOR=semi test
	$(MAKE) GC_COLLECTOR=pcc test
	$(MAKE) GC_COLLECTOR=mmc test

clean:
	rm -rf build

# ---- wasm (emscripten standalone, runs under wasmtime) ----------------------
# Single-threaded semispace for now: the platform shim has no threads.
WASM_CC = emcc
WASM_FLAGS = -O2 -Igc/api -Igc/src -I. -DNDEBUG -DGC_PRECISE_ROOTS=1 \
  -DGC_ATTRS=\"$(abspath gc/api/semi-attrs.h)\" \
  -DGC_EMBEDDER=\"$(abspath fpprt-embedder.h)\" \
  -s STANDALONE_WASM -s PURE_WASI=1 -s ALLOW_MEMORY_GROWTH=1

WASM_SRCS = gc-platform-wasm.c gc/src/gc-stack.c gc/src/gc-options.c \
  gc/src/gc-tracepoint.c gc/src/gc-ephemeron.c gc/src/gc-finalizer.c \
  gc/src/semi.c fpprt.c

build/wasm/test_rt.wasm: test/test_rt.c $(WASM_SRCS) fpprt.h fpprt-embedder.h
	@mkdir -p build/wasm
	$(WASM_CC) $(filter %.c,$^) $(WASM_FLAGS) -o $@ -s STANDALONE_WASM 2>/dev/null || \
	$(WASM_CC) $(filter %.c,$^) -O2 -Igc/api -Igc/src -I. -DNDEBUG -DGC_PRECISE_ROOTS=1 \
	  -DGC_ATTRS=\"$(abspath gc/api/semi-attrs.h)\" \
	  -DGC_EMBEDDER=\"$(abspath fpprt-embedder.h)\" \
	  -s STANDALONE_WASM -s PURE_WASI=1 -s ALLOW_MEMORY_GROWTH=1 -o $@

.PHONY: test-wasm
test-wasm: build/wasm/test_rt.wasm
	$(HOME)/.wasmtime/bin/wasmtime run $<
