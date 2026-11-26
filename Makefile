# lean-solana-client build. The only tool needed is a C compiler, and only to
# bootstrap leanc; everything after that is leanc compiling Lean to machine code.

CC      ?= cc
CFLAGS  ?= -O2 -Wall -Wextra -Wno-unused-parameter -Wno-missing-field-initializers
LEANC   := build/leanc
SRC     := $(wildcard leanc/*.c) leanc/leanc.h

LEAN_SRC := $(wildcard rt/*.lean lib/*.lean lib/*/*.lean client/*.lean)

all: $(LEANC) build/leansol

# The client: Lean in, static x86-64 ELF out.
build/leansol: $(LEANC) $(LEAN_SRC)
	$(LEANC) -v -I rt -I lib -I client -o $@ client/Main.lean

run: build/leansol
	./build/leansol

test: $(LEANC)
	tests/run.sh

# Optional: have the official Lean toolchain type-check every Lean file here
# and re-run the tests under it. Needs `lake` (https://lean-lang.org).
lean-check:
	lake build
	tests/run.sh --oracle

# No libc, no dynamic linker: leanc itself is a static, freestanding binary.
$(LEANC): $(SRC)
	@mkdir -p build
	$(CC) -std=gnu11 $(CFLAGS) -ffreestanding -fno-stack-protector -fno-builtin -nostdlib -static \
		-o $@ leanc/*.c

# Hosted build with sanitizers, for working on the compiler itself.
build/leanc-debug: $(SRC)
	@mkdir -p build
	$(CC) -std=gnu11 -g -O0 -Wall -Wextra -Wno-unused-parameter -DLEANC_HOSTED -fsanitize=address,undefined \
		-fno-builtin -o $@ leanc/*.c

clean:
	rm -rf build

.PHONY: all run test lean-check clean
