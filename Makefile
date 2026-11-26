# lean-solana-client build.
#
# No C toolchain is involved: the compiler is the prebuilt bootstrap/leanc
# (a 143 KB static binary), and everything after that is leanc turning Lean
# into machine code. `make from-c` rebuilds the compiler from its C source
# for those who want to; `make verify-seed` checks that both compilers emit
# the same bytes.

CC      ?= cc
CFLAGS  ?= -O2 -Wall -Wextra -Wno-unused-parameter -Wno-missing-field-initializers
LEANC   := build/leanc
SEED    := bootstrap/leanc
SRC     := $(wildcard leanc/*.c) leanc/leanc.h
LEAN_SRC := $(wildcard rt/*.lean lib/*.lean lib/*/*.lean client/*.lean)
INCLUDE := -I rt -I lib -I client

all: $(LEANC) build/leansol

# The compiler: by default, the checked-in seed.
$(LEANC): $(SEED)
	@mkdir -p build
	cp $(SEED) $@

# The client: Lean in, static x86-64 ELF out.
build/leansol: $(LEANC) $(LEAN_SRC)
	$(LEANC) -v $(INCLUDE) -o $@ client/Main.lean

run: build/leansol
	./build/leansol

test: $(LEANC)
	tests/run.sh

# ---- optional: the compiler from its C source ------------------------------

# No libc, no dynamic linker: leanc itself is a static, freestanding binary.
build/leanc-c: $(SRC)
	@mkdir -p build
	$(CC) -std=gnu11 $(CFLAGS) -ffreestanding -fno-stack-protector -fno-builtin -nostdlib -static \
		-o $@ leanc/*.c

# Use the compiler built from C instead of the seed.
from-c: build/leanc-c
	cp build/leanc-c $(LEANC)

# The seed's machine code depends on which C compiler built it; what must not
# depend on anything is its output. Compile the client with the seed and with
# a compiler built here from C, and require identical bytes.
verify-seed: build/leanc-c
	build/leanc-c $(INCLUDE) -o build/leansol.from-c client/Main.lean
	$(SEED) $(INCLUDE) -o build/leansol.from-seed client/Main.lean
	cmp build/leansol.from-c build/leansol.from-seed
	@echo "seed and source agree: identical client binary ($$(sha256sum < build/leansol.from-seed | cut -c1-16)...)"

# After changing leanc/*.c: refresh the seed.
update-seed: build/leanc-c
	cp build/leanc-c $(SEED)

# Hosted build with sanitizers, for working on the compiler itself.
build/leanc-debug: $(SRC)
	@mkdir -p build
	$(CC) -std=gnu11 -g -O0 -Wall -Wextra -Wno-unused-parameter -DLEANC_HOSTED -fsanitize=address,undefined \
		-fno-builtin -o $@ leanc/*.c

# ---- optional: on-chain programs --------------------------------------------
#
# tests/programs/ holds sBPF programs used as test inputs: programs written
# in Lean and compiled by toly's lean-svm (https://github.com/aeyakovenko/lean-svm,
# Apache-2.0), and two builds of the SPL token programs. This rebuilds the
# lean-svm ones from that repository at a pinned commit, compares them with
# the checked-in files, and checks every file's hash. Needs git and `lake`.
LEAN_SVM := https://github.com/aeyakovenko/lean-svm
LEAN_SVM_COMMIT := 81507bb6f8309b4f20be5dd4ee326ed030079c68

programs:
	@mkdir -p build/programs
	@test -d build/lean-svm || git clone -q $(LEAN_SVM) build/lean-svm
	cd build/lean-svm && git fetch -q && git checkout -q $(LEAN_SVM_COMMIT) && lake build LeanSVM Examples lean-svm
	@for pair in Noop:noop Counter:counter Vault:vault HashCheck:hashcheck Amm:amm \
			BondingCurve:bonding_curve DutchAuction:dutch_auction; do \
		p=$${pair%%:*}; out=$${pair##*:}.so; \
		(cd build/lean-svm && lake exe lean-svm build Examples.$$p Examples.$$p.entrypoint -o ../programs/$$out > /dev/null) && \
		cmp build/programs/$$out tests/programs/$$out && echo "$$out: identical to tests/programs/$$out" || exit 1; \
	done
	cd tests/programs && sha256sum -c SHA256SUMS

# Optional: have the official Lean toolchain type-check every Lean file here
# and re-run the tests under it. Needs `lake` (https://lean-lang.org).
lean-check: $(LEANC)
	lake build
	tests/run.sh --oracle

clean:
	rm -rf build

.PHONY: all run test from-c verify-seed update-seed programs lean-check clean
