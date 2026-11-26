# bootstrap/leanc

A prebuilt `leanc`: the compiler in `../leanc/`, compiled once and checked in
so that building this repository needs no C toolchain. `make` copies it to
`build/leanc` and uses it to turn the Lean sources into executables.

It is a 143 KB static x86-64 Linux binary with no dynamic dependencies.

## Trusting it

You do not have to. The compiler's source is in `leanc/`, and

    make verify-seed

builds a second `leanc` from that source with your own C compiler, compiles
the client with both, and requires the two outputs to be byte-identical.
Continuous integration runs this on every push. To skip the seed entirely:

    make from-c

The seed's own bytes depend on the C compiler that produced it (this one was
built with `gcc -O2`). Its *output* does not: `leanc` built with gcc or
clang, as C99, C11 or C23, emits exactly the same executables.

## Updating it

After changing anything in `leanc/`:

    make update-seed && make verify-seed
