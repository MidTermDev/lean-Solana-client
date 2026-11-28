# tests/programs: on-chain programs used as test inputs

Everything here is sBPF v0 bytecode that this repository's virtual machine
(`lib/Solana/Sbpf.lean`) loads and runs in its tests. Apart from the Anchor
program and the sysvar probe, none of it was built here, and none of it is modified. `SHA256SUMS` lists the hashes.

## Written in Lean, compiled by lean-svm

`noop.so`, `counter.so`, `vault.so`, `hashcheck.so`, `amm.so`,
`bonding_curve.so`, `dutch_auction.so`

Programs written in Lean 4 by Anatoly Yakovenko and compiled by his
[lean-svm](https://github.com/aeyakovenko/lean-svm) compiler: the output of
that project for its examples of the same names, at commit
`81507bb6f8309b4f20be5dd4ee326ed030079c68`. Apache-2.0.

    make programs    # rebuild them from lean-svm and compare byte for byte

## The SPL token programs

`spl_token_2022-10.0.0.so`, `pinocchio_token_program.so`

The Token-2022 program and the program that serves the classic Token
address (p-token), as bundled by [LiteSVM](https://github.com/LiteSVM/litesvm)
v0.11.0 in `crates/litesvm/src/programs/elf/`. These are the builds
lean-svm's test runner executes, which is what lets the tests here compare
compute-unit totals with the ones it reports. Both are built with the
standard Rust toolchain from the Solana Program Library and p-token
sources. Apache-2.0.

## The Associated Token Account program

`spl_associated_token_account-1.1.1.so`

Also as bundled by LiteSVM v0.11.0. A Rust program built on `solana-program`
that creates token accounts at derived addresses, calling the token program
and the system program to do it. Apache-2.0.

## An Anchor program, with its source

`anchor_vault.so`, built from [`anchor-vault/`](anchor-vault/src/lib.rs)

A token vault written for this repository with Anchor 0.32.1 (MIT, like the
rest of the repository). It is here to exercise what Anchor programs do when
they call other programs. Built with:

    cargo build-sbf --manifest-path tests/programs/anchor-vault/Cargo.toml

using Solana 3.1 tools (platform-tools v1.52). The checked-in file is what
the tests and `tests/oracle` use; a rebuild with other tool versions will
differ in bytes and possibly in compute units.

## A sysvar probe, with its source

`sysvar_probe.so`, built from [`sysvar-probe/`](sysvar-probe/src/lib.rs)

A Rust program written for this repository (MIT) that asks for every sysvar
in every way a program can (dedicated system calls, the generic one, and
accounts), reads the transaction it is part of, and logs what it finds.
Two runtimes that produce the same logs agree on the sysvars. Built like
the Anchor program, with `solana-program` 2.3.

## A memory probe, with its source

`memory_probe.so`, built from [`memory-probe/`](memory-probe/src/lib.rs)

A Rust program written for this repository (MIT), with no SDK and no
dependencies, that reads and writes around the end of an account's data: the
last byte, the byte after it, the room an account may grow into, by plain
instructions and by the system calls that copy and fill. Where a runtime puts
the end of a program's memory shows in which of those succeed. Built with the
same tool (`cargo-build-sbf`, platform-tools v1.52).

## The same programs for other versions of sBPF

`sysvar_probe_v1.so`, `sysvar_probe_v2.so`, `sysvar_probe_v3.so`, `anchor_vault_v3.so`

The sysvar probe and the Anchor vault again, from the same sources, built
with `cargo build-sbf --arch v1` (and `v2`, `v3`). Versions 1 and 2 use
platform-tools v1.52; version 3 needs a newer compiler and uses
`--tools-version v1.57`. `tests/versions.lean` and `tests/anchor.lean` run
them, and `tests/oracle-next` runs them on Agave 4.3.

## What the tests do with them

`tests/sbpf.lean` runs the four self-contained programs. `tests/cpi.lean`
runs the AMM, the bonding curve and the Dutch auction, which call the token
programs and the system program: three or four programs executing inside
one another. Both use lean-svm's own scenarios and require the
compute-unit counts its runner reports from Agave. `tests/anchor.lean` runs
the Anchor vault, which calls the Associated Token Account program, which
calls the token program; `make oracle` runs the same scenario on Agave's
runtime and requires identical output. `tests/transaction.lean` applies
whole signed transactions, using the counter and the sysvar probe, and is
compared with Agave the same way.

Try one:

    leansol run tests/programs/counter.so --data 01 \
        --account counter:program:1000000:e703000000000000:w
