# tests/programs: on-chain programs written in Lean

These four `.so` files are Solana programs (sBPF v0 bytecode). They were
written in Lean 4 by Anatoly Yakovenko and compiled by his
[lean-svm](https://github.com/aeyakovenko/lean-svm) compiler: they are the
unmodified output of that project for its `Noop`, `Counter`, `Vault` and
`HashCheck` examples at commit `81507bb6f8309b4f20be5dd4ee326ed030079c68`.
lean-svm is licensed under Apache-2.0, and so are these files.

They are here as test inputs for this repository's sBPF virtual machine
(`lib/Solana/Sbpf.lean`). `tests/sbpf.lean` runs them through the same
scenarios lean-svm's own test runner uses and requires the compute-unit
counts that runner reports from Agave.

    make programs    # rebuild them from lean-svm and compare byte for byte

Try one:

    leansol run tests/programs/counter.so --data 01 \
        --account counter:program:1000000:e703000000000000:w
