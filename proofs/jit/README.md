# The ALU translation, proved

`Certificate.pinned_step_correct` in `Proof.lean`: for every ALU opcode byte that `Jit.aluKind` accepts
(54 bytes, sBPF v0 and v3), every dst r0-r9, src r0-r10, imm32 and register file, running the bytes that
`Jit.aluCode` emits on the x86-64 model in `X86.lean` gives the same r0-r10 as one step of the
interpreter's ALU arm (`Sbpf.aluStep`). That includes the 32-bit add/sub/mul sign extension, masked shifts
(SHLX/SHRX/SARX), div/mod and the byte swaps. A register divisor of zero takes the fault branch with every
guest register unchanged (`linked_division_correct`, `div_sites`).

`aluCode` is the ALU part of `compile`, moved into its own function in `lib/Solana/Jit.lean` without
changing a byte. The definitions the proof needs are copied from b9fa957 (`Alu.lean`, `Interpreter.lean`)
and keep the source in a header.

Not covered: the fault stubs, metering, program layout and memory, the rest of `compile`, v1 and v2.
`X86.lean` is a model of the instructions `aluCode` emits. `Vectors.lean` writes 30,272 cases from it
(472 byte sequences, 66 register files) and `run_vectors.c` runs them on the CPU.

With the official Lean 4.36.0:

    cd proofs/jit && lake build
    lake env lean --run Vectors.lean vectors > vectors.tsv
    cc -O1 -o run_vectors run_vectors.c && ./run_vectors vectors.tsv   # x86-64 with BMI2

`#print axioms` on the three theorems shows only `propext`, `Classical.choice` and `Quot.sound`: no `sorry`,
no `native_decide`, no `Lean.ofReduceBool`.
