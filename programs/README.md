# programs: built-in programs that are bytecode today

Solana's stake, config and address lookup table programs used to be native
code inside the validator. They have since been rewritten as ordinary sBPF
programs ("Core BPF") and deployed at the same addresses. These are those
programs, each named by the address it lives at:

| file | program |
|---|---|
| `Stake11111111111111111111111111111111111111.so` | stake accounts (core-bpf-stake 1.0.1) |
| `Config1111111111111111111111111111111111111.so` | config records |
| `AddressLookupTab1e1111111111111111111111111.so` | address lookup tables |

They are the builds [LiteSVM](https://github.com/LiteSVM/litesvm) v0.11.0
bundles (`crates/litesvm/src/programs/elf/`), unmodified; Apache-2.0.
`SHA256SUMS` lists their hashes.

The virtual machine runs them like any other program. `tests/builtins.lean`
uses them, and from the command line:

    leansol tx <transaction> --programs programs/ --account ...

loads whichever of them the transaction names.
