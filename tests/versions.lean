import Solana.Bank

/-! One program, four encodings: the sysvar probe compiled for sBPF v0, v1,
v2 and v3.

The versions differ in how a program is laid out and encoded, not in what
it means. v1 lets functions move the stack pointer themselves. v2 re-encodes
arithmetic and memory instructions and adds explicit signed and unsigned
division, remainder and high multiplication. v3 returns to v0's instruction
set, adds 32-bit conditional jumps, names system calls by hash, and loads
from a stricter file with nothing to relocate.

Each build does the same arithmetic on the same numbers (64-bit, 32-bit,
signed, unsigned, 128-bit) and must print the same results, at a different
cost. `tests/oracle-next` runs the same four files on Agave; `make oracle`
requires the two reports to be identical. -/

def key (name : String) : ByteArray := Sha256.hash name.toUTF8

def u64le (v : UInt64) : ByteArray := Wire.putU64 (ByteArray.emptyWithCapacity 8) v

def none_ : Array Tx.Key := Array.emptyWithCapacity 0

def transfer (source dest : ByteArray) (lamports : UInt64) : Tx.Instruction :=
  ⟨Sbpf.systemProgram, #[⟨source, true, true⟩, ⟨dest, false, true⟩], Wire.putU64 (Wire.putU32 ByteArray.empty 2) lamports⟩

def run (label : String) (bank : Bank.Bank) (instructions : Array Tx.Instruction) : IO Bank.Bank := do
  let payer := Ed25519.publicKey (key "payer")
  let alice := Ed25519.publicKey (key "alice")
  let tx := Tx.sign (Tx.compile payer instructions bank.blockhash) #[key "payer"]
  let r := bank.process (Tx.parse tx.serialize) true
  IO.println s!"{label}: {if r.error == "" then "success" else r.error}, fee {r.fee}, {r.units} units"
  IO.println s!"  signature {Base58.encode tx.signatures[0]!}"
  for line in r.logs do
    IO.println s!"  log: {line}"
  IO.println s!"  payer {(r.bank.get payer).lamports}, alice {(r.bank.get alice).lamports}"
  return r.bank

def main : IO Unit := do
  let payer := Ed25519.publicKey (key "payer")
  let alice := Ed25519.publicKey (key "alice")
  let blockhash := Base58.decode "CmpNeggWJ4JaWJeJ8YKN1Zypmk7uvQq3PECGUCAEMbky"
  let mut bank := (Bank.create ⟨0, 0, 0, 0, 0⟩).withBlockhash blockhash
  bank := bank.set ⟨payer, Sbpf.systemProgram, 10000000000, ByteArray.empty, false⟩
  bank := bank.set ⟨alice, Sbpf.systemProgram, 2000000000, ByteArray.empty, false⟩
  IO.println s!"blockhash {Base58.encode blockhash}"
  let files : Array String := #["tests/programs/sysvar_probe.so", "tests/programs/sysvar_probe_v1.so",
    "tests/programs/sysvar_probe_v2.so", "tests/programs/sysvar_probe_v3.so"]
  let mut versions : Array Nat := Array.emptyWithCapacity 4
  for file in files do
    let bytes ← IO.FS.readBinFile file
    let program := Sbpf.load bytes
    if program.error != "" then
      IO.println s!"sBPF v{bytes[48]!}: this runtime does not accept the program"
    else
      bank := bank.addProgram (key s!"probe for sBPF v{program.version}") program
      versions := versions.push program.version
  let numbers := (ByteArray.empty.push 4) ++ u64le 0xFEDCBA9876543210 ++ u64le 0x0123456789ABCDEF ++ u64le 1000003
  let sysvar : Tx.Key := ⟨Base58.decode "Sysvar1nstructions1111111111111111111111111", false, false⟩
  for version in versions do
    let program := key s!"probe for sBPF v{version}"
    bank ← run s!"sBPF v{version}, arithmetic" bank #[⟨program, none_, numbers⟩]
    bank ← run s!"sBPF v{version}, reads its own transaction" bank #[transfer payer alice (1000 + version.toUInt64),
      ⟨program, #[sysvar], ByteArray.empty.push 2⟩]
