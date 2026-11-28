import Solana.Bank

/-! Where a program's memory ends.

A program sees each account's data followed by 10,240 bytes of room to grow
into. Validators used to hand that room over as zeros. Since mainnet's epoch
1097 it is not there until the program writes to it; an account the program
may not change cannot be written at all, not even with what it already holds;
and both are errors the moment they happen, costing the program everything
it had left to spend.

`tests/programs/memory-probe` does each of those things, one per
instruction, on an account of its own, the same passed read-only, and another
program's. `oracle-next memory` runs the same transactions on Agave with
accounts mapped that way; `make oracle` requires the two reports to be
identical. -/

def key (name : String) : ByteArray := Sha256.hash name.toUTF8

def does : Array String := #["reads the last byte", "reads the byte after the last", "reads eight bytes across the end",
  "reads the last byte of the room", "reads what follows the room", "writes a byte back as it is",
  "writes into the room and reads elsewhere in it", "writes into the room and grows by a byte",
  "writes eight bytes across the end and grows", "grows without writing, then reads", "copies its data out by system call",
  "copies across the end by system call", "fills across the end by system call and grows",
  "copies from its header into its data by system call", "reads an address where nothing is", "does something else"]

def main : IO Unit := do
  let payer := Ed25519.publicKey (key "payer")
  let alice := Ed25519.publicKey (key "alice")
  let probe := key "memory probe"
  let blockhash := Base58.decode "CmpNeggWJ4JaWJeJ8YKN1Zypmk7uvQq3PECGUCAEMbky"
  let mut bank := (Bank.create ⟨0, 0, 0, 0, 0⟩).withBlockhash blockhash
  bank := bank.addProgram probe (Sbpf.load (← IO.FS.readBinFile "tests/programs/memory_probe.so"))
  bank := bank.set ⟨payer, Sbpf.systemProgram, 10000000000, ByteArray.empty, false⟩
  bank := bank.set ⟨alice, Sbpf.systemProgram, 2000000000, ByteArray.empty, false⟩
  IO.println s!"blockhash {Base58.encode blockhash}"
  let mut contents := ByteArray.emptyWithCapacity 16
  for i in [1:17] do
    contents := contents.push i.toUInt8
  let kinds := #["its own account", "its own account, read-only", "another program's account"]
  for k in [0:3] do
    let target := key kinds[k]!
    for mode in [0:16] do
      -- the account as it was, every time: 16 bytes, 1 to 16
      bank := bank.set ⟨target, if k == 2 then key "someone" else probe, 1000000000, contents, false⟩
      let tx := Tx.sign (Tx.compile payer #[⟨probe, #[⟨target, false, k != 1⟩], ByteArray.empty.push mode.toUInt8⟩] bank.blockhash) #[key "payer"]
      let result := bank.process (Tx.parse tx.serialize) true
      bank := result.bank
      IO.println s!"{kinds[k]!}: {does[mode]!}: {if result.error == "" then "success" else result.error}, fee {result.fee}, {result.units} units"
      IO.println s!"  signature {Base58.encode tx.signatures[0]!}"
      IO.println s!"  payer {(bank.get payer).lamports}, alice {(bank.get alice).lamports}"
      let a := bank.get target
      IO.println s!"  the account: {a.lamports} lamports, {a.data.size} bytes, owner {Base58.encode a.owner}, data {Base58.encode (Sha256.hash a.data)}"
