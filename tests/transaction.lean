import Solana.Bank

/-! Whole transactions: fees, compute budgets, several instructions that take
effect together or not at all, rent, and every sysvar.

Each transaction here is built, signed with real Ed25519 keys, serialized,
parsed back and then applied to a bank. `tests/oracle` builds the same
transactions with Solana's SDK and applies them on Agave's runtime. The two
must print the same thing, line for line, and since the first line of each
report is the transaction's signature, the bytes that were signed are the
same too. `make oracle` checks it.

`tests/programs/sysvar-probe` is a Rust program that asks for every sysvar in
every way a program can and logs what it gets; its logs are how the sysvars
are compared. -/

def key (name : String) : ByteArray := Sha256.hash name.toUTF8

def u64le (v : UInt64) : ByteArray := Wire.putU64 (ByteArray.emptyWithCapacity 8) v

def none_ : Array Tx.Key := Array.emptyWithCapacity 0

/-- An instruction for the compute budget program: a tag, then a little-endian number. -/
def budget (tag : UInt8) (value : UInt64) (width : Nat) : Tx.Instruction :=
  ⟨Sbpf.computeBudgetProgram, none_, (ByteArray.empty.push tag) ++ (u64le value).extract 0 width⟩

def unitLimit (units : UInt64) : Tx.Instruction := budget 2 units 4
def unitPrice (microLamports : UInt64) : Tx.Instruction := budget 3 microLamports 8
def heapFrame (bytes : UInt64) : Tx.Instruction := budget 1 bytes 4

def transfer (source dest : ByteArray) (lamports : UInt64) : Tx.Instruction :=
  ⟨Sbpf.systemProgram, #[⟨source, true, true⟩, ⟨dest, false, true⟩], Wire.putU64 (Wire.putU32 ByteArray.empty 2) lamports⟩

def createAccount (source fresh : ByteArray) (lamports space : UInt64) (owner : ByteArray) : Tx.Instruction :=
  ⟨Sbpf.systemProgram, #[⟨source, true, true⟩, ⟨fresh, true, true⟩],
    Wire.putU64 (Wire.putU64 (Wire.putU32 ByteArray.empty 0) lamports) space ++ owner⟩

/-- An instruction for the Ed25519 program: check the signature the holder of
`seed` made of `message`. `claimed` is the message the instruction says was signed. -/
def ed25519 (seed message claimed : ByteArray) : Tx.Instruction := Id.run do
  let pk := Ed25519.publicKey seed
  let mut data := (ByteArray.empty.push 1).push 0
  -- where the signature, the public key and the message are: offset, then which instruction (0xFFFF = this one)
  let fields : Array UInt64 := #[48, 0xFFFF, 16, 0xFFFF, 112, claimed.size.toUInt64, 0xFFFF]
  for f in fields do
    data := Wire.putU16 data f
  return ⟨Bank.ed25519Program, none_, data ++ pk ++ Ed25519.sign seed pk message ++ claimed⟩

def readonly (address : String) : Tx.Key := ⟨Base58.decode address, false, false⟩

/-- Serializes a transaction, parses it back, applies it, and reports. -/
def send (label : String) (bank : Bank.Bank) (tx : Tx.Transaction) : IO Bank.Bank := do
  let r := bank.process (Tx.parse tx.serialize) true
  IO.println s!"{label}: {if r.error == "" then "success" else r.error}, fee {r.fee}, {r.units} units"
  IO.println s!"  signature {Base58.encode tx.signatures[0]!}"
  for line in r.logs do
    IO.println s!"  log: {line}"
  let payer := Ed25519.publicKey (key "payer")
  let alice := Ed25519.publicKey (key "alice")
  IO.println s!"  payer {(r.bank.get payer).lamports}, alice {(r.bank.get alice).lamports}"
  return r.bank

/-- A transaction paid for and signed by the usual payer alone. -/
def run (label : String) (bank : Bank.Bank) (instructions : Array Tx.Instruction) : IO Bank.Bank :=
  send label bank (Tx.sign (Tx.compile (Ed25519.publicKey (key "payer")) instructions bank.blockhash) #[key "payer"])

def count (bank : Bank.Bank) (counter : ByteArray) : IO Unit := do
  let account := bank.get counter
  if account.lamports == 0 then
    IO.println "  the counter account does not exist"
  else
    IO.println s!"  count {Wire.u64 account.data 0}"

def main : IO Unit := do
  let probe := key "sysvar probe"
  let counter := key "counter program"
  let payer := Ed25519.publicKey (key "payer")
  let alice := Ed25519.publicKey (key "alice")
  let bob := Ed25519.publicKey (key "bob")
  let poor := Ed25519.publicKey (key "poor")
  let nobody := Ed25519.publicKey (key "nobody")
  let system := Sbpf.systemProgram
  let blockhash := Base58.decode "CmpNeggWJ4JaWJeJ8YKN1Zypmk7uvQq3PECGUCAEMbky"
  let mut bank := (Bank.create ⟨0, 0, 0, 0, 0⟩).withBlockhash blockhash
  bank := bank.addProgram probe (Sbpf.load (← IO.FS.readBinFile "tests/programs/sysvar_probe.so"))
  bank := bank.addProgram counter (Sbpf.load (← IO.FS.readBinFile "tests/programs/counter.so"))
  bank := bank.set ⟨payer, system, 10000000000, ByteArray.empty, false⟩
  bank := bank.set ⟨alice, system, 2000000000, ByteArray.empty, false⟩
  bank := bank.set ⟨poor, system, 3000, ByteArray.empty, false⟩
  IO.println s!"blockhash {Base58.encode blockhash}"
  let instructionsSysvar := readonly "Sysvar1nstructions1111111111111111111111111"

  -- fees: 5,000 lamports per signature, plus the price offered per compute unit of the limit
  bank ← run "transfer, with a priority fee" bank #[unitLimit 300000, unitPrice 2500, transfer payer alice 1000000000]

  -- the sysvars, as a program sees them
  bank ← run "sysvars by system call" bank #[⟨probe, none_, ByteArray.empty.push 0⟩]
  bank ← run "sysvars by address" bank #[⟨probe, none_, ByteArray.empty.push 3⟩]
  bank ← run "sysvar accounts" bank #[unitLimit 1400000, ⟨probe, #[
    readonly "SysvarC1ock11111111111111111111111111111111",
    readonly "SysvarEpochSchedu1e111111111111111111111111",
    readonly "SysvarEpochRewards1111111111111111111111111",
    readonly "SysvarFees111111111111111111111111111111111",
    readonly "SysvarLastRestartS1ot1111111111111111111111",
    readonly "SysvarRecentB1ockHashes11111111111111111111",
    readonly "SysvarRent111111111111111111111111111111111",
    readonly "SysvarS1otHashes111111111111111111111111111",
    readonly "SysvarS1otHistory11111111111111111111111111",
    readonly "SysvarStakeHistory1111111111111111111111111",
    instructionsSysvar], ByteArray.empty.push 1⟩]
  bank ← run "a program reads its own transaction" bank #[unitPrice 1, transfer payer alice 5000,
    ⟨probe, #[instructionsSysvar], ByteArray.empty.push 2⟩]

  -- several instructions, two signers: create an account, hand it to the counter program, count twice
  let counting : Array Tx.Key := #[⟨bob, false, true⟩]
  bank ← send "create an account and count twice" bank (Tx.sign (Tx.compile payer #[createAccount payer bob 946560 8 counter,
    ⟨counter, counting, ByteArray.empty.push 0⟩, ⟨counter, counting, ByteArray.empty.push 1⟩,
    ⟨counter, counting, ByteArray.empty.push 1⟩] blockhash) #[key "payer", key "bob"])
  count bank bob

  -- all or nothing: the third instruction overflows, so the transfer and the first count are undone. The fee is not.
  bank ← run "the last instruction fails" bank #[transfer payer alice 7, ⟨counter, counting, ByteArray.empty.push 1⟩,
    ⟨counter, counting, (ByteArray.empty.push 2) ++ u64le 0xFFFFFFFFFFFFFFFF⟩]
  count bank bob

  -- rent: an account may not be left with a balance too small to keep it alive
  bank ← run "leaves an account below the rent minimum" bank #[transfer payer (key "pauper") 1000]

  -- the Ed25519 program: signatures checked by the runtime, visible to programs through the Instructions sysvar
  bank ← run "a signature checked by the runtime" bank #[ed25519 (key "alice") "hello".toUTF8 "hello".toUTF8,
    ⟨probe, #[instructionsSysvar], ByteArray.empty.push 2⟩]
  bank ← run "a signature that does not match" bank #[ed25519 (key "alice") "hello".toUTF8 "jello".toUTF8, transfer payer alice 9]

  -- the compute budget
  bank ← run "the same budget instruction twice" bank #[unitLimit 1000, unitLimit 2000, transfer payer alice 11]
  bank ← run "a heap size that is not allowed" bank #[heapFrame 1000, ⟨probe, none_, ByteArray.empty.push 0⟩]
  bank ← run "a bigger heap costs units" bank #[heapFrame 65536, ⟨probe, none_, ByteArray.empty.push 0⟩]
  bank ← run "a budget the program exceeds" bank #[unitLimit 2000, ⟨probe, none_, ByteArray.empty.push 0⟩]
  bank ← run "a budget too small for a transfer" bank #[unitLimit 200, transfer payer alice 13]
  bank ← run "a budget of nothing" bank #[unitLimit 0, transfer payer alice 15]

  -- who pays
  bank ← send "a payer that does not exist" bank (Tx.sign (Tx.compile nobody #[transfer nobody alice 1] blockhash) #[key "nobody"])
  bank ← send "a payer that cannot afford the fee" bank (Tx.sign (Tx.compile poor #[transfer poor alice 1] blockhash) #[key "poor"])
  let honest := Tx.sign (Tx.compile payer #[transfer payer alice 17] blockhash) #[key "payer"]
  let flipped := honest.signatures[0]!.set! 0 (honest.signatures[0]![0]! ^^^ 1)
  bank ← send "a signature that was tampered with" bank { honest with signatures := honest.signatures.set! 0 flipped }

  -- an account emptied by a transaction ceases to exist
  let all := (bank.get alice).lamports
  bank ← send "alice sends everything she has" bank (Tx.sign (Tx.compile payer #[transfer alice payer all] blockhash) #[key "payer", key "alice"])
  IO.println s!"  alice exists: {(bank.get alice).lamports != 0}"
