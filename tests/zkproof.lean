import Solana.Bank

/-! The ZK ElGamal proof program: proofs about encrypted token balances,
checked by a program built into the validator.

`tests/zkproofs.bin` holds proofs of every kind, made by the library the
validators use (`oracle-next zkproof-make`; proofs are random, so the file is
one run, kept). Each is checked as made and with a bit changed; then what a
proof was about is stored in an account, read from one, and such accounts are
closed.

`oracle-next zkproof` runs the same transactions on Agave; `make oracle`
requires the two reports to be identical. -/

def key (name : String) : ByteArray := Sha256.hash name.toUTF8
def u64le (v : UInt64) : ByteArray := Wire.putU64 (ByteArray.emptyWithCapacity 8) v
def u32le (v : UInt64) : ByteArray := Wire.putU32 (ByteArray.emptyWithCapacity 4) v

def system : ByteArray := Sbpf.systemProgram
def program : ByteArray := Sbpf.zkProofProgram

def w (k : ByteArray) : Tx.Key := ⟨k, false, true⟩
def r (k : ByteArray) : Tx.Key := ⟨k, false, false⟩
def rs (k : ByteArray) : Tx.Key := ⟨k, true, false⟩
def ws (k : ByteArray) : Tx.Key := ⟨k, true, true⟩

def transfer (source dest : ByteArray) (lamports : UInt64) : Tx.Instruction :=
  ⟨system, #[ws source, w dest], u32le 2 ++ u64le lamports⟩

def createAccount (source fresh : ByteArray) (lamports space : UInt64) (owner : ByteArray) : Tx.Instruction :=
  ⟨system, #[ws source, ws fresh], u32le 0 ++ u64le lamports ++ u64le space ++ owner⟩

def unitLimit (units : UInt64) : Tx.Instruction := ⟨Sbpf.computeBudgetProgram, #[], (ByteArray.empty.push 2) ++ u32le units⟩

def proof (data : ByteArray) (accounts : Array Tx.Key) : Tx.Instruction := ⟨program, accounts, data⟩

def withKind (kind : UInt8) (bytes : ByteArray) : ByteArray := (ByteArray.empty.push kind) ++ bytes

def changed (b : ByteArray) (i : Nat) : ByteArray := b.set! i (b[i]! ^^^ 1)

/-- A transaction paid for by the usual payer and signed by it and by the holders of `seeds`. -/
def signed (label : String) (bank : Bank.Bank) (seeds : Array ByteArray) (instructions : Array Tx.Instruction) : IO Bank.Bank := do
  let payer := Ed25519.publicKey (key "payer")
  let tx := Tx.sign (Tx.compile payer instructions bank.blockhash) (seeds.push (key "payer"))
  let result := bank.process (Tx.parse tx.serialize) true
  IO.println s!"{label}: {if result.error == "" then "success" else result.error}, fee {result.fee}, {result.units} units"
  IO.println s!"  signature {Base58.encode tx.signatures[0]!}"
  IO.println s!"  payer {(result.bank.get payer).lamports}, alice {(result.bank.get (Ed25519.publicKey (key "alice"))).lamports}"
  return result.bank

def showAccount (bank : Bank.Bank) (name : String) (k : ByteArray) : IO Unit := do
  let a := bank.get k
  if a.lamports == 0 then
    IO.println s!"  {name}: no such account"
  else
    IO.println s!"  {name}: {a.lamports} lamports, {a.data.size} bytes, owner {Base58.encode a.owner}, data {Base58.encode (Sha256.hash a.data)}"

def nobody : Array ByteArray := Array.emptyWithCapacity 0
def none_ : Array Tx.Key := Array.emptyWithCapacity 0

def main : IO Unit := do
  -- the proofs: each a kind, a length in two bytes, and that many bytes
  let file ← IO.FS.readBinFile "tests/zkproofs.bin"
  let mut kinds : Array UInt8 := Array.emptyWithCapacity 13
  let mut proofs : Array ByteArray := Array.emptyWithCapacity 13
  let mut o := 0
  while o < file.size do
    let size := file[o + 1]!.toNat + 256 * file[o + 2]!.toNat
    kinds := kinds.push file[o]!
    proofs := proofs.push (file.extract (o + 3) (o + 3 + size))
    o := o + 3 + size

  let payer := Ed25519.publicKey (key "payer")
  let alice := Ed25519.publicKey (key "alice")
  let held := key "held"
  let blockhash := Base58.decode "CmpNeggWJ4JaWJeJ8YKN1Zypmk7uvQq3PECGUCAEMbky"
  let mut bank := (Bank.create ⟨0, 0, 0, 0, 0⟩).withBlockhash blockhash
  bank := bank.set ⟨payer, system, 10000000000, ByteArray.empty, false⟩
  bank := bank.set ⟨alice, system, 2000000000, ByteArray.empty, false⟩
  -- an account that holds a proof (the third of the file) after seven other bytes
  let mut heldData := ByteArray.emptyWithCapacity 327
  for _ in [0:7] do
    heldData := heldData.push 9
  bank := bank.set ⟨held, system, 10000000, heldData ++ proofs[2]!, false⟩
  IO.println s!"blockhash {Base58.encode blockhash}"

  -- --- every kind of proof: as made, with a bit of the proof changed, with a bit of what it is about changed
  for number in [0:proofs.size] do
    let kind := kinds[number]!
    let bytes := proofs[number]!
    bank ← signed s!"proof {number}, of kind {kind}" bank nobody #[unitLimit 400000, proof (withKind kind bytes) none_]
    bank ← signed s!"proof {number} with a bit of the proof changed" bank nobody #[unitLimit 400000, proof (withKind kind (changed bytes (bytes.size - 40))) none_]
    bank ← signed s!"proof {number} with a bit of what it is about changed" bank nobody #[unitLimit 400000, proof (withKind kind (changed bytes 5)) none_]
  bank ← signed "a 64-bit range proof on the default budget" bank nobody #[proof (withKind 6 proofs[6]!) none_]
  bank ← signed "a 256-bit range proof on the default budget" bank nobody #[proof (withKind 8 proofs[8]!) none_]
  bank ← signed "an instruction with no data" bank nobody #[proof ByteArray.empty none_]
  bank ← signed "an instruction of no kind" bank nobody #[proof (ByteArray.empty.push 13) none_]
  let keyProof := withKind 4 proofs[3]!
  bank ← signed "a proof cut short" bank nobody #[proof (keyProof.extract 0 96) none_]
  bank ← signed "a proof with a byte too many" bank nobody #[proof (keyProof.push 0) none_]

  -- --- what a proof was about, stored in an account for later instructions to rely on
  let stored := Ed25519.publicKey (key "stored")
  bank ← signed "check a proof and store what it was about" bank #[key "stored"] #[createAccount payer stored 1343280 65 program,
    proof keyProof #[w stored, r alice]]
  showAccount bank "stored" stored
  bank ← signed "store into it again" bank nobody #[transfer payer alice 1, proof keyProof #[w stored, r alice]]
  let wide := Ed25519.publicKey (key "wide")
  bank ← signed "store into an account of another size" bank #[key "wide"] #[createAccount payer wide 1350240 66 program,
    proof keyProof #[w wide, r alice]]
  bank ← signed "store into an account of another program" bank nobody #[proof keyProof #[w alice, r payer]]
  let blank := Ed25519.publicKey (key "blank")
  bank ← signed "create an account that stores nothing yet" bank #[key "blank"] #[createAccount payer blank 1343280 65 program]
  bank ← signed "store into it, passed read-only" bank nobody #[proof keyProof #[r blank, r alice]]
  showAccount bank "blank" blank

  -- --- a proof read from an account
  bank ← signed "a proof read from an account" bank nobody #[proof (withKind 3 (u32le 7)) #[r held]]
  bank ← signed "read from the wrong place" bank nobody #[proof (withKind 3 (u32le 6)) #[r held]]
  bank ← signed "read past the account's end" bank nobody #[proof (withKind 3 (u32le 8)) #[r held]]
  bank ← signed "read from no account" bank nobody #[proof (withKind 3 (u32le 7)) none_]
  let third := Ed25519.publicKey (key "third")
  bank ← signed "read from an account and store" bank #[key "third"] #[createAccount payer third 2011440 161 program,
    proof (withKind 3 (u32le 7)) #[r held, w third, r payer]]
  showAccount bank "third" third

  -- --- closing a stored context: only its authority may, and gets (or directs) the lamports
  let close := ByteArray.empty.push 0
  bank ← signed "someone else closes it" bank nobody #[proof close #[w stored, w payer, rs payer]]
  bank ← signed "close without the authority signing" bank nobody #[proof close #[w stored, w payer, r alice]]
  bank ← signed "close into itself" bank #[key "alice"] #[proof close #[w stored, w stored, rs alice]]
  bank ← signed "close with too few accounts" bank nobody #[proof close #[w stored, w alice]]
  bank ← signed "close an account that stores nothing" bank #[key "alice"] #[proof close #[w blank, w alice, rs alice]]
  bank ← signed "close an account of another program" bank #[key "alice"] #[proof close #[w held, w alice, rs alice]]
  bank ← signed "close into a read-only account" bank #[key "alice"] #[proof close #[w stored, r held, rs alice]]
  bank ← signed "the authority closes it" bank #[key "alice"] #[proof close #[w stored, w alice, rs alice]]
  showAccount bank "stored" stored
  bank ← signed "the payer closes the other, to alice" bank nobody #[proof close #[w third, w alice, rs payer]]
  showAccount bank "third" third
