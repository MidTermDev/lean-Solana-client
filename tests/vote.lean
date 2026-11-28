import Solana.Bank

/-! What is left of the vote program now that votes are not transactions:
setting a vote account up, naming new voters (under Alpenglow with a BLS key
and a proof of holding it) and withdrawers, a new node, commissions and who
collects them, withdrawals, and accounts still in the layouts of before,
which are read as they are and brought up to date when changed.

`oracle-next vote` runs the same transactions on Agave, with the features
mainnet has switched on; `make oracle` requires the two reports to be
identical. -/

def key (name : String) : ByteArray := Sha256.hash name.toUTF8
def u64le (v : UInt64) : ByteArray := Wire.putU64 (ByteArray.emptyWithCapacity 8) v
def u32le (v : UInt64) : ByteArray := Wire.putU32 (ByteArray.emptyWithCapacity 4) v
def u16le (v : UInt64) : ByteArray := Wire.putU16 (ByteArray.emptyWithCapacity 2) v
def byte (v : UInt8) : ByteArray := ByteArray.empty.push v
def address (text : String) : ByteArray := Base58.decode text
def text (s : String) : ByteArray := u64le s.toUTF8.size.toUInt64 ++ s.toUTF8

def system : ByteArray := Sbpf.systemProgram
def program : ByteArray := Sbpf.voteProgram
def rent : ByteArray := address "SysvarRent111111111111111111111111111111111"
def clock : ByteArray := address "SysvarC1ock11111111111111111111111111111111"

def w (k : ByteArray) : Tx.Key := ⟨k, false, true⟩
def ws (k : ByteArray) : Tx.Key := ⟨k, true, true⟩
def r (k : ByteArray) : Tx.Key := ⟨k, false, false⟩
def rs (k : ByteArray) : Tx.Key := ⟨k, true, false⟩

def ix (tag : UInt64) (fields : ByteArray) (accounts : Array Tx.Key) : Tx.Instruction := ⟨program, accounts, u32le tag ++ fields⟩

def transfer (source dest : ByteArray) (lamports : UInt64) : Tx.Instruction :=
  ⟨system, #[ws source, w dest], u32le 2 ++ u64le lamports⟩

def createAccount (source fresh : ByteArray) (lamports space : UInt64) (owner : ByteArray) : Tx.Instruction :=
  ⟨system, #[ws source, ws fresh], u32le 0 ++ u64le lamports ++ u64le space ++ owner⟩

def unitLimit (units : UInt64) : Tx.Instruction := ⟨Sbpf.computeBudgetProgram, #[], byte 2 ++ u32le units⟩

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

/-- A BLS key and the proof that its holder has the secret, for a vote account. -/
def bls (secret : UInt64) (account : ByteArray) : ByteArray :=
  let words : Array UInt64 := #[secret, 0, 0, 0]
  let blsKey := (Bls12381.generator.scale words).toBytes false
  blsKey ++ ((Bls12381.hashToCurve ("ALPENGLOW".toUTF8 ++ account ++ blsKey) Alpenglow.proofDomain).scale words).toBytes true

/-- A vote account as accounts were laid out before the present layout: 2 is the one before, 1 the one
before that (votes of 12 bytes, 31 bytes shorter). -/
def older (layout : UInt64) (node withdrawer voter : ByteArray) : ByteArray := Id.run do
  let mut d := (u32le layout ++ node ++ withdrawer).push 9
  d := d ++ u64le 2
  for slot in [100:102] do
    if layout == 2 then
      d := d.push 1
    d := d ++ u64le slot.toUInt64 ++ u32le (102 - slot).toUInt64
  d := d.push 1 ++ u64le 99 ++ u64le 1 ++ u64le 3 ++ voter
  d := (Fast.pushZeros d 1536 ++ u64le 31).push 1
  d := d ++ u64le 2 ++ u64le 3 ++ u64le 500 ++ u64le 0 ++ u64le 4 ++ u64le 900 ++ u64le 500
  d := d ++ u64le 101 ++ u64le 1700000000
  return Fast.pushZeros d ((if layout == 1 then 3731 else 3762) - d.size)

def changed (b : ByteArray) (i : Nat) : ByteArray := b.set! i (b[i]! ^^^ 1)

def nobody : Array ByteArray := Array.emptyWithCapacity 0
def none_ : Array Tx.Key := Array.emptyWithCapacity 0

def main : IO Unit := do
  let payer := Ed25519.publicKey (key "payer")
  let alice := Ed25519.publicKey (key "alice")
  let node := Ed25519.publicKey (key "node")
  let voter := Ed25519.publicKey (key "voter")
  let withdrawer := Ed25519.publicKey (key "withdrawer")
  let vote := Ed25519.publicKey (key "vote")
  let second := Ed25519.publicKey (key "second")
  let next := Ed25519.publicKey (key "next")
  let otherNode := Ed25519.publicKey (key "other node")
  let poor := key "poor"
  let rich := key "rich"
  let old := key "old"
  let olderStill := key "older still"
  let shortOfRent := key "short of rent"
  let blockhash := address "CmpNeggWJ4JaWJeJ8YKN1Zypmk7uvQq3PECGUCAEMbky"
  let mut bank := ((Bank.create ⟨0, 0, 0, 0, 0⟩).withBlockhash blockhash).withClock ⟨0, 0, 5, 6, 0⟩
  bank := bank.set ⟨payer, system, 10000000000, ByteArray.empty, false⟩
  bank := bank.set ⟨alice, system, 2000000000, ByteArray.empty, false⟩
  bank := bank.set ⟨poor, system, 500000, ByteArray.empty, false⟩
  bank := bank.set ⟨rich, system, 5000000, ByteArray.empty, false⟩
  -- three accounts nobody has touched since the layouts before the present one
  bank := bank.set ⟨old, program, 30000000, older 2 node withdrawer voter, false⟩
  bank := bank.set ⟨olderStill, program, 30000000, older 1 node withdrawer voter, false⟩
  bank := bank.set ⟨shortOfRent, program, 26858640, older 1 node withdrawer voter, false⟩
  IO.println s!"blockhash {Base58.encode blockhash}"
  let size : UInt64 := 3762
  let rentForIt : UInt64 := 27074400
  let init := node ++ voter ++ withdrawer ++ byte 7

  -- --- setting a vote account up: the node it votes for must sign
  bank ← signed "set up a vote account" bank #[key "vote", key "node"] #[createAccount payer vote rentForIt size program,
    ix 0 init #[w vote, r rent, r clock, rs node]]
  showAccount bank "vote" vote
  bank ← signed "set it up again" bank #[key "node"] #[ix 0 (node ++ voter ++ withdrawer ++ byte 8) #[w vote, r rent, r clock, rs node]]
  bank ← signed "set one up without the node signing" bank #[key "second"] #[createAccount payer second rentForIt size program,
    ix 0 init #[w second, r rent, r clock, r node]]
  bank ← signed "an account a byte too small" bank #[key "second", key "node"] #[createAccount payer second rentForIt (size - 1) program,
    ix 0 init #[w second, r rent, r clock, rs node]]
  bank ← signed "an account a lamport short of its rent" bank #[key "second", key "node"] #[createAccount payer second (rentForIt - 1) size program,
    ix 0 init #[w second, r rent, r clock, rs node]]
  bank ← signed "the clock where the rent should be" bank #[key "second", key "node"] #[createAccount payer second rentForIt size program,
    ix 0 init #[w second, r clock, r clock, rs node]]
  bank ← signed "no clock" bank #[key "second"] #[createAccount payer second rentForIt size program, ix 0 init #[w second, r rent]]
  bank ← signed "no accounts at all" bank nobody #[ix 0 init none_]
  bank ← signed "an account of another program" bank nobody #[ix 5 (byte 1) #[w alice]]
  bank ← signed "data cut short" bank #[key "node"] #[ix 0 (init.extract 0 96) #[w vote, r rent, r clock, rs node]]

  -- --- a new withdrawer, a new voter
  bank ← signed "the withdrawer names alice withdrawer" bank #[key "withdrawer"] #[ix 1 (alice ++ u32le 1) #[w vote, r clock, rs withdrawer]]
  showAccount bank "vote" vote
  bank ← signed "the old withdrawer tries again" bank #[key "withdrawer"] #[ix 1 (withdrawer ++ u32le 1) #[w vote, r clock, rs withdrawer]]
  bank ← signed "the voter names the next voter" bank #[key "voter"] #[ix 1 (next ++ u32le 0) #[w vote, r clock, rs voter]]
  showAccount bank "vote" vote
  bank ← signed "and another for the same epoch" bank #[key "voter"] #[ix 1 (node ++ u32le 0) #[w vote, r clock, rs voter]]
  bank ← signed "someone else names a voter" bank #[key "node"] #[ix 1 (node ++ u32le 0) #[w vote, r clock, rs node]]
  bank ← signed "a kind of authority there is not" bank #[key "voter"] #[ix 1 (node ++ u32le 3) #[w vote, r clock, rs voter]]
  bank ← signed "no clock for it" bank nobody #[ix 1 (node ++ u32le 0) #[w vote]]
  bank ← signed "the rent where the clock should be" bank #[key "voter"] #[ix 1 (node ++ u32le 0) #[w vote, r rent, rs voter]]
  bank := bank.withClock ⟨0, 0, 8, 9, 0⟩
  bank ← signed "three epochs on, the old voter names one" bank #[key "voter"] #[ix 1 (alice ++ u32le 0) #[w vote, r clock, rs voter]]
  bank ← signed "the next voter does" bank #[key "next"] #[ix 1 (voter ++ u32le 0) #[w vote, r clock, rs next]]
  showAccount bank "vote" vote

  -- --- a voter with a BLS key: the key comes with a proof that its holder has the secret
  bank ← signed "a proof made for another account" bank #[key "alice"] #[ix 1 (node ++ u32le 2 ++ bls 77 second) #[w vote, r clock, rs alice]]
  bank ← signed "a proof with a bit changed" bank #[key "alice"] #[ix 1 (node ++ u32le 2 ++ changed (bls 77 vote) 140) #[w vote, r clock, rs alice]]
  bank ← signed "a key that is no point" bank #[key "alice"] #[ix 1 (node ++ u32le 2 ++ changed (bls 77 vote) 1) #[w vote, r clock, rs alice]]
  bank ← signed "a key and proof on too small a budget" bank #[key "alice"] #[unitLimit 30000, ix 1 (node ++ u32le 2 ++ bls 77 vote) #[w vote, r clock, rs alice]]
  bank ← signed "the epoch after next is taken" bank #[key "alice"] #[ix 1 (node ++ u32le 2 ++ bls 76 vote) #[w vote, r clock, rs alice]]
  bank := bank.withClock ⟨0, 0, 9, 10, 0⟩
  bank ← signed "an epoch later, a voter with a BLS key" bank #[key "alice"] #[ix 1 (node ++ u32le 2 ++ bls 77 vote) #[w vote, r clock, rs alice]]
  showAccount bank "vote" vote
  bank := bank.withClock ⟨0, 0, 12, 13, 0⟩
  bank ← signed "now a voter without one is refused" bank #[key "alice"] #[ix 1 (next ++ u32le 0) #[w vote, r clock, rs alice]]
  bank ← signed "another key replaces it, by the voter" bank #[key "node"] #[ix 1 (next ++ u32le 2 ++ bls 78 vote) #[w vote, r clock, rs node]]
  showAccount bank "vote" vote

  -- --- where the new authority must sign too
  bank ← signed "a withdrawer who signs for it" bank #[key "alice", key "withdrawer"] #[ix 7 (u32le 1) #[w vote, r clock, rs alice, rs withdrawer]]
  bank ← signed "one who does not" bank #[key "withdrawer"] #[ix 7 (u32le 1) #[w vote, r clock, rs withdrawer, r alice]]
  bank ← signed "too few accounts for it" bank #[key "withdrawer"] #[ix 7 (u32le 1) #[w vote, r clock, rs withdrawer]]

  -- --- an authority that is an address derived from a base key and a seed
  let derived := Sha256.hash (payer ++ "treasury".toUTF8 ++ system)
  bank ← signed "the withdrawer names a derived address" bank #[key "withdrawer"] #[ix 1 (derived ++ u32le 1) #[w vote, r clock, rs withdrawer]]
  bank ← signed "the wrong seed" bank nobody #[ix 10 (u32le 1 ++ system ++ text "treasure" ++ alice) #[w vote, r clock, rs payer]]
  bank ← signed "a seed too long" bank nobody #[ix 10 (u32le 1 ++ system ++ text "a seed that is much longer than is allowed" ++ alice) #[w vote, r clock, rs payer]]
  bank ← signed "the base does not sign" bank nobody #[transfer payer alice 1, ix 10 (u32le 1 ++ system ++ text "treasury" ++ alice) #[w vote, r clock, r alice]]
  bank ← signed "the base signs: alice is withdrawer again" bank nobody #[ix 10 (u32le 1 ++ system ++ text "treasury" ++ alice) #[w vote, r clock, rs payer]]
  bank ← signed "back to the derived address" bank #[key "alice"] #[ix 1 (derived ++ u32le 1) #[w vote, r clock, rs alice]]
  bank ← signed "derived, and the new one signs" bank #[key "withdrawer"] #[ix 11 (u32le 1 ++ system ++ text "treasury") #[w vote, r clock, rs payer, rs withdrawer]]
  showAccount bank "vote" vote

  -- --- a new node; commissions and who collects them
  bank ← signed "a new node, which must sign" bank #[key "withdrawer"] #[ix 4 ByteArray.empty #[w vote, r otherNode, rs withdrawer]]
  bank ← signed "it signs, the withdrawer does not" bank #[key "other node"] #[ix 4 ByteArray.empty #[w vote, rs otherNode, r withdrawer]]
  bank ← signed "both sign" bank #[key "withdrawer", key "other node"] #[ix 4 ByteArray.empty #[w vote, rs otherNode, rs withdrawer]]
  bank ← signed "no node named" bank nobody #[ix 4 ByteArray.empty #[w vote]]
  bank ← signed "a commission of 10 percent" bank #[key "withdrawer"] #[ix 5 (byte 10) #[w vote, rs withdrawer]]
  bank ← signed "without the withdrawer" bank nobody #[ix 5 (byte 11) #[w vote, r withdrawer]]
  bank ← signed "a commission of 12.34 percent" bank #[key "withdrawer"] #[ix 18 (u16le 1234 ++ u32le 0) #[w vote, rs withdrawer]]
  bank ← signed "a commission on block fees" bank #[key "withdrawer"] #[ix 18 (u16le 1234 ++ u32le 1) #[w vote, rs withdrawer]]
  showAccount bank "vote" vote
  bank ← signed "alice collects the rewards' commission" bank #[key "withdrawer"] #[ix 17 (u32le 0) #[w vote, w alice, rs withdrawer]]
  bank ← signed "and the block fees" bank #[key "withdrawer"] #[ix 17 (u32le 1) #[w vote, w alice, rs withdrawer]]
  bank ← signed "a collector passed read-only" bank #[key "withdrawer"] #[ix 17 (u32le 0) #[w vote, r rich, rs withdrawer]]
  bank ← signed "a collector that is not a plain account" bank #[key "withdrawer"] #[ix 17 (u32le 0) #[w vote, w old, rs withdrawer]]
  bank ← signed "a collector that could not pay its rent" bank #[key "withdrawer"] #[ix 17 (u32le 0) #[w vote, w poor, rs withdrawer]]
  bank ← signed "the account itself collects" bank #[key "withdrawer"] #[ix 17 (u32le 0) #[w vote, w vote, rs withdrawer]]
  showAccount bank "vote" vote

  -- --- accounts in the layouts before: withdrawn from as they are, brought up to date when changed
  bank ← signed "withdraw from an account in the old layout" bank #[key "withdrawer"] #[ix 3 (u64le 1000000) #[w old, w alice, rs withdrawer]]
  showAccount bank "old" old
  bank ← signed "withdraw below its rent" bank #[key "withdrawer"] #[ix 3 (u64le 2000000) #[w old, w alice, rs withdrawer]]
  bank ← signed "change its commission" bank #[key "withdrawer"] #[ix 5 (byte 20) #[w old, rs withdrawer]]
  showAccount bank "old" old
  bank ← signed "give the older one a voter" bank #[key "voter"] #[ix 1 (next ++ u32le 0) #[w olderStill, r clock, rs voter]]
  showAccount bank "older still" olderStill
  bank ← signed "one that cannot pay for growing" bank #[key "withdrawer"] #[ix 5 (byte 20) #[w shortOfRent, rs withdrawer]]
  bank := bank.withClock ⟨0, 0, 5, 6, 0⟩
  bank ← signed "empty an account whose credits are fresh" bank #[key "withdrawer"] #[ix 3 (u64le 26858640) #[w shortOfRent, w alice, rs withdrawer]]
  bank := bank.withClock ⟨0, 0, 12, 13, 0⟩
  bank ← signed "withdraw more than there is" bank #[key "withdrawer"] #[ix 3 (u64le 26858641) #[w shortOfRent, w alice, rs withdrawer]]
  bank ← signed "withdraw without the withdrawer" bank nobody #[ix 3 (u64le 1) #[w old, w alice, r withdrawer]]
  bank ← signed "withdraw to nowhere" bank nobody #[ix 3 (u64le 1) #[w old]]
  bank ← signed "empty it, its credits long past" bank #[key "withdrawer"] #[transfer payer alice 2, ix 3 (u64le 26858640) #[w shortOfRent, w alice, rs withdrawer]]
  showAccount bank "short of rent" shortOfRent

  -- --- what the program no longer does
  bank ← signed "a vote, as votes were sent" bank #[key "voter"] #[ix 2 (u64le 1 ++ u64le 100 ++ Fast.pushZeros ByteArray.empty 32 ++ byte 0) #[w vote, r clock, r clock, rs voter]]
  bank ← signed "setting up the newer way" bank nobody #[ix 16 (Fast.pushZeros ByteArray.empty 244) #[w vote, rs payer, w alice, w alice]]
  bank ← signed "a deposit for delegators" bank nobody #[ix 19 (u64le 5) #[w vote, ws payer]]
  bank ← signed "an instruction there is not" bank nobody #[ix 20 ByteArray.empty #[w vote]]
