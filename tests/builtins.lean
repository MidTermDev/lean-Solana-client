import Solana.Bank

/-! The programs every chain starts with.

Some are native code in the validator and are written here in Lean: the
system program, with its seed-derived addresses and its nonce accounts. Some
used to be native and are bytecode today, and run here from the files in
`programs/` exactly as they run on mainnet: config, address lookup tables,
stake.

`tests/oracle` runs the same transactions on Agave; `make oracle` requires
the two reports to be identical. -/

def key (name : String) : ByteArray := Sha256.hash name.toUTF8
def u64le (v : UInt64) : ByteArray := Wire.putU64 (ByteArray.emptyWithCapacity 8) v
def u32le (v : UInt64) : ByteArray := Wire.putU32 (ByteArray.emptyWithCapacity 4) v
def address (text : String) : ByteArray := Base58.decode text

def system : ByteArray := Sbpf.systemProgram
def config : ByteArray := address "Config1111111111111111111111111111111111111"
def lookupTable : ByteArray := address "AddressLookupTab1e1111111111111111111111111"
def stakeProgram : ByteArray := address "Stake11111111111111111111111111111111111111"
def recentBlockhashes : ByteArray := address "SysvarRecentB1ockHashes11111111111111111111"
def rent : ByteArray := address "SysvarRent111111111111111111111111111111111"
def clock : ByteArray := address "SysvarC1ock11111111111111111111111111111111"
def stakeHistory : ByteArray := address "SysvarStakeHistory1111111111111111111111111"

-- how an instruction refers to an account: writable or read-only, signing or not
def w (k : ByteArray) : Tx.Key := ⟨k, false, true⟩
def ws (k : ByteArray) : Tx.Key := ⟨k, true, true⟩
def r (k : ByteArray) : Tx.Key := ⟨k, false, false⟩
def rs (k : ByteArray) : Tx.Key := ⟨k, true, false⟩

/-- An instruction whose data is a 32-bit tag followed by `fields`. -/
def tagged (program : ByteArray) (tag : UInt64) (fields : ByteArray) (accounts : Array Tx.Key) : Tx.Instruction :=
  ⟨program, accounts, u32le tag ++ fields⟩

/-- A string as bincode writes it: its length in 8 bytes, then its bytes. -/
def text (s : String) : ByteArray := u64le s.toUTF8.size.toUInt64 ++ s.toUTF8

def transfer (source dest : ByteArray) (lamports : UInt64) : Tx.Instruction :=
  tagged system 2 (u64le lamports) #[ws source, w dest]

def createAccount (source fresh : ByteArray) (lamports space : UInt64) (owner : ByteArray) : Tx.Instruction :=
  tagged system 0 (u64le lamports ++ u64le space ++ owner) #[ws source, ws fresh]

def send (label : String) (bank : Bank.Bank) (tx : Tx.Transaction) : IO Bank.Bank := do
  let result := bank.process (Tx.parse tx.serialize) true
  IO.println s!"{label}: {if result.error == "" then "success" else result.error}, fee {result.fee}, {result.units} units"
  IO.println s!"  signature {Base58.encode tx.signatures[0]!}"
  for line in result.logs do
    IO.println s!"  log: {line}"
  let payer := Ed25519.publicKey (key "payer")
  let alice := Ed25519.publicKey (key "alice")
  IO.println s!"  payer {(result.bank.get payer).lamports}, alice {(result.bank.get alice).lamports}"
  return result.bank

/-- A transaction paid for by the usual payer and signed by it and by the holders of `seeds`. -/
def signed (label : String) (bank : Bank.Bank) (seeds : Array ByteArray) (instructions : Array Tx.Instruction) : IO Bank.Bank :=
  send label bank (Tx.sign (Tx.compile (Ed25519.publicKey (key "payer")) instructions bank.blockhash) (seeds.push (key "payer")))

/-- One line describing an account: balance, size, owner and a hash of its data. -/
def showAccount (bank : Bank.Bank) (name : String) (k : ByteArray) : IO Unit := do
  let a := bank.get k
  if a.lamports == 0 then
    IO.println s!"  {name}: no such account"
  else
    IO.println s!"  {name}: {a.lamports} lamports, {a.data.size} bytes, owner {Base58.encode a.owner}, data {Base58.encode (Sha256.hash a.data)}"

def withdrawStake (stake dest : ByteArray) (amount : UInt64) (signer : ByteArray) : Tx.Instruction :=
  tagged stakeProgram 4 (u64le amount) #[w stake, w dest, r clock, r stakeHistory, rs signer]

def nobody : Array ByteArray := Array.emptyWithCapacity 0

def main : IO Unit := do
  let payer := Ed25519.publicKey (key "payer")
  let alice := Ed25519.publicKey (key "alice")
  let mut blockhash := address "CmpNeggWJ4JaWJeJ8YKN1Zypmk7uvQq3PECGUCAEMbky"
  let mut bank := (Bank.create ⟨0, 0, 0, 0, 0⟩).withBlockhash blockhash
  bank := bank.addProgram config (Sbpf.load (← IO.FS.readBinFile "programs/Config1111111111111111111111111111111111111.so"))
  bank := bank.addProgram lookupTable (Sbpf.load (← IO.FS.readBinFile "programs/AddressLookupTab1e1111111111111111111111111.so"))
  bank := bank.addProgram stakeProgram (Sbpf.load (← IO.FS.readBinFile "programs/Stake11111111111111111111111111111111111111.so"))
  bank := bank.set ⟨payer, system, 10000000000, ByteArray.empty, false⟩
  bank := bank.set ⟨alice, system, 2000000000, ByteArray.empty, false⟩
  IO.println s!"blockhash {Base58.encode blockhash}"

  -- --- the system program: addresses derived from a base key and a seed
  let vault := Sha256.hash (payer ++ "vault".toUTF8 ++ system)
  bank ← signed "create an account at a seed-derived address" bank nobody #[tagged system 3
    (payer ++ text "vault" ++ u64le 1000000000 ++ u64le 0 ++ system) #[ws payer, w vault]]
  showAccount bank "vault" vault
  bank ← signed "transfer out of it, signed by the base" bank nobody #[tagged system 11
    (u64le 250000000 ++ text "vault" ++ system) #[w vault, rs payer, w alice]]
  showAccount bank "vault" vault
  bank ← signed "transfer with the wrong seed" bank nobody #[tagged system 11
    (u64le 1 ++ text "vaults" ++ system) #[w vault, rs payer, w alice]]
  let ledger := Sha256.hash (payer ++ "ledger".toUTF8 ++ config)
  bank ← signed "fund, allocate and assign a seed-derived address" bank nobody #[transfer payer ledger 1447680,
    tagged system 9 (payer ++ text "ledger" ++ u64le 80 ++ config) #[w ledger, rs payer],
    tagged system 10 (payer ++ text "ledger" ++ config) #[w ledger, rs payer]]
  showAccount bank "ledger" ledger
  bank ← signed "a seed longer than 32 bytes" bank nobody #[tagged system 9
    (payer ++ text "a seed that is much longer than is allowed" ++ u64le 80 ++ config) #[w ledger, rs payer]]

  -- --- the system program: nonce accounts
  let nonce := Ed25519.publicKey (key "nonce")
  bank ← signed "create a nonce account" bank #[key "nonce"] #[createAccount payer nonce 2000000 80 system,
    tagged system 6 payer #[w nonce, r recentBlockhashes, r rent]]
  showAccount bank "nonce" nonce
  bank ← signed "initialize it again" bank nobody #[tagged system 6 alice #[w nonce, r recentBlockhashes, r rent]]
  bank ← signed "advance it before the blockhash changed" bank nobody #[tagged system 4 ByteArray.empty #[w nonce, r recentBlockhashes, rs payer]]
  bank ← signed "give it to alice" bank nobody #[tagged system 7 alice #[w nonce, rs payer]]
  showAccount bank "nonce" nonce
  bank ← signed "the old authority tries to advance it" bank nobody #[transfer payer alice 1,
    tagged system 4 ByteArray.empty #[w nonce, r recentBlockhashes, rs payer]]
  bank ← signed "alice withdraws a little" bank #[key "alice"] #[tagged system 5 (u64le 100000)
    #[w nonce, w alice, r recentBlockhashes, r rent, rs alice]]
  bank ← signed "alice withdraws too much" bank #[key "alice"] #[tagged system 5 (u64le 500000)
    #[w nonce, w alice, r recentBlockhashes, r rent, rs alice]]
  -- time passes: a new blockhash
  blockhash := Sha256.hash blockhash
  bank := bank.withBlockhash blockhash
  IO.println s!"blockhash {Base58.encode blockhash}"
  bank ← signed "advance it after the blockhash changed" bank #[key "alice"] #[tagged system 4 ByteArray.empty #[w nonce, r recentBlockhashes, rs alice]]
  showAccount bank "nonce" nonce
  bank ← signed "advance it twice" bank #[key "alice"] #[transfer payer alice 2,
    tagged system 4 ByteArray.empty #[w nonce, r recentBlockhashes, rs alice]]
  bank ← signed "close it while its nonce is current" bank #[key "alice"] #[tagged system 5 (u64le 1900000)
    #[w nonce, w alice, r recentBlockhashes, r rent, rs alice]]
  showAccount bank "nonce" nonce

  -- --- the config program (bytecode): a record with a list of keys that must sign changes to it
  let record := Ed25519.publicKey (key "record")
  let store := ((ByteArray.empty.push 1) ++ alice).push 1 ++ "what the record says".toUTF8
  bank ← signed "create a config record" bank #[key "record", key "alice"] #[createAccount payer record 1670400 112 config,
    ⟨config, #[ws record, rs alice], store⟩]
  showAccount bank "record" record
  let changed := store.set! 40 87
  bank ← signed "change it without the key it names" bank #[key "record"] #[⟨config, #[ws record], changed⟩]
  bank ← signed "change it with that key" bank #[key "alice"] #[⟨config, #[w record, rs alice], changed⟩]
  showAccount bank "record" record

  -- --- address lookup tables (bytecode): create one, add addresses, then use it in a version 0 transaction
  let (table, bump) := Sbpf.findProgramAddress #[payer, u64le 0] lookupTable
  let carol := key "carol"
  let dave := key "dave"
  bank ← signed "create a lookup table" bank nobody #[tagged lookupTable 0 ((u64le 0).push bump) #[w table, r payer, ws payer, r system]]
  showAccount bank "table" table
  bank ← signed "add two addresses to it" bank nobody #[tagged lookupTable 2 (u64le 2 ++ carol ++ dave) #[w table, rs payer, ws payer, r system]]
  showAccount bank "table" table
  -- a version 0 message: its own keys are the payer and the system program; dave is entry 1 of the table, writable
  let lookup : Tx.Lookup := ⟨table, ByteArray.empty.push 1, ByteArray.empty⟩
  let pay : Tx.Compiled := ⟨1, (ByteArray.empty.push 0).push 2, u32le 2 ++ u64le 1000000000⟩
  bank ← send "pay an address through the table in the slot it was added" bank
    (Tx.sign ⟨true, 1, 0, 1, #[payer, system], blockhash, #[pay], #[lookup]⟩ #[key "payer"])
  bank := bank.withClock ⟨1, 0, 0, 0, 0⟩
  bank ← send "pay it through the table one slot later" bank
    (Tx.sign ⟨true, 1, 0, 1, #[payer, system], blockhash, #[{ pay with data := u32le 2 ++ u64le 1000000001 }], #[lookup]⟩ #[key "payer"])
  showAccount bank "dave" dave
  bank ← signed "freeze the table" bank nobody #[tagged lookupTable 1 ByteArray.empty #[w table, rs payer]]
  bank ← signed "add to the frozen table" bank nobody #[tagged lookupTable 2 (u64le 1 ++ alice) #[w table, rs payer, ws payer, r system]]
  showAccount bank "table" table

  -- --- the stake program (bytecode): a stake account is created, handed over, split and drawn down
  let stake := Ed25519.publicKey (key "stake")
  let half := Ed25519.publicKey (key "half")
  let noLockup := Sbpf.zeros ByteArray.empty 48
  bank ← signed "create a stake account" bank #[key "stake"] #[createAccount payer stake 3000000000 200 stakeProgram,
    tagged stakeProgram 0 (payer ++ payer ++ noLockup) #[w stake, r rent]]
  showAccount bank "stake" stake
  bank ← signed "initialize it again" bank nobody #[tagged stakeProgram 0 (alice ++ alice ++ noLockup) #[w stake, r rent]]
  bank ← signed "make alice the withdrawer" bank nobody #[tagged stakeProgram 1 (alice ++ u32le 1) #[w stake, r clock, rs payer]]
  showAccount bank "stake" stake
  bank ← signed "split off a third" bank #[key "half"] #[createAccount payer half 2282880 200 stakeProgram,
    tagged stakeProgram 3 (u64le 1000000000) #[w stake, w half, rs payer]]
  showAccount bank "stake" stake
  showAccount bank "the split" half
  bank ← signed "the old withdrawer tries to withdraw" bank nobody #[withdrawStake stake alice 500000000 payer]
  bank ← signed "alice withdraws" bank #[key "alice"] #[withdrawStake stake alice 500000000 alice]
  showAccount bank "stake" stake
  bank ← signed "alice withdraws below the reserve" bank #[key "alice"] #[withdrawStake stake alice 1499000000 alice]
