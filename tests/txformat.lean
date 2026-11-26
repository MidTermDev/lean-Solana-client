import Solana.Bank

/-! The transaction wire format: round trips, version 0 messages that take
accounts from an address lookup table, and a parser that must survive
whatever it is given. -/

def key (name : String) : ByteArray := Sha256.hash name.toUTF8

def transfer (source dest : ByteArray) (lamports : UInt64) : Tx.Instruction :=
  ⟨Sbpf.systemProgram, #[⟨source, true, true⟩, ⟨dest, false, true⟩], Wire.putU64 (Wire.putU32 ByteArray.empty 2) lamports⟩

def report (label : String) (r : Bank.Receipt) : IO Unit :=
  IO.println s!"{label}: {if r.error == "" then "success" else r.error}, fee {r.fee}, charged {r.charged}"

def main : IO Unit := do
  let payer := Ed25519.publicKey (key "payer")
  let alice := Ed25519.publicKey (key "alice")
  let carol := Ed25519.publicKey (key "carol")
  let blockhash := key "blockhash"
  let mut bank := ((Bank.create ⟨0, 0, 0, 0, 0⟩).withBlockhash blockhash).set ⟨payer, Sbpf.systemProgram, 5000000000, ByteArray.empty, false⟩

  -- a legacy message: keys are ordered by role, then by address, and survive a round trip
  let msg := Tx.compile payer #[transfer payer alice 1000000000, transfer payer carol 2000000000] blockhash
  IO.println s!"legacy: {msg.keys.size} keys, {msg.signers} signer, {msg.readonlySigned} read-only signer, {msg.readonlyUnsigned} read-only other"
  IO.println s!"  writable keys in address order: {Tx.before msg.keys[1]! msg.keys[2]!}; the program is last: {msg.keys[3]! == Sbpf.systemProgram}"
  let tx := Tx.sign msg #[key "payer"]
  let bytes := tx.serialize
  let back := Tx.parse bytes
  IO.println s!"  {bytes.size} bytes; parses: {back.error == ""}; same bytes again: {back.serialize == bytes}; verifies: {back.verify}"
  IO.println s!"  signed by someone else verifies: {(Tx.sign msg #[key "mallory"]).verify}"
  let r := bank.process back true
  report "  applied" r
  IO.println s!"  alice {(r.bank.get alice).lamports}, carol {(r.bank.get carol).lamports}, payer {(r.bank.get payer).lamports}"
  -- a transaction naming another blockhash is refused
  report "  with a stale blockhash" (bank.process (Tx.sign (Tx.compile payer #[transfer payer alice 1] (key "old")) #[key "payer"]) true)

  -- a version 0 message: two of its accounts come from a table stored on chain
  let table := key "table"
  let tableData := Sbpf.zeros ByteArray.empty 56 ++ carol ++ alice
  bank := bank.set ⟨table, Bank.lookupTableProgram, 1000000, tableData, false⟩
  let data := Wire.putU64 (Wire.putU32 ByteArray.empty 2) 1500000000
  -- keys: payer, system program; from the table: entry 1 (alice) writable, entry 0 (carol) read-only
  let lookup : Tx.Lookup := ⟨table, ByteArray.empty.push 1, ByteArray.empty.push 0⟩
  let toAlice : Tx.Compiled := ⟨1, (ByteArray.empty.push 0).push 2, data⟩
  let v0 : Tx.Message := ⟨true, 1, 0, 1, #[payer, Sbpf.systemProgram], blockhash, #[toAlice], #[lookup]⟩
  let tx0 := Tx.sign v0 #[key "payer"]
  let back0 := Tx.parse tx0.serialize
  IO.println s!"version 0: {tx0.serialize.size} bytes; parses: {back0.error == ""}; versioned: {back0.message.versioned}; lookups: {back0.message.lookups.size}; same bytes again: {back0.serialize == tx0.serialize}"
  let r := bank.process back0 true
  report "  transfer to a table account" r
  IO.println s!"  alice {(r.bank.get alice).lamports}"
  -- the read-only table entry cannot be paid into
  let toCarol : Tx.Compiled := ⟨1, (ByteArray.empty.push 0).push 3, data⟩
  let v0ro : Tx.Message := ⟨true, 1, 0, 1, #[payer, Sbpf.systemProgram], blockhash, #[toCarol], #[lookup]⟩
  let r := bank.process (Tx.sign v0ro #[key "payer"]) true
  report "  transfer to a read-only table account" r
  IO.println s!"  carol {(r.bank.get carol).lamports}, payer {(r.bank.get payer).lamports}"
  -- a table that is not there, and an entry that is not in the table
  let missing : Tx.Lookup := ⟨key "no table", ByteArray.empty.push 1, ByteArray.empty⟩
  report "  missing table" (bank.process (Tx.sign { v0 with lookups := #[missing] } #[key "payer"]) true)
  let beyond : Tx.Lookup := ⟨table, ByteArray.empty.push 2, ByteArray.empty⟩
  report "  entry beyond the table" (bank.process (Tx.sign { v0 with lookups := #[beyond] } #[key "payer"]) true)
  -- the same account twice
  let twice : Tx.Lookup := ⟨table, (ByteArray.empty.push 1).push 1, ByteArray.empty⟩
  report "  the same account twice" (bank.process (Tx.sign { v0 with lookups := #[twice] } #[key "payer"]) true)

  -- hostile input: truncations, single-byte corruptions and noise must be refused or fail cleanly, never crash
  let mut parsed := 0
  let mut verified := 0
  let mut applied := 0
  let mut seed := key "fuzz"
  for round in [0:600] do
    seed := Sha256.hash seed
    let source := if round % 2 == 0 then bytes else tx0.serialize
    let mut input := source
    let kind := seed[0]!.toNat % 4
    if kind == 0 then
      input := source.extract 0 ((Wire.u16 seed 1).toNat % source.size)
    else if kind == 1 then
      let at_ := (Wire.u16 seed 1).toNat % source.size
      input := source.set! at_ (source[at_]! ^^^ (seed[3]! ||| 1))
    else if kind == 2 then
      input := source ++ seed.extract 0 (seed[4]!.toNat % 32)
    else
      input := (seed ++ Sha256.hash seed ++ source).extract 0 ((Wire.u16 seed 1).toNat % 300)
    let candidate := Tx.parse input
    if candidate.error == "" then
      parsed := parsed + 1
      if candidate.verify then
        verified := verified + 1
      let r := bank.process candidate true
      if r.error == "" then
        applied := applied + 1
  IO.println s!"fuzz: 600 inputs, {parsed} parsed, {verified} with valid signatures, {applied} applied"
