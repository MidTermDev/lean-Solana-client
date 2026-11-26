import Crypto.Ed25519
import Solana.Wire

/-!
# Transactions

A Solana transaction is a list of signatures and a *message*: the accounts
involved, a recent blockhash, and instructions that refer to those accounts
by position. This file builds messages from instructions, signs them, and
reads and writes the wire format, for both legacy messages and version 0
messages (which can also name accounts through address lookup tables).

Nothing here executes anything; `Solana.Bank` does that.
-/

namespace Tx

/-- An account as an instruction refers to it. -/
structure Key where
  key : ByteArray
  signer : Bool
  writable : Bool
  deriving Inhabited

/-- An instruction as written: which program, on which accounts, with what data. -/
structure Instruction where
  program : ByteArray
  accounts : Array Key
  data : ByteArray
  deriving Inhabited

/-- An instruction as a message stores it: accounts are positions in the
message's list of keys, one byte each. -/
structure Compiled where
  program : Nat
  accounts : ByteArray
  data : ByteArray
  deriving Inhabited

/-- Accounts a version 0 message takes from an on-chain table: the table's
address, and positions in it of the accounts wanted writable and read-only. -/
structure Lookup where
  table : ByteArray
  writable : ByteArray
  readonly : ByteArray
  deriving Inhabited

/-- The signed part of a transaction. The first `signers` keys sign; of
those the last `readonlySigned` are read-only, and of the rest the last
`readonlyUnsigned` are read-only. The first key pays the fee. -/
structure Message where
  versioned : Bool
  signers : Nat
  readonlySigned : Nat
  readonlyUnsigned : Nat
  keys : Array ByteArray
  blockhash : ByteArray
  instructions : Array Compiled
  lookups : Array Lookup
  deriving Inhabited

/-- A transaction. `signed` is the serialized message, the bytes the
signatures are over. `error` is non-empty if it could not be parsed. -/
structure Transaction where
  signatures : Array ByteArray
  message : Message
  signed : ByteArray
  error : String
  deriving Inhabited

-- ------------------------------------------------------------------ building

/-- True when `a` sorts before `b`, comparing bytes from the first. -/
def before (a b : ByteArray) : Bool := Id.run do
  for i in [0:a.size] do
    if i >= b.size then
      return false
    if a[i]! != b[i]! then
      return a[i]! < b[i]!
  return a.size < b.size

def position (keys : Array ByteArray) (key : ByteArray) : Nat := Id.run do
  for i in [0:keys.size] do
    if keys[i]! == key then
      return i
  return keys.size

/-- Compiles instructions into a legacy message with `payer` paying the fee.

Every account mentioned gets one entry, with the strongest rights any
instruction gives it. The order is the one the format requires (writable
signers, read-only signers, writable others, read-only others) and, within
each group, by address, as Solana's own SDK orders them, so that the same
instructions always give the same bytes and therefore the same signature. -/
def compile (payer : ByteArray) (instructions : Array Instruction) (blockhash : ByteArray) : Message := Id.run do
  -- every key once, with bit 0 = signer, bit 1 = writable
  let mut keys : Array ByteArray := #[payer]
  let mut rights : Array UInt64 := #[3]
  for ix in instructions do
    if position keys ix.program == keys.size then
      keys := keys.push ix.program
      rights := rights.push 0
    for a in ix.accounts do
      let bits : UInt64 := (if a.signer then 1 else 0) ||| (if a.writable then 2 else 0)
      let at_ := position keys a.key
      if at_ == keys.size then
        keys := keys.push a.key
        rights := rights.push bits
      else
        rights := rights.set! at_ (rights[at_]! ||| bits)
  -- the payer stays first; the rest are sorted by group, then by address
  let mut order : Array ByteArray := #[payer]
  let mut counts : Array Nat := #[1, 0, 0, 0]
  let groups : Array UInt64 := #[3, 1, 2, 0]
  for g in [0:4] do
    let mut group : Array ByteArray := Array.emptyWithCapacity keys.size
    for i in [1:keys.size] do
      if rights[i]! == groups[g]! then
        -- insertion sort: these lists are short
        group := group.push keys[i]!
        let mut j := group.size - 1
        while j > 0 && before group[j]! group[j - 1]! do
          let moved := group[j]!
          group := group.set! j group[j - 1]!
          group := group.set! (j - 1) moved
          j := j - 1
    counts := counts.set! g (counts[g]! + group.size)
    for key in group do
      order := order.push key
  let mut compiled : Array Compiled := Array.emptyWithCapacity instructions.size
  for ix in instructions do
    let mut indexes := ByteArray.emptyWithCapacity ix.accounts.size
    for a in ix.accounts do
      indexes := indexes.push (position order a.key).toUInt8
    compiled := compiled.push ⟨position order ix.program, indexes, ix.data⟩
  return ⟨false, counts[0]! + counts[1]!, counts[1]!, counts[3]!, order, blockhash, compiled, Array.emptyWithCapacity 0⟩

-- --------------------------------------------------------------- wire format

def Message.serialize (m : Message) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 512
  if m.versioned then
    b := b.push 0x80
  b := ((b.push m.signers.toUInt8).push m.readonlySigned.toUInt8).push m.readonlyUnsigned.toUInt8
  b := Wire.putVarint b m.keys.size.toUInt64
  for key in m.keys do
    b := b ++ key
  b := b ++ m.blockhash
  b := Wire.putVarint b m.instructions.size.toUInt64
  for ix in m.instructions do
    b := b.push ix.program.toUInt8
    b := Wire.putVarint b ix.accounts.size.toUInt64 ++ ix.accounts
    b := Wire.putVarint b ix.data.size.toUInt64 ++ ix.data
  if m.versioned then
    b := Wire.putVarint b m.lookups.size.toUInt64
    for l in m.lookups do
      b := b ++ l.table
      b := Wire.putVarint b l.writable.size.toUInt64 ++ l.writable
      b := Wire.putVarint b l.readonly.size.toUInt64 ++ l.readonly
  return b

def Transaction.serialize (tx : Transaction) : ByteArray := Id.run do
  let mut b := Wire.putVarint (ByteArray.emptyWithCapacity (tx.signed.size + 200)) tx.signatures.size.toUInt64
  for sig in tx.signatures do
    b := b ++ sig
  return b ++ tx.signed

/-- Signs a message. `seeds` are Ed25519 private keys (32-byte seeds), in any
order; each is matched to the signer position holding its public key. A
position with no key gets an all-zero signature, which will not verify. -/
def sign (m : Message) (seeds : Array ByteArray) : Transaction := Id.run do
  let signed := m.serialize
  let mut signatures : Array ByteArray := Array.emptyWithCapacity m.signers
  for i in [0:m.signers] do
    let mut sig := ByteArray.emptyWithCapacity 64
    for seed in seeds do
      let pk := Ed25519.publicKey seed
      if i < m.keys.size && pk == m.keys[i]! then
        sig := Ed25519.sign seed pk signed
    if sig.size != 64 then
      sig := ByteArray.emptyWithCapacity 64
      for _ in [0:64] do
        sig := sig.push 0
    signatures := signatures.push sig
  return ⟨signatures, m, signed, ""⟩

/-- True when every signature is a valid signature of the message by the key in its position. -/
def Transaction.verify (tx : Transaction) : Bool := Id.run do
  if tx.signatures.size != tx.message.signers || tx.signatures.size > tx.message.keys.size then
    return false
  for i in [0:tx.signatures.size] do
    if !(Ed25519.verify tx.message.keys[i]! tx.signatures[i]! tx.signed) then
      return false
  return true

def failed (why : String) : Transaction :=
  ⟨Array.emptyWithCapacity 0, ⟨false, 0, 0, 0, Array.emptyWithCapacity 0, ByteArray.empty, Array.emptyWithCapacity 0,
    Array.emptyWithCapacity 0⟩, ByteArray.empty, why⟩

/-- Reads a short vector of bytes at `o`: a length, then that many bytes.
Returns the offset after it, or `Wire.bad`. -/
def afterBytes (b : ByteArray) (o : Nat) : Nat :=
  Wire.skipN b (Wire.skipVarint b o) (Wire.varint b o) 1

def bytesAt (b : ByteArray) (o : Nat) : ByteArray :=
  let start := Wire.skipVarint b o
  let stop := afterBytes b o
  if Wire.ok stop then b.extract start stop else ByteArray.empty

/-- Parses a serialized transaction. Every length comes from the input and is checked against it. -/
def parse (b : ByteArray) : Transaction := Id.run do
  let count := Wire.varint b 0
  let mut o := Wire.skipN b (Wire.skipVarint b 0) count 64
  if !(Wire.ok o) || count == 0 then
    return failed "the signatures are truncated"
  let mut signatures : Array ByteArray := Array.emptyWithCapacity count.toNat
  let first := Wire.skipVarint b 0
  for i in [0:count.toNat] do
    signatures := signatures.push (b.extract (first + 64 * i) (first + 64 * i + 64))
  let start := o
  let mut versioned := false
  if Wire.u8 b o >= 0x80 then
    if Wire.u8 b o != 0x80 then
      return failed "unknown message version"
    versioned := true
    o := o + 1
  if !(Wire.ok (Wire.adv b o 3)) then
    return failed "the message header is truncated"
  let signers := (Wire.u8 b o).toNat
  let readonlySigned := (Wire.u8 b (o + 1)).toNat
  let readonlyUnsigned := (Wire.u8 b (o + 2)).toNat
  o := o + 3
  let keyCount := Wire.varint b o
  let keysAt := Wire.skipVarint b o
  o := Wire.adv b (Wire.skipN b keysAt keyCount 32) 32
  if !(Wire.ok o) then
    return failed "the account keys are truncated"
  let mut keys : Array ByteArray := Array.emptyWithCapacity keyCount.toNat
  for i in [0:keyCount.toNat] do
    keys := keys.push (b.extract (keysAt + 32 * i) (keysAt + 32 * i + 32))
  let blockhash := b.extract (o - 32) o
  let ixCount := Wire.varint b o
  o := Wire.skipVarint b o
  if !(Wire.ok o) || ixCount > b.size.toUInt64 then
    return failed "the instructions are truncated"
  let mut instructions : Array Compiled := Array.emptyWithCapacity ixCount.toNat
  for _ in [0:ixCount.toNat] do
    let program := (Wire.u8 b o).toNat
    let accountsAt := Wire.adv b o 1
    let dataAt := afterBytes b accountsAt
    let next := afterBytes b dataAt
    if !(Wire.ok next) then
      return failed "an instruction is truncated"
    instructions := instructions.push ⟨program, bytesAt b accountsAt, bytesAt b dataAt⟩
    o := next
  let mut lookups : Array Lookup := Array.emptyWithCapacity 0
  if versioned then
    let tableCount := Wire.varint b o
    o := Wire.skipVarint b o
    if !(Wire.ok o) || tableCount > b.size.toUInt64 then
      return failed "the address table lookups are truncated"
    for _ in [0:tableCount.toNat] do
      let writableAt := Wire.adv b o 32
      let readonlyAt := afterBytes b writableAt
      let next := afterBytes b readonlyAt
      if !(Wire.ok next) then
        return failed "an address table lookup is truncated"
      lookups := lookups.push ⟨b.extract o (o + 32), bytesAt b writableAt, bytesAt b readonlyAt⟩
      o := next
  if o != b.size then
    return failed "bytes are left over after the message"
  return ⟨signatures, ⟨versioned, signers, readonlySigned, readonlyUnsigned, keys, blockhash, instructions, lookups⟩,
    b.extract start b.size, ""⟩

end Tx
