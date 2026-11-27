import Crypto.Sha256
import Solana.Transaction

/-!
# Entries and proof of history

A block is a list of **entries**. Each entry says how many times the
previous entry's hash was hashed again to get here, and gives the resulting
hash; if it carries transactions, the last step mixes them in. Recomputing
the chain proves the entries were produced in this order, with this much
hashing between them: a clock made of SHA-256.

    hash = sha256(sha256(... sha256(previous) ...))        `numHashes` times, for an entry with no transactions
    hash = sha256(that, one step earlier ‖ mixin)          for an entry with transactions

where the mixin is the root of a Merkle tree over the signatures of the
entry's transactions.
-/

namespace Entry

structure Entry where
  numHashes : UInt64
  hash : ByteArray
  /-- where its transactions start and end in the batch it was parsed from -/
  start : Nat
  stop : Nat
  count : Nat
  deriving Inhabited

/-- Parses a batch of entries: a count, then each entry (hash count, hash, a
count of transactions, the transactions), possibly followed by zero padding.
Returns `none` if it is malformed. -/
def parseBatch (b : ByteArray) : Option (Array Entry) := Id.run do
  let n := Wire.u64 b 0
  if b.size < 8 || n > b.size.toUInt64 then
    return none
  let mut out : Array Entry := Array.emptyWithCapacity n.toNat
  let mut o := 8
  for _ in [0:n.toNat] do
    if o + 48 > b.size then
      return none
    let count := Wire.u64 b (o + 40)
    if count > b.size.toUInt64 then
      return none
    let start := o + 48
    let mut q := start
    for _ in [0:count.toNat] do
      let (tx, next) := Tx.parseAt b q
      if tx.error != "" || !(Wire.ok next) then
        return none
      q := next
    out := out.push ⟨Wire.u64 b o, b.extract (o + 8) (o + 40), start, q, count.toNat⟩
    o := q
  -- some producers pad each batch with zeros to fill its last shreds
  for i in [o:b.size] do
    if b[i]! != 0 then
      return none
  return some out

/-- `sha256` applied `n` times. -/
def iterate (h : ByteArray) (n : UInt64) : ByteArray := Id.run do
  let mut x := h
  let mut left := n
  while left != 0 do
    x := Sha256.hash x
    left := left - 1
  return x

/-- The Merkle root of signatures: leaves are `sha256(0 ‖ signature)`, inner
nodes `sha256(1 ‖ left ‖ right)`, and a level with an odd number of nodes
pairs its last node with itself. -/
def signatureRoot (signatures : Array ByteArray) : ByteArray := Id.run do
  if signatures.size == 0 then
    return ByteArray.empty
  let mut level : Array ByteArray := Array.emptyWithCapacity signatures.size
  for s in signatures do
    level := level.push (Sha256.hash ((ByteArray.empty.push 0) ++ s))
  while level.size > 1 do
    let mut next : Array ByteArray := Array.emptyWithCapacity ((level.size + 1) / 2)
    for i in [0:(level.size + 1) / 2] do
      let left := level[2 * i]!
      let right := if 2 * i + 1 < level.size then level[2 * i + 1]! else left
      next := next.push (Sha256.hash ((ByteArray.empty.push 1) ++ left ++ right))
    level := next
  return level[0]!

/-- The hash an entry must have, given the hash before it and what its
transactions mix in (the root of their signatures; empty for an entry with none). -/
def expectedWith (previous : ByteArray) (numHashes : UInt64) (mixin : ByteArray) : ByteArray :=
  if numHashes == 0 && mixin.size == 0 then previous
  else
    let before := iterate previous (if numHashes == 0 then 0 else numHashes - 1)
    if mixin.size == 0 then Sha256.hash before else Sha256.hash (before ++ mixin)

/-- The hash an entry must have, given the hash before it and the signatures of its transactions. -/
def expected (previous : ByteArray) (numHashes : UInt64) (signatures : Array ByteArray) : ByteArray :=
  expectedWith previous numHashes (signatureRoot signatures)

end Entry
