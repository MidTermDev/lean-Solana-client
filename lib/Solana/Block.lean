import Solana.Shred
import Solana.Entry

/-!
# Checking a block

Given the data shreds of one slot, this checks everything that can be
checked about the block without executing it:

1. every shred is on a Merkle path to a root, and shreds of the same set
   agree on the root;
2. each root is signed by the same key, the slot's leader;
3. each set names the root of the set before it;
4. the shreds' data, joined in order, parses as entries and block markers
   (a header naming the parent block, a footer with the leader's bank hash);
5. the entries' hashes form an unbroken proof-of-history chain;
6. every signature of every transaction verifies.
-/

namespace Block

structure Report where
  /-- empty if the block passed every check that was made -/
  error : String
  slot : UInt64
  parentSlot : UInt64
  leader : ByteArray
  shreds : Nat
  sets : Nat
  entries : Nat
  ticks : Nat
  transactions : Nat
  signatures : Nat
  /-- sha256 evaluations recomputed for the proof of history -/
  hashes : UInt64
  /-- whether the first entry could be checked against the block before -/
  linked : Bool
  /-- the hash of the last entry: the block's blockhash -/
  blockhash : ByteArray
  bytes : Nat
  /-- from the block's header marker: the Merkle root of the parent block's last set of shreds -/
  parentId : ByteArray
  /-- from the block's footer marker: the hash of all state after this block, as the leader computed it -/
  bankHash : ByteArray
  /-- from the footer: the software that produced the block -/
  producer : String
  deriving Inhabited

def failed (why : String) : Report :=
  ⟨why, 0, 0, ByteArray.empty, 0, 0, 0, 0, 0, 0, 0, false, ByteArray.empty, 0, ByteArray.empty, ByteArray.empty, ""⟩

def printable (b : ByteArray) : String := Id.run do
  let mut out := ByteArray.emptyWithCapacity b.size
  for c in b do
    out := out.push (if c >= 32 && c < 127 then c else 63)
  return String.fromUTF8! out

/-- Which of `candidates` (32-byte keys, back to back) signed `root`? Returns its offset, or `Wire.bad`.
`hint` (an offset, or `Wire.bad`) is tried first. -/
def signer (candidates : ByteArray) (hint : Nat) (signature root : ByteArray) : Nat := Id.run do
  if hint + 32 <= candidates.size && Ed25519.verify (candidates.extract hint (hint + 32)) signature root then
    return hint
  for i in [0:candidates.size / 32] do
    if 32 * i != hint && Ed25519.verify (candidates.extract (32 * i) (32 * i + 32)) signature root then
      return 32 * i
  return Wire.bad

/-- The entry batches of a slot: the shreds' data joined up to each "data complete" mark. -/
def batches (shreds : Array ByteArray) : Array ByteArray := Id.run do
  let mut out : Array ByteArray := Array.emptyWithCapacity 64
  let mut current := ByteArray.emptyWithCapacity 65536
  for p in shreds do
    let h := Shred.parse p
    current := current ++ Shred.data p h
    if h.flags &&& Shred.flagDataComplete != 0 then
      out := out.push current
      current := ByteArray.emptyWithCapacity 65536
  if current.size != 0 then
    out := out.push current
  return out

/-- Checks a block. `shreds` are the data shreds of one slot, in order from
index 0, none missing. `candidates` are the keys the leader may be (back to
back) and `hint` the offset of the likeliest. `previous` is the blockhash
of the parent block, or empty if it is not known, in which case the first
entry's hash is taken on trust and the chain is checked from there.
`previousRoot` is the Merkle root of the parent block's last set of shreds,
which this block's first set must name; empty if not known. -/
def verify (shreds : Array ByteArray) (candidates : ByteArray) (hint : Nat) (previous previousRoot : ByteArray) : Report := Id.run do
  if shreds.size == 0 then
    return failed "no shreds"
  let first := Shred.parse shreds[0]!
  if !first.ok || !first.isData then
    return failed "the first shred is malformed"
  if previousRoot.size == 32 && Shred.chainedRoot shreds[0]! first != previousRoot then
    return failed "the block's first set does not follow the last set of its parent block"
  -- 1-3: Merkle paths, the leader's signature on each set, and the chain of sets
  let mut leaderAt := Wire.bad
  let mut sets := 0
  let mut root := ByteArray.empty
  let mut priorRoot := ByteArray.empty
  let mut setIndex : UInt64 := 0xFFFFFFFFFFFFFFFF
  for i in [0:shreds.size] do
    let p := shreds[i]!
    let h := Shred.parse p
    if !h.ok || !h.isData || h.slot != first.slot || h.index != i.toUInt64 then
      return failed s!"shred {i} is malformed or out of place"
    let r := Shred.merkleRoot p h
    if r.size != 32 then
      return failed s!"shred {i} has an invalid Merkle path"
    if h.fecSet != setIndex then
      -- a new set: its root must be signed by the leader, and it must name the previous set's root
      let at_ := signer candidates (if leaderAt != Wire.bad then leaderAt else hint) (p.extract 0 64) r
      if at_ == Wire.bad || (leaderAt != Wire.bad && at_ != leaderAt) then
        return failed s!"the set starting at shred {i} is not signed by {if leaderAt == Wire.bad then "any known node" else "the leader"}"
      leaderAt := at_
      if sets != 0 && Shred.chainedRoot p h != root then
        return failed s!"the set starting at shred {i} does not follow the one before it"
      priorRoot := root
      root := r
      setIndex := h.fecSet
      sets := sets + 1
    else if r != root || p.extract 0 64 != shreds[i - 1]!.extract 0 64 then
      return failed s!"shred {i} does not belong to its set"
  let last := Shred.parse shreds[shreds.size - 1]!
  if last.flags &&& Shred.flagLastInSlot != Shred.flagLastInSlot then
    return failed "the last shred does not end the slot"
  -- 4-6: entries, proof of history, transaction signatures
  let mut hash := previous
  let mut entries := 0
  let mut ticks := 0
  let mut transactions := 0
  let mut signatures := 0
  let mut hashes : UInt64 := 0
  let mut bytes := 0
  let mut parentId := ByteArray.empty
  let mut bankHash := ByteArray.empty
  let mut producer := ""
  for batch in batches shreds do
    bytes := bytes + batch.size
    if batch.size >= 13 && Wire.u64 batch 0 == 0 then
      -- a block marker instead of entries: version, kind, length, contents
      let length := (Wire.u16 batch 11).toNat
      if Wire.u16 batch 8 != 1 || 13 + length > batch.size then
        return failed "a block marker is malformed"
      let kind := Wire.u8 batch 10
      if kind == 1 && length >= 41 then
        -- header: the parent slot and the parent block's id
        if Wire.u64 batch 14 != first.slot - first.parentOffset then
          return failed "the block's header names a different parent than its shreds"
        parentId := batch.extract 22 54
      else if kind == 0 && length >= 42 then
        -- footer: bank hash, production time, the producer's name
        bankHash := batch.extract 14 46
        let n := (Wire.u8 batch 54).toNat
        if 55 + n <= batch.size then
          producer := printable (batch.extract 55 (55 + n))
    else
     match Entry.parseBatch batch with
     | none => return failed s!"the entries after entry {entries} do not parse"
     | some parsed =>
       for e in parsed do
         let mut sigs : Array ByteArray := Array.emptyWithCapacity (e.count * 2)
         let mut o := e.start
         for _ in [0:e.count] do
           let (tx, next) := Tx.parseAt batch o
           o := next
           if !tx.verify then
             return failed s!"a transaction in entry {entries} has an invalid signature"
           for s in tx.signatures do
             sigs := sigs.push s
           signatures := signatures + tx.signatures.size
         if hash.size == 32 then
           if Entry.expected hash e.numHashes sigs != e.hash then
             return failed s!"proof of history breaks at entry {entries}"
           hashes := hashes + e.numHashes
         hash := e.hash
         entries := entries + 1
         transactions := transactions + e.count
         if e.count == 0 then
           ticks := ticks + 1
  return ⟨"", first.slot, first.slot - first.parentOffset, candidates.extract leaderAt (leaderAt + 32), shreds.size, sets,
    entries, ticks, transactions, signatures, hashes, previous.size == 32, hash, bytes, parentId, bankHash, producer⟩

/-- The blockhash of a block, given its last shreds (from the one after the
last "data complete" mark before the end, to the end): the hash of its last entry. -/
def lastHash (tail : Array ByteArray) : ByteArray :=
  let all := batches tail
  if all.size == 0 then ByteArray.empty
  else
    match Entry.parseBatch all[all.size - 1]! with
    | none => ByteArray.empty
    | some parsed => if parsed.size == 0 then ByteArray.empty else parsed[parsed.size - 1]!.hash

/-- The Merkle root of the set a shred belongs to. -/
def rootOf (shred : ByteArray) : ByteArray := Shred.merkleRoot shred (Shred.parse shred)

end Block
