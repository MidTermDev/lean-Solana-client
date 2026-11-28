import Solana.Wire
import Solana.LtHash

/-!
# Snapshots

A snapshot is the whole state of the chain at one slot: an archive holding a
*manifest* (the bank: slot, hashes, the stake of every validator, and the
lattice hash of all accounts) and then the accounts themselves, in files
named `accounts/<slot>.<id>` after the slot each was last written in.

This module reads the manifest and the account files. Neither is trusted:
the accounts must hash to the manifest's lattice hash, whose checksum is the
hash in the snapshot's name, the value validators announce in gossip.
-/

namespace Snapshot

-- ------------------------------------------------------------ account files

/-- One stored account, located in a buffer. -/
structure Stored where
  /-- false when the buffer does not hold the whole record from the offset given -/
  ok : Bool
  /-- offsets of the address, the owner and the data -/
  pubkey : Nat
  owner : Nat
  data : Nat
  dataLen : Nat
  lamports : UInt64
  rentEpoch : UInt64
  executable : Bool
  /-- offset of the next record: records are aligned to 8 bytes -/
  next : Nat
  deriving Inhabited

/-- Bytes before an account's data: write version (unused), data length,
address; lamports, rent epoch, owner, executable flag and padding; and an
unused hash. -/
def headerSize : Nat := 136

/-- The largest account there can be. -/
def maxData : Nat := 10485760

/-- Reads the record at `o`, which must end by `limit` (the end of the
file, or of what has been read of it). With `ok` false, `dataLen` says
whether more bytes could help: it is `Wire.bad` when the record is not valid
at all. -/
def stored (b : ByteArray) (o limit : Nat) : Stored := Id.run do
  if o + headerSize > limit then
    return ⟨false, 0, 0, 0, 0, 0, 0, false, 0⟩
  let dataLen := (Wire.u64 b (o + 8)).toNat
  if dataLen > maxData then
    return ⟨false, 0, 0, 0, Wire.bad, 0, 0, false, 0⟩
  if o + headerSize + dataLen > limit then
    return ⟨false, 0, 0, 0, dataLen, 0, 0, false, 0⟩
  return ⟨true, o + 16, o + 64, o + headerSize, dataLen, Wire.u64 b (o + 48), Wire.u64 b (o + 56), b[o + 96]! != 0,
    o + (headerSize + dataLen + 7) / 8 * 8⟩

/-- The slot in the name of an account file, `accounts/<slot>.<id>`; `none` for any other name. -/
def fileSlot (name : String) : Option UInt64 := Id.run do
  let b := name.toUTF8
  if b.size < 12 || !(Wire.eqAt b 0 "accounts/".toUTF8 0 9) then
    return none
  let mut slot : UInt64 := 0
  let mut o := 9
  while o < b.size && b[o]! >= 48 && b[o]! <= 57 do
    slot := slot * 10 + (b[o]! - 48).toUInt64
    o := o + 1
  if o == 9 || o + 1 >= b.size || b[o]! != 46 then
    return none
  for i in [o + 1:b.size] do
    if b[i]! < 48 || b[i]! > 57 then
      return none
  return some slot

-- ---------------------------------------------------------------- manifest

/-- A validator's vote account as an epoch's stakes record it. -/
structure Voter where
  vote : ByteArray
  node : ByteArray
  stake : UInt64
  /-- the validator's BLS key (48 bytes), with which it signs its votes; empty if its vote account has none -/
  bls : ByteArray
  /-- the address its vote account names to receive its share of block fees; empty in older layouts, where the identity receives it -/
  collector : ByteArray
  /-- what it keeps of its stakers' rewards, in hundredths of a percent -/
  commission : UInt64
  deriving Inhabited

/-- The stakes that decide who leads and whose votes count during one epoch. -/
structure EpochStakes where
  epoch : UInt64
  total : UInt64
  voters : Array Voter
  deriving Inhabited

structure Manifest where
  error : String
  slot : UInt64
  parentSlot : UInt64
  /-- the bank hash of the slot, and of its parent -/
  hash : ByteArray
  parentHash : ByteArray
  /-- the most recent blockhash -/
  blockhash : ByteArray
  blockHeight : UInt64
  epoch : UInt64
  /-- every lamport in existence -/
  capitalization : UInt64
  /-- the bytes of data in all accounts together -/
  accountsDataLen : UInt64
  transactionCount : UInt64
  signatureCount : UInt64
  tickHeight : UInt64
  ticksPerSlot : UInt64
  /-- 0 when hashing is off (test clusters) -/
  hashesPerTick : UInt64
  lamportsPerSignature : UInt64
  slotsPerEpoch : UInt64
  leaderScheduleOffset : UInt64
  warmup : Bool
  firstNormalEpoch : UInt64
  firstNormalSlot : UInt64
  leader : ByteArray
  /-- recent blockhashes still valid for transactions: count -/
  blockhashes : Nat
  /-- the queue of recent blockhashes: 56 bytes each (hash, lamports per signature, position, timestamp) -/
  queue : ByteArray
  /-- the position of the newest blockhash in the queue's numbering -/
  lastHashIndex : UInt64
  /-- vote accounts and stake delegations in the bank's current stakes -/
  voteAccounts : Nat
  delegations : Nat
  /-- the stakes of the epochs around the snapshot -/
  epochStakes : Array EpochStakes
  /-- the lattice hash of all accounts: 2048 bytes, or empty if the snapshot has none -/
  ltHash : ByteArray
  /-- the block's identifier, if recorded -/
  blockId : ByteArray
  /-- inflation: its initial and terminal rates, the taper, the foundation's share and term (doubles) -/
  inflation : ByteArray
  /-- the address of every delegated stake account (32 bytes each) -/
  stakeKeys : ByteArray
  deriving Inhabited

def Manifest.failed (why : String) : Manifest :=
  ⟨why, 0, 0, ByteArray.empty, ByteArray.empty, ByteArray.empty, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, false, 0, 0, ByteArray.empty,
    0, ByteArray.empty, 0, 0, 0, Array.emptyWithCapacity 0, ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty⟩

/-- Skips a sequence of `count`-prefixed fixed-size elements. -/
def skipSeq (b : ByteArray) (o size : Nat) : Nat :=
  if !(Wire.ok o) || o + 8 > b.size then Wire.bad
  else
    let n := (Wire.u64 b o).toNat
    if n > b.size then Wire.bad else Wire.adv b (o + 8) (n * size)

/-- Reads a map of vote accounts (address, stake, account). Returns the offset after it, and the voters
with stake if `keep` is set. An account is: lamports, data (length-prefixed), owner, executable, rent epoch. -/
def voteAccounts (b : ByteArray) (start : Nat) (keep : Bool) : Nat × Array Voter × Nat := Id.run do
  if !(Wire.ok start) || start + 8 > b.size then
    return (Wire.bad, Array.emptyWithCapacity 0, 0)
  let n := (Wire.u64 b start).toNat
  let mut o := start + 8
  let mut voters : Array Voter := Array.emptyWithCapacity (if keep then n else 0)
  for _ in [0:n] do
    if o + 56 > b.size then
      return (Wire.bad, voters, 0)
    let stake := Wire.u64 b (o + 32)
    let dataLen := (Wire.u64 b (o + 48)).toNat
    let data := o + 56
    if dataLen > b.size || data + dataLen + 41 > b.size then
      return (Wire.bad, voters, 0)
    -- a vote account's data begins with a version number and the validator's identity
    if keep && stake != 0 && dataLen >= 36 then
      -- (in the current layout of a vote account, an optional BLS key follows four addresses and three numbers)
      let bls := if Wire.u32 b data == 3 && dataLen >= 193 && b[data + 144]! == 1 then b.extract (data + 145) (data + 193) else ByteArray.empty
      let collector := if Wire.u32 b data == 3 && dataLen >= 132 then b.extract (data + 100) (data + 132) else ByteArray.empty
      let commission := if Wire.u32 b data == 3 && dataLen >= 134 then Wire.u16 b (data + 132) else if dataLen > 68 then 100 * Wire.u8 b (data + 68) else 0
      voters := voters.push ⟨b.extract o (o + 32), b.extract (data + 4) (data + 36), stake, bls, collector, commission⟩
    o := data + dataLen + 41
  return (o, voters, n)

/-- Skips `Stakes` after its vote accounts: delegations of `size` bytes each, two numbers, and the stake history. -/
def restOfStakes (b : ByteArray) (o size : Nat) : Nat :=
  skipSeq b (Wire.adv b (skipSeq b o size) 16) 32

def parse (b : ByteArray) : Manifest := Id.run do
  -- the blockhash queue: index of the last hash, the last hash, a map of hashes, the maximum age
  if b.size < 64 then
    return Manifest.failed "manifest too short"
  let mut o := 8
  let mut blockhash := ByteArray.empty
  if b[o]! == 1 then
    blockhash := b.extract (o + 1) (o + 33)
    o := o + 33
  else
    o := o + 1
  let blockhashes := (Wire.u64 b o).toNat
  let lastHashIndex := Wire.u64 b 0
  let queueAt := o + 8
  o := Wire.adv b (skipSeq b o 56) 8
  let queue := if Wire.ok o then b.extract queueAt (queueAt + 56 * blockhashes) else ByteArray.empty
  -- ancestors
  o := skipSeq b o 16
  if !(Wire.ok o) || o + 72 > b.size then
    return Manifest.failed "manifest: blockhash queue does not parse"
  let hash := b.extract o (o + 32)
  let parentHash := b.extract (o + 32) (o + 64)
  let parentSlot := Wire.u64 b (o + 64)
  -- hard forks
  o := skipSeq b (o + 72) 16
  if !(Wire.ok o) || o + 41 > b.size then
    return Manifest.failed "manifest: hard forks do not parse"
  let transactionCount := Wire.u64 b o
  let tickHeight := Wire.u64 b (o + 8)
  let signatureCount := Wire.u64 b (o + 16)
  let capitalization := Wire.u64 b (o + 24)
  o := o + 40
  let mut hashesPerTick : UInt64 := 0
  if b[o]! == 1 then
    hashesPerTick := Wire.u64 b (o + 1)
    o := o + 9
  else
    o := o + 1
  if o + 330 > b.size then
    return Manifest.failed "manifest too short"
  let ticksPerSlot := Wire.u64 b o
  -- (nanoseconds per slot, genesis time, slots per year)
  let accountsDataLen := Wire.u64 b (o + 40)
  let slot := Wire.u64 b (o + 48)
  let epoch := Wire.u64 b (o + 56)
  let blockHeight := Wire.u64 b (o + 64)
  let leader := b.extract (o + 72) (o + 104)
  -- (collector fees, fee calculator, fee rate governor 33, collected rent, rent collector 66)
  o := o + 104 + 16 + 33 + 8 + 66
  let slotsPerEpoch := Wire.u64 b o
  let leaderScheduleOffset := Wire.u64 b (o + 8)
  let warmup := b[o + 16]! != 0
  let firstNormalEpoch := Wire.u64 b (o + 17)
  let firstNormalSlot := Wire.u64 b (o + 25)
  -- (inflation: six numbers)
  let inflation := b.extract (o + 33) (o + 73)
  o := o + 33 + 48
  -- the bank's stakes
  let (afterVotes, _, voteCount) := voteAccounts b o false
  if !(Wire.ok afterVotes) || afterVotes + 8 > b.size then
    return Manifest.failed "manifest: vote accounts do not parse"
  let delegations := (Wire.u64 b afterVotes).toNat
  o := restOfStakes b afterVotes 96
  -- (each delegation is the stake account's address and 64 bytes that the account itself also holds)
  let mut stakeKeys := ByteArray.emptyWithCapacity (if Wire.ok o then 32 * delegations else 0)
  if Wire.ok o then
    for k in [0:delegations] do
      stakeKeys := b.copySlice (afterVotes + 8 + 96 * k) stakeKeys stakeKeys.size 32
  -- three unused collections, then the old place of the epoch stakes, which must be empty
  o := skipSeq b (skipSeq b (skipSeq b o 32) 32) 40
  if !(Wire.ok o) || o + 9 > b.size then
    return Manifest.failed "manifest: stakes do not parse"
  if Wire.u64 b o != 0 then
    return Manifest.failed "manifest: epoch stakes in the old format"
  o := o + 9
  -- the accounts database: a map of slot to storage files (no longer used), a version, the slot, hashes and statistics
  if o + 8 > b.size then
    return Manifest.failed "manifest too short"
  let storages := (Wire.u64 b o).toNat
  o := o + 8
  for _ in [0:storages] do
    o := skipSeq b (Wire.adv b o 8) 16
    if !(Wire.ok o) then
      return Manifest.failed "manifest: storage list does not parse"
  if o + 120 > b.size then
    return Manifest.failed "manifest too short"
  if Wire.u64 b (o + 8) != slot then
    return Manifest.failed "manifest: the accounts database is for another slot"
  o := skipSeq b (skipSeq b (o + 120) 8) 40
  if !(Wire.ok o) then
    return Manifest.failed "manifest: historical roots do not parse"
  -- fields added over time; a manifest may end before any of them
  let mut lamportsPerSignature : UInt64 := 0
  let mut epochStakes : Array EpochStakes := Array.emptyWithCapacity 8
  let mut ltHash := ByteArray.empty
  let mut blockId := ByteArray.empty
  if o + 8 <= b.size then
    lamportsPerSignature := Wire.u64 b o
    o := o + 8
  if o < b.size then
    o := if b[o]! == 1 then Wire.adv b o 89 else o + 1
  if Wire.ok o && o < b.size then
    o := if b[o]! == 1 then Wire.adv b o 33 else o + 1
  if Wire.ok o && o + 8 <= b.size then
    let n := (Wire.u64 b o).toNat
    o := o + 8
    for _ in [0:n] do
      if !(Wire.ok o) || o + 12 > b.size then
        return Manifest.failed "manifest: epoch stakes do not parse"
      let forEpoch := Wire.u64 b o
      if Wire.u32 b (o + 8) != 0 then
        return Manifest.failed s!"manifest: epoch stakes in an unknown format ({Wire.u32 b (o + 8)})"
      let (afterVotes, voters, _) := voteAccounts b (o + 12) true
      -- delegations here carry one more number each; then the total, the nodes' vote accounts, the authorised voters
      o := restOfStakes b afterVotes 104
      if !(Wire.ok o) || o + 16 > b.size then
        return Manifest.failed "manifest: epoch stakes do not parse"
      let total := Wire.u64 b o
      let nodes := (Wire.u64 b (o + 8)).toNat
      o := o + 16
      for _ in [0:nodes] do
        o := Wire.adv b (skipSeq b (Wire.adv b o 32) 32) 8
      o := skipSeq b o 64
      epochStakes := epochStakes.push ⟨forEpoch, total, voters⟩
  if !(Wire.ok o) then
    return Manifest.failed "manifest: epoch stakes do not parse"
  if o < b.size then
    if b[o]! == 1 then
      if o + 2049 > b.size then
        return Manifest.failed "manifest: lattice hash cut short"
      ltHash := b.extract (o + 1) (o + 2049)
      o := o + 2049
    else
      o := o + 1
  if o < b.size && b[o]! == 1 && o + 33 <= b.size then
    blockId := b.extract (o + 1) (o + 33)
  -- newer manifests leave the epoch field unused: it follows from the slot
  let counted := if slotsPerEpoch != 0 && slot >= firstNormalSlot then firstNormalEpoch + (slot - firstNormalSlot) / slotsPerEpoch else epoch
  return ⟨"", slot, parentSlot, hash, parentHash, blockhash, blockHeight, (if epoch == 0 then counted else epoch), capitalization, accountsDataLen, transactionCount,
    signatureCount, tickHeight, ticksPerSlot, hashesPerTick, lamportsPerSignature, slotsPerEpoch, leaderScheduleOffset, warmup,
    firstNormalEpoch, firstNormalSlot, leader, blockhashes, queue, lastHashIndex, voteCount, delegations, epochStakes, ltHash, blockId, inflation, stakeKeys⟩

end Snapshot
