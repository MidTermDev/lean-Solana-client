import Sys
import Fmt
import Encoding.Base58
import Encoding.Hex
import Solana.Bank
import Solana.Block
import Solana.Accounts
import Solana.Snapshot
import Solana.LtHash
import Solana.LeaderSchedule
import Solana.Alpenglow
import Solana.Epoch
import RunBlock

/-!
# `leansol replay`

Executes blocks against the state a snapshot left, and checks the result
the only way that settles it: the bank hash. After a block, the lattice hash
of all accounts is the parent's with every account the block changed taken
out as it was and put back as it is; hashed with the parent's bank hash, the
number of signatures and the blockhash, it must be the hash in the block's
footer, which the leader computed and signed its shreds over.

The state is the snapshot's store, never written, and an *overlay*: one more
shard of the same kind, holding every account as the replayed blocks left it.
-/

namespace RunReplay

def usage : String :=
  "usage: leansol replay --state DIR --blocks DIR [--count N] [options]\n" ++
  "       leansol replay --state DIR --blocks DIR --live [options]\n" ++
  "\n" ++
  "  --state DIR    the store loaded by `leansol snapshot`\n" ++
  "  --blocks DIR   blocks saved by `leansol block SLOT --save DIR/SLOT.block`, or by a node run with --spool DIR\n" ++
  "  --count N      how many blocks (default 1; with --live, no limit)\n" ++
  "  --live         follow the chain: execute each block in DIR once a later block's footer proves it final\n" ++
  "                 (a certificate signed by enough of the stake, which is checked), wait for more, fetch\n" ++
  "                 the ones that are missing, and save the state in STATE/live every few minutes, where\n" ++
  "                 the next run with --live goes on from. Blocks are deleted once the state past them is\n" ++
  "                 saved. Stops at the first bank hash that differs.\n" ++
  "  --until SLOT   with --live: save the state and stop once this slot is reached\n" ++
  "  --resume       without --live: start from the state --live last saved instead of the snapshot's,\n" ++
  "                 leaving it as it is (not while a run with --live is going)\n" ++
  "  --node A:P     with --live: the running node that says where the chain is and whom to ask for blocks\n" ++
  "                 (default 127.0.0.1:9184)\n" ++
  "  --fetchers N   with --live: processes fetching missing blocks (default 24)\n" ++
  "  --lines        print one line per transaction: its outcome, fee, compute units and balances\n" ++
  "  --follow       after a block whose hash differs, continue from the block's own hash\n" ++
  "  --timing       say where each block's time went\n" ++
  "  --interpret    run every program with the interpreter, none as machine code\n" ++
  "  --signatures N check every transaction's signatures, in N other processes, and every footer's\n" ++
  "                 certificate (default 3; 0 = not at all). Not with --live, whose blocks were verified\n" ++
  "                 by whoever saved them and whose certificates are checked as they are relied on\n" ++
  "  --trace N      print the log of transaction N of the first block\n"

def fail (message : String) : IO Unit := do
  IO.eprintln s!"leansol replay: {message}"
  Sys.exit 1

/-- The store a snapshot left, and what has changed since. Changes stay in memory, among the accounts
held, until `save` writes them to a log: an account rewritten by every block is then written once. -/
structure World where
  shards : Array Accounts.Shard
  /-- logs of what has changed since the snapshot, the newest first; `save` writes to the first -/
  overlays : Array Accounts.Shard
  /-- Accounts read or written lately, as they are now, found by address (`Sbpf.accountAt`): most of what a
  block touches was touched by the block before it. -/
  slots : Array UInt64
  held : Array Sbpf.Account
  heldBytes : Nat
  /-- For each account held: what it adds to the lattice hash as it is now, where that has been worked
  out (empty where it has not, or the account has changed since). -/
  hashes : Array ByteArray
  /-- For each account held: 1 if it has changed since it was last written to a log. -/
  unsaved : Array UInt64

def absent (key : ByteArray) : Sbpf.Account := ⟨key, Sbpf.systemProgram, 0, ByteArray.empty, false⟩

def ofRecord (r : ByteArray) : Sbpf.Account :=
  if r.size < Accounts.headerSize || Accounts.recLamports r == 0 then absent (r.extract 0 32)
  else ⟨r.extract 0 32, r.extract 32 64, Accounts.recLamports r, Accounts.recData r, Accounts.recExecutable r⟩

/-- The account at `key` as of now: as held, or as a log has it, or else as the snapshot does. -/
def World.get (w : World) (key : ByteArray) : IO Sbpf.Account := do
  let at_ := Sbpf.accountAt w.slots w.held key
  if at_ != Sbpf.notFound then
    return w.held[at_]!
  for overlay in w.overlays do
    let (_, loc) ← overlay.locate ByteArray.empty key 0
    if loc != Accounts.none_ then
      return ofRecord (← overlay.recordAt ByteArray.empty loc)
  let shard := w.shards[Accounts.shardOf key 0 w.shards.size]!
  let (_, found) ← shard.locate ByteArray.empty key 0
  if found == Accounts.none_ then
    return absent key
  return ofRecord (← shard.recordAt ByteArray.empty found)

def heldSlots : Nat := 2097152

/-- With this much held, it is time to `save`. -/
def World.full (w : World) : Bool := w.held.size >= 400000 || w.heldBytes > 4000000000

/-- Holds an account as it is now; `changed` says it differs from what the logs and the snapshot have. -/
def World.keep (w : World) (a : Sbpf.Account) (changed : Bool) : World :=
  let ⟨shards, overlays, slots, held, bytes, hashes, unsaved⟩ := w
  let at_ := Sbpf.accountAt slots held a.key
  if at_ != Sbpf.notFound then
    let before := held[at_]!.data.size
    ⟨shards, overlays, slots, held.set! at_ a, bytes + a.data.size - before, hashes.set! at_ ByteArray.empty, if changed then unsaved.set! at_ 1 else unsaved⟩
  else
    ⟨shards, overlays, Sbpf.accountLink slots held a.key held.size, held.push a, bytes + a.data.size, hashes.push ByteArray.empty, unsaved.push (if changed then 1 else 0)⟩

/-- What the account at `key` adds to the lattice hash, if that is known for its present state (else empty). -/
def World.hashOf (w : World) (key : ByteArray) : ByteArray :=
  let at_ := Sbpf.accountAt w.slots w.held key
  if at_ != Sbpf.notFound then w.hashes[at_]! else ByteArray.empty

/-- Notes what the account at `key`, as it is now, adds to the lattice hash. -/
def World.noteHash (w : World) (key : ByteArray) (c : ByteArray) : World :=
  let at_ := Sbpf.accountAt w.slots w.held key
  if at_ == Sbpf.notFound then w
  else
    let ⟨shards, overlays, slots, held, bytes, hashes, unsaved⟩ := w
    ⟨shards, overlays, slots, held, bytes, hashes.set! at_ c, unsaved⟩

/-- `get`, remembering what was read. -/
def World.fetch (w : World) (key : ByteArray) : IO (World × Sbpf.Account) := do
  let at_ := Sbpf.accountAt w.slots w.held key
  if at_ != Sbpf.notFound then
    let a := w.held[at_]!
    return (w, a)
  let a ← w.get key
  return (w.keep a false, a)

/-- Writes every account that has changed since the last time to the first log, and holds nothing any more. -/
def World.save (w : World) (slot : UInt64) : IO World := do
  let mut overlay := w.overlays[0]!
  let mut pending := ByteArray.emptyWithCapacity 4300000
  for k in [0:w.held.size] do
    if w.unsaved[k]! != 0 then
      let a := w.held[k]!
      let r := Accounts.recordFrom (a.key ++ a.owner) 0 32 a.lamports Accounts.noRent slot a.executable a.data 0 a.data.size
      let (entry, loc) ← overlay.locate pending a.key 0
      overlay ← overlay.point entry (loc == Accounts.none_) (Accounts.Shard.keyOf r 0) (overlay.flushed + pending.size.toUInt64)
      pending := pending ++ r
      if pending.size >= 4194304 then
        overlay ← overlay.flush pending
        pending := ByteArray.emptyWithCapacity 4300000
  overlay ← overlay.flush pending
  return ⟨w.shards, w.overlays.set! 0 overlay, Array.replicate heldSlots 0, Array.emptyWithCapacity 1024, 0, Array.emptyWithCapacity 1024, Array.emptyWithCapacity 1024⟩

/-- The system calls a program file names that the machine does not provide (for diagnosis). -/
def missingCalls (elf : ByteArray) (found0 : String) : String := Id.run do
  let mut found := found0
  let mut i := 1
  while i + 5 < elf.size do
    if elf[i]! == 115 && elf[i + 1]! == 111 && elf[i + 2]! == 108 && elf[i + 3]! == 95 && elf[i - 1]! == 0 then
      let mut j := i
      while j < elf.size && elf[j]! != 0 && j - i < 48 do
        j := j + 1
      let name := String.fromUTF8! (elf.extract i j)
      let mut known := false
      for n in Sbpf.syscallNames do
        if n == name then
          known := true
      if !known && RunBlock.findAt found.toUTF8 name.toUTF8 0 == found.toUTF8.size then
        found := found ++ " " ++ name
      i := j
    else
      i := i + 1
  return found

def same (a b : Sbpf.Account) : Bool :=
  a.lamports == b.lamports && a.executable == b.executable && a.owner == b.owner && a.data == b.data

def u64 (v : UInt64) : ByteArray := Wire.putU64 (ByteArray.emptyWithCapacity 8) v

/-- The `SlotHashes` sysvar with one more slot at its front: a count, then (slot, hash) pairs, at most 512, in a buffer of fixed size. -/
def slotHashesWith (old : ByteArray) (slot : UInt64) (hash : ByteArray) : ByteArray := Id.run do
  let count := (Wire.u64 old 0).toNat
  let kept := if count >= 512 then 511 else count
  let mut b := u64 (kept + 1).toUInt64 ++ u64 slot ++ hash
  b := old.copySlice 8 b b.size (40 * kept)
  return Sbpf.zeros b (20488 - b.size)

def clockData (slot epochStart epoch leaderEpoch unix : UInt64) : ByteArray :=
  u64 slot ++ u64 epochStart ++ u64 epoch ++ u64 leaderEpoch ++ u64 unix

/-- The (deprecated, still maintained) `RecentBlockhashes` sysvar with a new blockhash at its front: a count, then up to 150 (hash, lamports per signature) pairs, newest first, in a buffer of 6008 bytes. -/
def recentBlockhashesWith (old blockhash : ByteArray) (lamportsPerSignature : UInt64) : ByteArray := Id.run do
  let count := (Wire.u64 old 0).toNat
  let kept := if count >= 150 then 149 else count
  let mut b := u64 (kept + 1).toUInt64 ++ blockhash ++ u64 lamportsPerSignature
  b := old.copySlice 8 b b.size (40 * kept)
  return Sbpf.zeros b (6008 - b.size)

/-- The `SlotHistory` sysvar with one more slot marked as having a block: a
bit for each of the last 1,048,576 slots, and the next slot expected. Slots
skipped since the last block are cleared. Layout: a presence byte, the
number of 64-bit words (16,384), the words, the number of bits, the next slot. -/
def slotHistoryWith (old : ByteArray) (slot : UInt64) : ByteArray := Id.run do
  let mut b := old
  let next := Wire.u64 old 131089
  if slot > next && slot - next >= 1048576 then
    for i in [9:131081] do
      b := b.set! i 0
  else
    let mut skipped := next
    while skipped < slot do
      let at_ := 9 + 8 * ((skipped % 1048576) / 64).toNat
      let word := Wire.u64 b at_ &&& ~~~((1 : UInt64) <<< ((skipped % 1048576) % 64))
      b := Sbpf.storeAt b at_ 8 word
      skipped := skipped + 1
  let at_ := 9 + 8 * ((slot % 1048576) / 64).toNat
  b := Sbpf.storeAt b at_ 8 (Wire.u64 b at_ ||| ((1 : UInt64) <<< ((slot % 1048576) % 64)))
  return Sbpf.storeAt b 131089 8 (slot + 1)

def tokenProgram : ByteArray := Base58.decode "TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA"
def token2022Program : ByteArray := Base58.decode "TokenzQdBNbLqP5VEhdkAS6EPFLC1PHnBqCXEpPxuEb"
def recentBlockhashesSysvar : ByteArray := Base58.decode "SysvarRecentB1ockHashes11111111111111111111"
def slotHistorySysvar : ByteArray := Base58.decode "SysvarS1otHistory11111111111111111111111111"
def incinerator : ByteArray := Bank.incinerator
def alpenglowFeature : ByteArray := Base58.decode "A1pengvuM6JEcyNuTnMqepBKhwHE3N6PmUrdATGawhJS"

/-- The account holding the rewards an epoch can pay, and the one recording when Alpenglow took over. -/
def voteRewardAccount : ByteArray := (Sbpf.findProgramAddress #["vote_reward_account".toUTF8] alpenglowFeature).1
def genesisCertificate : ByteArray := (Sbpf.findProgramAddress #["carlgration".toUTF8] alpenglowFeature).1

/-- Position of `key` among `keys`, or `Sbpf.notFound`. -/
def keyIndex (keys : Array ByteArray) (key : ByteArray) : Nat := Id.run do
  for i in [0:keys.size] do
    if keys[i]! == key then
      return i
  return Sbpf.notFound

/-- The stakes recorded for an epoch, or none. -/
def stakesOf (m : Snapshot.Manifest) (epoch : UInt64) : Snapshot.EpochStakes := Id.run do
  for e in m.epochStakes do
    if e.epoch == epoch then
      return e
  return ⟨epoch, 0, Array.emptyWithCapacity 0⟩

/-- Where the chain keeps its clock to the nanosecond: an address derived from the Alpenglow feature's. -/
def nanosecondClock : ByteArray := (Sbpf.findProgramAddress #["alpenclock".toUTF8] alpenglowFeature).1

/-- A block read from the directory. -/
structure Waiting where
  slot : UInt64
  /-- the slot of the block it is built on -/
  parent : UInt64
  /-- its id, by which votes name it -/
  id : ByteArray
  /-- the shred version its leader sent it under -/
  version : UInt64
  /-- what its footer says of an earlier block being final (the slot is 0 if it says nothing, or once
  its certificate has proved bad), and whether the certificate has been checked -/
  final : Alpenglow.Certs
  proven : Bool
  block : Block.Contents
  deriving Inhabited

/-- The block saved for `slot`, or one whose `error` says why not. -/
def savedBlock (blocksDir : String) (slot : UInt64) : IO Waiting := do
  let file ← Sys.readFile s!"{blocksDir}/{slot}.block" 0x8000000
  if file.size < 104 + Shred.dataPayload || (file.size - 104) % Shred.dataPayload != 0 then
    return ⟨slot, 0, ByteArray.empty, 0, Alpenglow.parse ByteArray.empty, false,
      { Block.contents (Array.emptyWithCapacity 0) with error := s!"{blocksDir}/{slot}.block is not a saved block" }⟩
  let mut shreds : Array ByteArray := Array.emptyWithCapacity ((file.size - 104) / Shred.dataPayload)
  for k in [0:(file.size - 104) / Shred.dataPayload] do
    shreds := shreds.push (file.extract (104 + Shred.dataPayload * k) (104 + Shred.dataPayload * (k + 1)))
  let block := Block.contents shreds
  let first := Shred.parse shreds[0]!
  let parent := slot - first.parentOffset
  return ⟨slot, parent, Block.id shreds parent block.parentId, first.version, Alpenglow.parse block.certificates, false, block⟩

/-- Position in `waiting` of the block for `slot`, or `Sbpf.notFound`. -/
def waitingAt (waiting : Array Waiting) (slot : UInt64) : Nat := Id.run do
  for k in [0:waiting.size] do
    if waiting[k]!.slot == slot then
      return k
  return Sbpf.notFound

/-- Is `slot` between a waiting block and the block that one is built on, so that the chain passed it by? -/
def skipped (waiting : Array Waiting) (slot : UInt64) : Bool := Id.run do
  for w in waiting do
    if w.parent < slot && slot < w.slot then
      return true
  return false

/-- Which block to execute after `slot`'s: the one built on it that leads to a block some footer calls
final, so that nothing executed ever has to be undone. Only footers whose certificates are `proven`
(or only those not checked yet) are listened to, the latest first, and the blocks are followed back by
their ids, down to `id`, that of `slot`'s block (empty if not known). Returns the block's position in
`waiting` and that of the footer, or `Sbpf.notFound` and the slot of a block that is needed to tell (0
if none is known to be). -/
def next (waiting : Array Waiting) (slot : UInt64) (id : ByteArray) (proven : Bool) : Nat × Nat × UInt64 := Id.run do
  let mut found := Sbpf.notFound
  let mut via := Sbpf.notFound
  let mut missing : UInt64 := 0
  for j in [0:waiting.size] do
    let w := waiting[j]!
    if w.proven == proven && (via == Sbpf.notFound || w.slot > waiting[via]!.slot) then
      -- from the block the footer calls final, back from parent to parent
      let mut s := w.final.finalSlot
      let mut wanted := w.final.finalBlock
      for _ in [0:waiting.size] do
        if s > slot then
          let k := waitingAt waiting s
          if k == Sbpf.notFound || waiting[k]!.id != wanted then
            if missing == 0 || s < missing then
              missing := s
            s := 0
          else if waiting[k]!.parent == slot then
            if id.size == 0 || waiting[k]!.block.parentId == id then
              found := k
              via := j
            s := 0
          else
            wanted := waiting[k]!.block.parentId
            s := waiting[k]!.parent
  return (found, via, missing)

/-- The validators who can certify `slot`: those of its epoch, worked out anew only when the epoch changes. -/
def signersFor (m : Snapshot.Manifest) (known : Alpenglow.Signers) (slot : UInt64) : Alpenglow.Signers :=
  let epoch := if m.slotsPerEpoch == 0 then 0 else slot / m.slotsPerEpoch
  if known.epoch == epoch && known.keys.size != 0 then known else Alpenglow.signers epoch (stakesOf m epoch).voters

/-- A process that fetches blocks. For every slot number it is sent it asks validators for that slot's
block, verifies it (its leader's signature, its proof of history, every transaction signature) and
saves it in the directory, unless it is there already. -/
def fetcher (blocksDir node : String) (leaders : ByteArray) (requests : UInt64) : IO Unit := do
  let seed ← IO.getRandomBytes 32
  let pubkey := Ed25519.publicKey seed
  let sock ← Sys.udpSocket
  let _ ← Sys.bind sock 0 0
  Sys.setTimeout sock 20 20
  Sys.setRecvBuffer sock 8388608
  let unknown := Sbpf.zeros ByteArray.empty 32
  let mut candidates := ByteArray.empty
  let mut peers : Array RunBlock.Peer := Array.emptyWithCapacity 0
  let mut learned : UInt64 := 0
  repeat
    let request ← Sys.read requests 8
    if request.size != 8 then
      break
    let slot := Wire.u64 request 0
    let path := s!"{blocksDir}/{slot}.block"
    if (← Sys.readFile path 8).size == 0 then
      -- whom to ask: a new sample of the validators every ten minutes
      let now ← Sys.nowMs
      if now - learned > 600000 || peers.size == 0 then
        let (_, keys, sample, _) ← RunBlock.learn node 24
        candidates := keys
        peers := sample
        learned := now
      let (got, asked) ← RunBlock.fetch sock seed pubkey peers slot 0 4000
      peers := asked
      if got.complete then
        let shreds := RunBlock.slice got.shreds 0 (got.last + 1)
        let leader := LeaderSchedule.leaderAt leaders slot
        let r := if leader.size == 32 then Block.verify shreds leader 0 ByteArray.empty ByteArray.empty
          else Block.verify shreds candidates Wire.bad ByteArray.empty ByteArray.empty
        if r.error != "" then
          IO.eprintln s!"leansol replay: slot {slot} as fetched does not verify: {r.error}"
        else if !(← Sys.writeFileMode path (RunBlock.pack r unknown unknown shreds) 0x1a4) then
          IO.eprintln s!"leansol replay: cannot write {path}"

/-- A process that checks signatures. For every slot number it is sent it reads that block and checks the
signatures of its share of the transactions (every `workers`-th), and answers with how many did not
verify. Executing a block does not depend on its signatures, so this is done beside it, on other cores. -/
def signatureWorker (blocksDir : String) (share workers : Nat) (requests answers : UInt64) : IO Unit := do
  repeat
    let request ← Sys.read requests 8
    if request.size != 8 then
      break
    let block := (← savedBlock blocksDir (Wire.u64 request 0)).block
    let mut bad : UInt64 := if block.error != "" then 0xFFFFFFFF else 0
    for t in [0:block.transactions.size] do
      if t % workers == share && !(block.transactions[t]!.verify) then
        bad := bad + 1
    if !(← Sys.writeFully answers (u64 bad)) then
      break

def delegatedStakesAccount : ByteArray := (Sbpf.findProgramAddress #["reward_epoch_delegated_stakes".toUTF8] alpenglowFeature).1

/-- A validator's commission as the stakes of `epoch` recorded it, or all ones if they do not record the validator. -/
def commissionIn (m : Snapshot.Manifest) (epoch : UInt64) (vote : ByteArray) : UInt64 := Id.run do
  for v in (stakesOf m epoch).voters do
    if v.vote == vote then
      return v.commission
  return 0xFFFFFFFFFFFFFFFF

/-- What the first block of `epoch` does before its transactions (`Solana.Epoch` has the arithmetic).
`keys` are the addresses of all stake accounts that may be delegated, `supply` and `height` the lamports
in existence and the number of blocks before this one, `blockhash` the parent block's. Returns the
accounts as it leaves them; the supply; the stake rewards that the following blocks pay (56 bytes each:
the stake account, its reward, and the stake and credits it then has), grouped by block, and where each
block's begin; and the stakes of the epoch after this one. -/
def turn (world : World) (machine : Sbpf.Machine) (manifest : Snapshot.Manifest) (keys : ByteArray) (epoch supply height : UInt64)
    (blockhash : ByteArray) : IO (Array Sbpf.Account × UInt64 × ByteArray × Array Nat × Snapshot.EpochStakes) := do
  let ended := epoch - 1
  let oldHistory ← world.get Sbpf.stakeHistorySysvar
  -- ---- every delegated stake account, and what it was worth in the epoch that ended
  let count := keys.size / 32
  let mut stakeKeys := ByteArray.emptyWithCapacity keys.size
  let mut stakes : Array Epoch.Delegation := Array.emptyWithCapacity count
  let mut balances : Array UInt64 := Array.emptyWithCapacity count
  let mut minimums : Array UInt64 := Array.emptyWithCapacity count
  let mut effectives : Array UInt64 := Array.emptyWithCapacity count
  let mut actives : Array UInt64 := Array.emptyWithCapacity count
  -- the validators they are delegated to, as each is first met: its account, and the stake delegated to
  -- it in the epoch that ended and in the new one
  let mut validatorOf : Array Nat := Array.emptyWithCapacity count
  let mut validators : Array Sbpf.Account := Array.emptyWithCapacity 8192
  let mut validatorSlots : Array UInt64 := Array.replicate 262144 0
  let mut before : Array UInt64 := Array.emptyWithCapacity 8192
  let mut after : Array UInt64 := Array.emptyWithCapacity 8192
  let mut effective : UInt64 := 0
  let mut activating : UInt64 := 0
  let mut deactivating : UInt64 := 0
  for k in [0:count] do
    let a ← world.get (keys.extract (32 * k) (32 * k + 32))
    if a.owner == Bank.stakeProgram && a.lamports != 0 && Epoch.delegated a.data then
      let d := Epoch.delegation a.data
      let (e, warming, cooling) := Epoch.status d ended oldHistory.data
      effective := Alpenglow.saturating effective e
      activating := Alpenglow.saturating activating warming
      deactivating := Alpenglow.saturating deactivating cooling
      let mut v := Sbpf.accountAt validatorSlots validators d.voter
      if v == Sbpf.notFound then
        v := validators.size
        validatorSlots := Sbpf.accountLink validatorSlots validators d.voter v
        validators := validators.push (← world.get d.voter)
        before := before.push 0
        after := after.push 0
      before := before.set! v (before[v]! + e)
      stakeKeys := stakeKeys ++ a.key
      stakes := stakes.push d
      balances := balances.push a.lamports
      minimums := minimums.push (machine.rentMinimum a.data.size)
      effectives := effectives.push e
      actives := actives.push (if e != 0 || warming != 0 then 1 else 0)
      validatorOf := validatorOf.push v
  -- the history gains the epoch that ended, and with it each validator's stake in the new epoch is known
  let history := Epoch.historyWith oldHistory.data ended effective activating deactivating
  for k in [0:stakes.size] do
    let (e, _, _) := Epoch.status stakes[k]! epoch history
    let v := validatorOf[k]!
    after := after.set! v (after[v]! + e)
  -- ---- the validators admitted to the epoch after this one: a vote account in today's layout with a BLS
  -- key, stake, and enough lamports to pay its admission and still hold its account
  let admission : UInt64 := 800000000
  let mut admitted : Array Nat := Array.emptyWithCapacity 1024
  let mut isAdmitted : Array UInt64 := Array.replicate validators.size 0
  for v in [0:validators.size] do
    let a := validators[v]!
    if a.owner == Bank.voteProgram && a.data.size == 3762 && Wire.u32 a.data 0 == 3 && a.data[144]! == 1 && after[v]! != 0
        && a.lamports >= machine.rentMinimum 3762 + admission then
      -- (kept in order of address, as one of the accounts below lists them)
      let mut at_ := admitted.size
      admitted := admitted.push v
      while at_ > 0 && Alpenglow.keyBefore a.key validators[admitted[at_ - 1]!]!.key do
        admitted := (admitted.set! at_ admitted[at_ - 1]!).set! (at_ - 1) v
        at_ := at_ - 1
      isAdmitted := isAdmitted.set! v 1
  -- ---- every stake account's reward, and what its validator keeps of it
  let mut rows := ByteArray.emptyWithCapacity (56 * stakes.size)
  let mut stakeRewards : UInt64 := 0
  let mut kept : Array UInt64 := Array.replicate validators.size 0
  -- (each admitted validator's commission, as it stood an epoch or two ago, and its last entry of credits)
  let mut terms : Array UInt64 := Array.replicate (4 * validators.size) 0
  for v in admitted do
    let a := validators[v]!
    let earlier := commissionIn manifest ended a.key
    let later := if earlier != 0xFFFFFFFFFFFFFFFF then earlier else commissionIn manifest epoch a.key
    terms := terms.set! (4 * v) (if later != 0xFFFFFFFFFFFFFFFF then later else Wire.u16 a.data 132)
    let credits := (Alpenglow.VoteState.parse a.data).credits
    if credits.size >= 3 then
      for i in [0:3] do
        terms := terms.set! (4 * v + 1 + i) credits[credits.size - 3 + i]!
  for k in [0:stakes.size] do
    let v := validatorOf[k]!
    let r := Epoch.reward stakes[k]! ended effectives[k]! (actives[k]! != 0) balances[k]! minimums[k]! (isAdmitted[v]! != 0)
      terms[4 * v + 1]! terms[4 * v + 2]! terms[4 * v + 3]! before[v]! terms[4 * v]!
    if r.due then
      rows := Wire.putU64 (Wire.putU64 (Wire.putU64 (stakeKeys.copySlice (32 * k) rows rows.size 32) r.staker) r.stake) r.credits
      stakeRewards := stakeRewards + r.staker
      kept := kept.set! v (kept[v]! + r.commission)
  -- ---- the accounts written: the admitted validators' stakes of the epoch that ended, on record
  let mut listing := Wire.putU64 (Wire.putU64 (ByteArray.emptyWithCapacity (16 + 40 * admitted.size)) ended) admitted.size.toUInt64
  for v in admitted do
    listing := Wire.putU64 (listing ++ validators[v]!.key) before[v]!
  let mut writes : Array Sbpf.Account := Array.emptyWithCapacity (admitted.size + 16)
  writes := writes.push ⟨delegatedStakesAccount, Sbpf.systemProgram, machine.rentMinimum 80016, listing, false⟩
  -- each admitted validator pays its admission, which is burned, and collects its commission, unless it names
  -- another address to collect it: a system account that the commission leaves able to hold itself, or
  -- the incinerator; anything else, and the commission is not paid
  let mut ashes ← world.get Bank.incinerator
  ashes := { ashes with lamports := ashes.lamports + admission * admitted.size.toUInt64 }
  let mut paid : UInt64 := 0
  let mut burned : UInt64 := 0
  let mut others : Array ByteArray := Array.emptyWithCapacity 8
  let mut owed : Array UInt64 := Array.emptyWithCapacity 8
  for v in admitted do
    let a := validators[v]!
    let collector := a.data.extract 68 100
    writes := writes.push { a with lamports := a.lamports - admission + (if collector == a.key then kept[v]! else 0) }
    if collector == a.key then
      paid := paid + kept[v]!
    else if kept[v]! != 0 then
      let at_ := keyIndex others collector
      if at_ == Sbpf.notFound then
        others := others.push collector
        owed := owed.push kept[v]!
      else
        owed := owed.set! at_ (owed[at_]! + kept[v]!)
  for c in [0:others.size] do
    let mut at_ := Sbpf.notFound
    for w in [0:writes.size] do
      if writes[w]!.key == others[c]! then
        at_ := w
    let account ← if at_ != Sbpf.notFound then pure writes[at_]! else world.get others[c]!
    if others[c]! == Bank.incinerator then
      ashes := { ashes with lamports := ashes.lamports + owed[c]! }
    else if account.owner != Sbpf.systemProgram || Bank.reserved others[c]!
        || (account.lamports == 0 && owed[c]! < machine.rentMinimum account.data.size) then
      burned := burned + owed[c]!
    else
      paid := paid + owed[c]!
      let richer := { account with lamports := account.lamports + owed[c]! }
      writes := if at_ != Sbpf.notFound then writes.set! at_ richer else writes.push richer
  let incinerated := ashes.lamports - (← world.get Bank.incinerator).lamports - admission * admitted.size.toUInt64
  writes := writes.push ashes
  -- the rewards about to be paid, on record: from which block on, over how many, and how much of the
  -- budget of the epoch that ended has gone out
  let mut partitions := (rows.size / 56 + 2047) / 2048
  if partitions == 0 then
    partitions := 1
  if partitions > (manifest.slotsPerEpoch / 10).toNat then
    partitions := (manifest.slotsPerEpoch / 10).toNat
  let oldRewards ← world.get Sbpf.epochRewardsSysvar
  let oldBudget ← world.get voteRewardAccount
  let mut record := Wire.putU64 (Wire.putU64 (ByteArray.emptyWithCapacity 81) (height + 1)) partitions.toUInt64 ++ blockhash
  record := Wire.putU64 (Wire.putU64 (Sbpf.zeros record 16) (Wire.u64 oldBudget.data 0)) (paid + incinerated + burned)
  writes := writes.push { oldRewards with data := record.push 1 }
  -- the new epoch's budget, from the supply as these rewards will leave it; the old one stays beside it
  let budget := Epoch.budget manifest.inflation epoch manifest.slotsPerEpoch (supply + paid + stakeRewards)
  let mut state := Wire.putU64 (Wire.putU64 (Wire.putU64 (ByteArray.emptyWithCapacity 49) budget) manifest.slotsPerEpoch) epoch
  state := if oldBudget.data.size >= 24 then state.push 1 ++ oldBudget.data.extract 0 24 else state.push 0
  writes := writes.push ⟨voteRewardAccount, Sbpf.systemProgram, machine.rentMinimum state.size, state, false⟩
  writes := writes.push { oldHistory with data := history }
  -- (the two accounts made here hold what their size requires: the supply moves if that has changed)
  let oldListing ← world.get delegatedStakesAccount
  let supplyNow := supply + paid + incinerated + (machine.rentMinimum 80016 - oldListing.lamports) + (machine.rentMinimum state.size - oldBudget.lamports)
  -- ---- the stake rewards, grouped by the block that pays each
  let mut which : Array Nat := Array.emptyWithCapacity (rows.size / 56)
  let mut starts : Array Nat := Array.replicate (partitions + 1) 0
  for k in [0:rows.size / 56] do
    let p := (Epoch.partition blockhash (rows.extract (56 * k) (56 * k + 32)) partitions.toUInt64).toNat
    which := which.push p
    starts := starts.set! (p + 1) (starts[p + 1]! + 1)
  for p in [0:partitions] do
    starts := starts.set! (p + 1) (starts[p + 1]! + starts[p]!)
  let mut place := starts
  let mut grouped := Sbpf.zeros (ByteArray.emptyWithCapacity rows.size) rows.size
  for k in [0:which.size] do
    grouped := rows.copySlice (56 * k) grouped (56 * place[which[k]!]!) 56
    place := place.set! which[k]! (place[which[k]!]! + 1)
  -- ---- the stakes of the epoch after this one: the admitted validators, with their stake in this one
  let mut voters : Array Snapshot.Voter := Array.emptyWithCapacity admitted.size
  let mut total : UInt64 := 0
  for v in admitted do
    let a := validators[v]!
    voters := voters.push ⟨a.key, a.data.extract 4 36, after[v]!, a.data.extract 145 193, a.data.extract 100 132, Wire.u16 a.data 132⟩
    total := total + after[v]!
  IO.println s!"epoch {epoch}: {stakes.size} stake accounts, {admitted.size} validators admitted; {Fmt.thousands (paid + incinerated + burned)} lamports of commission and {Fmt.thousands stakeRewards} of stake rewards, the latter to {rows.size / 56} accounts over {partitions} blocks; the epoch's budget is {Fmt.thousands budget}"
  return (writes, supplyNow, grouped, starts, ⟨epoch + 1, total, voters⟩)

/-- Pays the stake rewards `rows[from_, to)` of the epoch `ended` (see `turn`): each stake account gains
its reward and takes on the stake and credits worked out for it, the stake no more than its balance can
back. Returns the accounts as it leaves them, among them the record of what has been paid, which `last`
closes; and the lamports created. -/
def pay (world : World) (machine : Sbpf.Machine) (rows : ByteArray) (from_ to : Nat) (ended : UInt64) (last : Bool)
    : IO (Array Sbpf.Account × UInt64) := do
  let mut writes : Array Sbpf.Account := Array.emptyWithCapacity (to - from_ + 1)
  let mut created : UInt64 := 0
  let mut owed : UInt64 := 0
  for k in [from_:to] do
    let a ← world.get (rows.extract (56 * k) (56 * k + 32))
    let reward := Wire.u64 rows (56 * k + 32)
    owed := owed + reward
    -- (a stake account closed since the epoch ended has lost its reward)
    if a.owner == Bank.stakeProgram && a.lamports != 0 && Epoch.delegated a.data then
      let minimum := machine.rentMinimum a.data.size
      let backed := if a.lamports + reward < minimum then 0 else a.lamports + reward - minimum
      let stake := if Wire.u64 rows (56 * k + 40) < backed then Wire.u64 rows (56 * k + 40) else backed
      let mut data := Sbpf.storeAt (Sbpf.storeAt a.data 156 8 stake) 188 8 (Wire.u64 rows (56 * k + 48))
      if stake == 0 && Wire.u64 rows (56 * k + 40) != 0 then
        data := Sbpf.storeAt data 172 8 ended
      writes := writes.push { a with lamports := a.lamports + reward, data := data }
      created := created + reward
  let record ← world.get Sbpf.epochRewardsSysvar
  let mut data := Sbpf.storeAt record.data 72 8 (Wire.u64 record.data 72 + owed)
  if last then
    data := data.set! 80 0
  return (writes.push { record with data := data }, created)

/-- An epoch's stakes as `turn` worked them out, for a file: the epoch, the total, and for each validator
its vote account, identity, stake, commission, BLS key and fee collector (160 bytes). -/
def stakesBytes (e : Snapshot.EpochStakes) : ByteArray := Id.run do
  let mut b := u64 e.epoch ++ u64 e.total
  for v in e.voters do
    b := b ++ v.vote ++ v.node ++ u64 v.stake ++ u64 v.commission ++ v.bls ++ v.collector
  return b

def stakesOfBytes (b : ByteArray) : Snapshot.EpochStakes := Id.run do
  let mut voters : Array Snapshot.Voter := Array.emptyWithCapacity (b.size / 160)
  for k in [0:(b.size - 16) / 160] do
    let o := 16 + 160 * k
    voters := voters.push ⟨b.extract o (o + 32), b.extract (o + 32) (o + 64), Wire.u64 b (o + 64), b.extract (o + 80) (o + 128),
      b.extract (o + 128) (o + 160), Wire.u64 b (o + 72)⟩
  return ⟨Wire.u64 b 0, Wire.u64 b 8, voters⟩

def bankMagic : ByteArray := "LSBANK01".toUTF8

/-- Saves the state as of `slot` for a later run to go on from: the changed accounts to the log, then
`bank.bin` beside it (a tag, the slot, the length of the log, the bank hash, the blockhash, the lattice
hash, the supply, the block height, the recent blockhashes), which is what makes the log's new end
count; before it `stake-keys.bin`, the stake accounts met since the snapshot. (An epoch's turn leaves
two more files there: the stakes it worked out, and the rewards being paid.) The blocks executed since
`from_` are no longer needed. This survives the process being killed at any moment. -/
def checkpoint (w : World) (dir blocksDir : String) (from_ slot : UInt64) (bankHash latest : ByteArray) (sum : Array UInt64)
    (supply height : UInt64) (recent stakeKeys : ByteArray) : IO World := do
  let saved ← w.save slot
  let log := saved.overlays[0]!
  Sys.sync log.fd
  let _ ← Sys.writeFileAtomic s!"{dir}/stake-keys.bin" stakeKeys
  let bank := bankMagic ++ u64 slot ++ u64 log.flushed ++ bankHash ++ latest ++ LtHash.bytes sum ++ u64 supply ++ u64 height ++ recent
  if log.failed || !(← Sys.writeFileAtomic s!"{dir}/bank.bin" bank) then
    fail s!"cannot save the state in {dir}"
  let mut s := from_ + 1
  while s <= slot do
    Sys.unlink s!"{blocksDir}/{s}.block"
    s := s + 1
  return saved

def main : IO Unit := do
  let argc ← Sys.argc
  let mut stateDir := ""
  let mut blocksDir := ""
  let mut count := 0
  let mut live := false
  let mut resume := false
  let mut until_ : UInt64 := 0
  let mut node := "127.0.0.1:9184"
  let mut fetchers := 24
  let mut lines := false
  -- for looking into a block that does not match: carry on from the block's own bank hash, so that what
  -- later blocks read of it (the slot hashes) is right and their transactions can still be compared
  let mut follow := false
  -- say where each block's time went
  let mut timing := false
  let mut interpret := false
  let mut checkers := 3
  let mut trace := Sbpf.notFound
  let mut cap : UInt64 := 0
  let mut traceSlot : UInt64 := 0
  let mut i := 2
  while i < argc do
    let a ← Sys.arg i
    if a == "--lines" then
      lines := true
      i := i + 1
    else if a == "--follow" then
      follow := true
      i := i + 1
    else if a == "--timing" then
      timing := true
      i := i + 1
    else if a == "--interpret" then
      interpret := true
      i := i + 1
    else if a == "--live" then
      live := true
      i := i + 1
    else if a == "--resume" then
      resume := true
      i := i + 1
    else if a == "--help" then
      IO.print usage
      return
    else if i + 1 >= argc then
      fail s!"{a} needs a value\n{usage}"
    else
      let v ← Sys.arg (i + 1)
      if a == "--state" then
        stateDir := v
      else if a == "--blocks" then
        blocksDir := v
      else if a == "--until" then
        until_ := RunBlock.number v
      else if a == "--node" then
        node := v
      else if a == "--fetchers" then
        fetchers := (RunBlock.number v).toNat
      else if a == "--signatures" then
        checkers := (RunBlock.number v).toNat
      else if a == "--count" then
        count := (RunBlock.number v).toNat
      else if a == "--trace" then
        trace := (RunBlock.number v).toNat
      else if a == "--cap" then
        cap := RunBlock.number v
      else if a == "--at" then
        traceSlot := RunBlock.number v
      else
        fail s!"unknown option {a}\n{usage}"
      i := i + 2
  if stateDir == "" || blocksDir == "" then
    fail usage
  if live then
    checkers := 0
  else if count == 0 then
    count := 1
  -- ---- the processes that check signatures, started before there is much to copy
  let mut askChecker : Array UInt64 := Array.emptyWithCapacity checkers
  let mut hearChecker : Array UInt64 := Array.emptyWithCapacity checkers
  if checkers > 16 then
    checkers := 16
  if checkers != 0 then
    Sys.ignoreBrokenPipes
    for w in [0:checkers] do
      let (requests, ask) ← Sys.pipe
      let (hear, answers) ← Sys.pipe
      let pid ← Sys.fork
      if pid == 0 then
        Sys.dieWithParent
        Sys.close ask
        Sys.close hear
        for fd in askChecker do
          Sys.close fd
        signatureWorker blocksDir w checkers requests answers
        Sys.exit 0
      if Sys.isErr pid then
        fail "cannot start a process to check signatures"
      Sys.close requests
      Sys.close answers
      askChecker := askChecker.push ask
      hearChecker := hearChecker.push hear
  let mut signaturesChecked : UInt64 := 0
  let mut signaturesBad : UInt64 := 0
  -- ---- the state
  let state ← Sys.readFile s!"{stateDir}/state.json" 65536
  let shardCount := (RunBlock.number (RunBlock.jsonField state "shards" 0)).toNat
  let seedBytes := Hex.decode (RunBlock.jsonField state "seed" 0)
  if shardCount == 0 || seedBytes.size != 8 || RunBlock.jsonField state "format" 0 != "2" then
    fail s!"{stateDir} holds no store this version can read"
  let seed := Wire.u64 seedBytes 0
  let mut shards : Array Accounts.Shard := Array.emptyWithCapacity shardCount
  for id in [0:shardCount] do
    let shard ← Accounts.Shard.openRead stateDir id seed
    if shard.failed then
      fail s!"cannot open shard {id} of {stateDir}"
    shards := shards.push shard
  let mfd ← Sys.openFile s!"{stateDir}/manifest.bin" 0
  let mut manifest := Snapshot.parse (← Sys.readAt mfd 0 (← Sys.fileSize mfd).toNat)
  Sys.close mfd
  if manifest.error != "" then
    fail s!"{stateDir}/manifest.bin: {manifest.error}"
  -- ---- what the bank carries from block to block: as the snapshot left it, or with --live as an earlier
  -- run saved it (see `checkpoint`)
  let mut slot := manifest.slot
  let mut bankHash := manifest.hash
  let mut sum := LtHash.ofBytes manifest.ltHash
  let mut latest := manifest.blockhash
  -- the lamports in existence and the number of blocks so far
  let mut supply := manifest.capitalization
  let mut height := manifest.blockHeight
  -- recent blockhashes, newest last, with their positions: a transaction must name one of the last 150
  -- (the manifest keeps them in no order, each with its number)
  let mut recent := ByteArray.emptyWithCapacity (40 * 512)
  for back in [0:151] do
    for k in [0:manifest.queue.size / 56] do
      if Wire.u64 manifest.queue (56 * k + 40) + 150 == manifest.lastHashIndex + back.toUInt64 then
        recent := recent ++ manifest.queue.extract (56 * k) (56 * k + 32)
  let dir := s!"{stateDir}/{if live then "live" else "replay"}"
  Sys.mkdir dir
  let saved ← Sys.readFile s!"{stateDir}/live/bank.bin" 16384
  let resumed := (live || resume) && saved.size >= 2152 && saved.extract 0 8 == bankMagic
  if resume && !resumed then
    fail s!"{stateDir}/live holds no saved state"
  -- (the log of changes: the one --live keeps, or a new one, over that one if resuming)
  let mut logs : Array Accounts.Shard := Array.emptyWithCapacity 2
  if !(live && resumed) then
    logs := logs.push (← Accounts.Shard.create dir 0 seed)
  if resumed then
    logs := logs.push (← Accounts.Shard.reopen s!"{stateDir}/live" 0 seed (Wire.u64 saved 16) live)
  for log in logs do
    if log.failed then
      fail s!"cannot open the log of changes in {dir}"
  if resumed then
    slot := Wire.u64 saved 8
    bankHash := saved.extract 24 56
    latest := saved.extract 56 88
    sum := LtHash.ofBytes (saved.extract 88 2136)
    supply := Wire.u64 saved 2136
    height := Wire.u64 saved 2144
    recent := saved.extract 2152 saved.size
  let mut world : World := ⟨shards, logs, Array.replicate heldSlots 0, Array.emptyWithCapacity 1024, 0, Array.emptyWithCapacity 1024, Array.emptyWithCapacity 1024⟩
  let mut machine := { Sbpf.Machine.create ⟨0, 0, 0, 0, 0⟩ 200000 with interpret := interpret }
  let mut leaderVotes := LeaderSchedule.table manifest 1
  let mut leaderCollectors := LeaderSchedule.table manifest 2
  -- every stake account that may be delegated (some more than once), and the stake rewards of the epoch
  -- that ended, while they are being paid (see `turn`)
  let mut stakeKeys := manifest.stakeKeys
  let mut owing := ByteArray.empty
  let mut owingFrom : Array Nat := Array.emptyWithCapacity 0
  if resumed then
    stakeKeys := stakeKeys ++ (← Sys.readFile s!"{stateDir}/live/stake-keys.bin" 0x10000000)
    -- the stakes of epochs the snapshot did not know, and rewards still being paid
    let mut known := manifest.epochStakes
    let mut newest : UInt64 := 0
    for e in known do
      if e.epoch > newest then
        newest := e.epoch
    for _ in [0:8] do
      let more ← Sys.readFile s!"{stateDir}/live/stakes-{newest + 1}.bin" 0x1000000
      if more.size >= 16 then
        known := known.push (stakesOfBytes more)
        newest := newest + 1
    manifest := { manifest with epochStakes := known }
    leaderVotes := LeaderSchedule.table manifest 1
    leaderCollectors := LeaderSchedule.table manifest 2
    if (← world.get Sbpf.epochRewardsSysvar).data[80]! == 1 then
      let file ← Sys.readFile s!"{stateDir}/live/rewards.bin" 0x10000000
      let shares := (Wire.u64 file 0).toNat
      for k in [0:shares] do
        owingFrom := owingFrom.push (Wire.u64 file (8 + 8 * k)).toNat
      owing := file.extract (8 + 8 * shares) file.size
  IO.println s!"state        slot {slot}, bank hash {Base58.encode bankHash}"
  -- ---- with --live: the processes that fetch missing blocks
  let mut askFetcher : Array UInt64 := Array.emptyWithCapacity fetchers
  if live then
    Sys.ignoreBrokenPipes
    let leaders := LeaderSchedule.table manifest 0
    for _ in [0:fetchers] do
      let (requests, ask) ← Sys.pipe
      let pid ← Sys.fork
      if pid == 0 then
        Sys.dieWithParent
        Sys.close ask
        for fd in askFetcher do
          Sys.close fd
        fetcher blocksDir node leaders requests
        Sys.exit 0
      if Sys.isErr pid then
        fail "cannot start a process to fetch blocks"
      Sys.close requests
      askFetcher := askFetcher.push ask
  let (nodeIp, nodePort) := RunBlock.parseAddr node
  -- the cluster's newest slot, as the node last said; when each slot's block was last asked for
  let mut tip : UInt64 := 0
  let mut asked : Array UInt64 := Array.replicate 4096 0
  let mut looked : UInt64 := 0
  -- the slot whose state is saved, and when it was
  let mut savedSlot := slot
  let mut savedAt ← Sys.nowMs
  let mut reported ← Sys.nowMs
  let mut reportedAt := 0
  let mut waiting : Array Waiting := Array.emptyWithCapacity 256
  let mut n := 0
  let mut rankedOrder : Array Snapshot.Voter := Array.emptyWithCapacity 0
  let mut rankedEpoch : UInt64 := 0
  let mut signers : Alpenglow.Signers := Alpenglow.signers 0 (Array.emptyWithCapacity 0)
  let mut certified := 0
  -- the id of the block last executed, once one has been
  let mut lastId := ByteArray.empty
  repeat
    if (count != 0 && n == count) || (until_ != 0 && slot >= until_) then
      break
    -- ---- the next block
    let mut chosen := Sbpf.notFound
    if live then
      -- what has arrived in the directory since
      for s in [1:257] do
        if waitingAt waiting (slot + s.toUInt64) == Sbpf.notFound then
          let w ← savedBlock blocksDir (slot + s.toUInt64)
          if w.block.error == "" then
            waiting := waiting.push w
      let (found, _, known) := next waiting slot lastId true
      if found == Sbpf.notFound && waitingAt waiting known != Sbpf.notFound then
        fail s!"the block held for slot {known} is not the one the chain made final: their ids differ"
      chosen := found
      let mut missing := known
      if chosen == Sbpf.notFound then
        -- no footer already checked leads on: the latest that would is checked, and dropped if it does not hold
        let (unproven, via, more) := next waiting slot lastId false
        if missing == 0 then
          missing := more
        if via != Sbpf.notFound then
          let w := waiting[via]!
          signers := signersFor manifest signers w.final.finalSlot
          if Alpenglow.finalProven w.final signers w.version then
            waiting := waiting.set! via { w with proven := true }
            chosen := unproven
            certified := certified + 1
          else
            IO.println s!"slot {w.slot}: its certificate that slot {w.final.finalSlot} is final does not hold, and is ignored"
            waiting := waiting.set! via { w with final := Alpenglow.parse ByteArray.empty }
            continue
      -- blocks that are not here are asked for: those the chain is known to need, and those old enough
      -- that the node should have delivered them by now
      let now ← Sys.nowMs
      if now - looked >= 500 then
        looked := now
        tip := RunBlock.number (RunBlock.jsonField (← RunBlock.httpGet nodeIp nodePort "/summary.json") "tipSlot" 0)
        for s in [1:257] do
          let want := slot + s.toUInt64
          if (want == missing || (want + 16 <= tip && !(skipped waiting want))) && waitingAt waiting want == Sbpf.notFound
              && now - asked[(want % 4096).toNat]! > (if want == missing then 8000 else 30000) then
            asked := asked.set! (want % 4096).toNat now
            let _ ← Sys.writeFully askFetcher[(want % askFetcher.size.toUInt64).toNat]! (u64 want)
      if chosen == Sbpf.notFound then
        IO.sleep 20
        continue
    else
      -- the first block saved after this one, which must be built on it
      for s in [1:65] do
        if waiting.size == 0 then
          let w ← savedBlock blocksDir (slot + s.toUInt64)
          if w.block.error == "" then
            waiting := waiting.push w
      if waiting.size == 0 then
        fail s!"no block is saved for the slots after {slot}"
      if waiting[0]!.parent != slot then
        fail s!"the block saved for slot {waiting[0]!.slot} is built on slot {waiting[0]!.parent}, and the state is that of slot {slot}"
      chosen := 0
      -- (a block whose certificate does not hold is no block; checked with the signatures)
      let w := waiting[0]!
      if checkers != 0 && w.final.finalSlot != 0 then
        signers := signersFor manifest signers w.final.finalSlot
        if !(Alpenglow.finalProven w.final signers w.version) then
          fail s!"slot {w.slot}: its certificate that slot {w.final.finalSlot} is final does not hold"
    let parent := slot
    slot := waiting[chosen]!.slot
    lastId := waiting[chosen]!.id
    let block := waiting[chosen]!.block
    let mut later : Array Waiting := Array.emptyWithCapacity 256
    for w in waiting do
      if w.slot > slot then
        later := later.push w
    waiting := later
    -- (the signature checkers start on the block at once, each reading it for itself)
    for fd in askChecker do
      let _ ← Sys.writeFully fd (u64 slot)
    let started ← Sys.nowMs
    let mut mark ← Sys.nowUs
    let mut usLoad : UInt64 := 0
    let mut usRun : UInt64 := 0
    let mut usKeep : UInt64 := 0
    -- every account this block changes, as it was before the block
    let mut touched : Array Sbpf.Account := Array.emptyWithCapacity 4096
    let mut touchedSlots : Array UInt64 := Array.replicate 65536 0
    -- what each of them added to the lattice hash, where the last block to change it left that on record
    let mut touchedHashes : Array ByteArray := Array.emptyWithCapacity 4096
    -- ---- a new bank: the parent's hash joins the recent slot hashes, and the clock moves to this slot
    let oldHashes ← world.get Sbpf.slotHashesSysvar
    let newHashes := { oldHashes with data := slotHashesWith oldHashes.data parent bankHash }
    let oldClock ← world.get Sbpf.clockSysvar
    let epoch := if manifest.slotsPerEpoch == 0 then 0 else manifest.firstNormalEpoch + (slot - manifest.firstNormalSlot) / manifest.slotsPerEpoch
    -- the first block of an epoch settles the one that ended, and starts its own clock
    let turning := Wire.u64 oldClock.data 16 != epoch
    let newClock := { oldClock with data := clockData slot (Wire.u64 oldClock.data (if turning then 32 else 8)) epoch (epoch + 1) (Wire.u64 oldClock.data 32) }
    height := height + 1
    -- (what an account must hold is asked of the machine below: it needs the chain's rent from the start)
    let rent ← world.get Sbpf.rentSysvar
    machine := { machine with sysvars := { machine.sysvars with rent := rent.data } }
    let mut opening : Array Sbpf.Account := Array.emptyWithCapacity 2
    if turning then
      let (writes, supplyNow, rows, starts, nextStakes) ← turn world machine manifest (Epoch.distinct stakeKeys) epoch supply height latest
      opening := writes
      supply := supplyNow
      owing := rows
      owingFrom := starts
      manifest := { manifest with epochStakes := manifest.epochStakes.push nextStakes }
      leaderVotes := LeaderSchedule.table manifest 1
      leaderCollectors := LeaderSchedule.table manifest 2
      -- (kept in files too, for a run that goes on from a state saved after this)
      let mut shares := u64 starts.size.toUInt64
      for from_ in starts do
        shares := shares ++ u64 from_.toUInt64
      if !(← Sys.writeFileAtomic s!"{dir}/stakes-{epoch + 1}.bin" (stakesBytes nextStakes)) || !(← Sys.writeFileAtomic s!"{dir}/rewards.bin" (shares ++ rows)) then
        fail s!"cannot write to {dir}"
    else if owing.size != 0 then
      -- the blocks after it each pay a share of the stake rewards
      let first := Wire.u64 (← world.get Sbpf.epochRewardsSysvar).data 0
      if height >= first && (height - first).toNat + 1 < owingFrom.size then
        let share := (height - first).toNat
        let (writes, created) ← pay world machine owing owingFrom[share]! owingFrom[share + 1]! (epoch - 1) (share + 2 == owingFrom.size)
        opening := writes
        supply := supply + created
        if share + 2 == owingFrom.size then
          owing := ByteArray.empty
    for a in (opening.push newHashes).push newClock do
      let was ← world.get a.key
      touchedSlots := Sbpf.accountLink touchedSlots touched was.key touched.size
      touched := touched.push was
      touchedHashes := touchedHashes.push (world.hashOf was.key)
      world := world.keep a true
    let schedule ← world.get Sbpf.epochScheduleSysvar
    let rewards ← world.get Sbpf.epochRewardsSysvar
    let history ← world.get Sbpf.stakeHistorySysvar
    let restart ← world.get Sbpf.lastRestartSlotSysvar
    let clock : Sbpf.Clock := ⟨slot, Wire.u64 newClock.data 8, epoch, epoch + 1, Wire.u64 newClock.data 32⟩
    let sysvars : Sbpf.Sysvars := ⟨rent.data, schedule.data, rewards.data, newHashes.data, history.data, Wire.u64 restart.data 0⟩
    -- (programs may ask for the stake active in this epoch: it was settled when the epoch began, as the next one's stakes)
    if machine.stakes.size == 0 || turning then
      let current := stakesOf manifest (epoch + 1)
      let mut packed := u64 current.total
      for v in current.voters do
        packed := Wire.putU64 (packed ++ v.vote) v.stake
      machine := { machine with stakes := packed }
    machine := { machine with clock := clock, blockhash := latest, lamportsPerSignature := 5000, sysvars := sysvars }
    -- ---- the transactions, in order
    let mut signatures : UInt64 := 0
    let mut fees : UInt64 := 0
    -- of the fees: what was paid per signature (half of it is burned), the rest being priority fees
    let mut signatureFees : UInt64 := 0
    let mut failedCount := 0
    let mut units : UInt64 := 0
    for t in [0:block.transactions.size] do
      let tx := block.transactions[t]!
      let msg := tx.message
      -- its accounts: those it names, those it takes from address tables, the tables, and the code of its programs
      let mut keys := msg.keys
      let mut accounts : Array Sbpf.Account := Array.emptyWithCapacity (keys.size + 16)
      for pass in [0:2] do
        for l in msg.lookups do
          let table ← world.get l.table
          if pass == 0 then
            accounts := accounts.push table
          for index in (if pass == 0 then l.writable else l.readonly) do
            let at_ := 56 + 32 * index.toNat
            if at_ + 32 <= table.data.size then
              keys := keys.push (table.data.extract at_ (at_ + 32))
      let named := accounts.size
      for key in keys do
        let (remembering, a) ← world.fetch key
        world := remembering
        accounts := accounts.push a
      if lines then
        IO.println s!"begin {t}"
      if timing then
        let now ← Sys.nowUs
        usLoad := usLoad + (now - mark)
        mark := now
      for k in [named:named + keys.size] do
        let a := accounts[k]!
        -- (unless the transaction names that account itself, as one closing the program does)
        if a.owner == Sbpf.loaderId && Sbpf.loaderKind a == 2 && !(Bank.hasProgram ⟨machine, #[], latest, 5000⟩ a.key)
            && keyIndex keys (a.data.extract 4 36) == Sbpf.notFound then
          accounts := accounts.push (← world.get (a.data.extract 4 36))
      -- a transaction names a recent blockhash, or else the value in a nonce account
      let mut known := false
      for k in [0:recent.size / 32] do
        if Wire.eqAt recent (32 * k) msg.blockhash 0 32 then
          known := true
      let traced := t == trace && (if traceSlot == 0 then n == 0 else slot == traceSlot)
      let capped := if traced then cap else 0
      let bank : Bank.Bank := ⟨{ machine with cap := capped }, accounts, (if known then msg.blockhash else latest), 5000⟩
      let receipt := bank.process tx false
      if timing then
        let now ← Sys.nowUs
        usRun := usRun + (now - mark)
        mark := now
      machine := { receipt.bank.machine with clock := clock }
      signatures := signatures + tx.signatures.size.toUInt64
      units := units + receipt.units
      if receipt.error != "" then
        failedCount := failedCount + 1
      if receipt.charged then
        fees := fees + receipt.fee
        let mut paidFor := tx.signatures.size.toUInt64
        for ix in msg.instructions do
          if ix.program < keys.size then
            let program := keys[ix.program]!
            if program == Bank.ed25519Program || program == Bank.secp256k1Program || program == Bank.secp256r1Program then
              paidFor := paidFor + Wire.u8 ix.data 0
        signatureFees := signatureFees + 5000 * paidFor
      -- what it changed goes to the overlay
      let mut balances := ""
      for k in [0:keys.size] do
        let was := accounts[named + k]!
        let found := Bank.find receipt.bank.accounts keys[k]!
        let now := if found == Sbpf.notFound then absent keys[k]! else receipt.bank.accounts[found]!
        if lines then
          balances := if k == 0 then toString now.lamports else s!"{balances},{now.lamports}"
        if !(same was now) then
          if Sbpf.accountAt touchedSlots touched was.key == Sbpf.notFound then
            touchedSlots := Sbpf.accountLink touchedSlots touched was.key touched.size
            touched := touched.push was
            touchedHashes := touchedHashes.push (world.hashOf was.key)
          world := world.keep now true
          if now.owner == Bank.stakeProgram then
            stakeKeys := stakeKeys ++ now.key
      if timing then
        let now ← Sys.nowUs
        usKeep := usKeep + (now - mark)
        mark := now
      if lines then
        IO.println s!"tx {t} {Base58.encode tx.signatures[0]!} err={if receipt.error == "" then "-" else receipt.error} charged={receipt.charged} fee={receipt.fee} cu={receipt.units} bal={balances}"
        for line in receipt.logs do
          IO.println s!"log {t} {line}"
        -- token accounts among its accounts, and what they hold afterwards (the amount is 8 bytes at offset 64)
        let mut tokens := ""
        for k in [0:keys.size] do
          let found := Bank.find receipt.bank.accounts keys[k]!
          if found != Sbpf.notFound then
            let a := receipt.bank.accounts[found]!
            if a.data.size >= 165 && (a.owner == tokenProgram || a.owner == token2022Program) && a.data.size != 82 && Wire.u8 a.data 108 != 0 then
              tokens := tokens ++ s!" {k}:{Wire.u64 a.data 64}"
        IO.println s!"tokens {t}{tokens}"
        let mut calls := ""
        for f in receipt.frames do
          calls := calls ++ s!" {f.depth}:{Base58.encode f.program}"
        IO.println s!"calls {t}{calls}"
        if receipt.why != "" then
          let mut missing := ""
          if RunBlock.findAt receipt.why.toUTF8 "status 6,".toUTF8 0 == 0 then
            for a in accounts do
              if a.data.size > 4 && Wire.u32 a.data 0 == 0x464c457f then
                missing := missingCalls a.data missing
              else if a.data.size > 49 && Wire.u32 a.data 45 == 0x464c457f then
                missing := missingCalls a.data missing
            for id in machine.ids do
              let code ← world.get id
              if code.owner == Sbpf.loaderId && code.data.size >= 36 then
                let holder ← world.get (code.data.extract 4 36)
                let mut used := false
                for key in keys do
                  if key == id then
                    used := true
                if used then
                  missing := missingCalls holder.data missing
          IO.println s!"why {t} {receipt.why}{if missing != "" then s!" · lacks:{missing}" else ""}"
      if traced then
        IO.println s!"    [{receipt.error}] [{receipt.why}] {receipt.units} units"
        for line in receipt.logs do
          IO.println s!"    {line}"
        for f in receipt.frames do
          let mut refs := ""
          for mt in f.metas do
            refs := refs ++ s!" {mt.index}{if mt.signer then "s" else ""}{if mt.writable then "w" else ""}"
          IO.println s!"    depth {f.depth} {Base58.encode f.program}:{refs} · {Hex.encode (f.data.extract 0 16)}"
        for k in [0:keys.size] do
          let found := Bank.find receipt.bank.accounts keys[k]!
          IO.println s!"    account {k} {Base58.encode keys[k]!} {accounts[named + k]!.lamports} -> {if found == Sbpf.notFound then 0 else receipt.bank.accounts[found]!.lamports}"
          if found != Sbpf.notFound && receipt.bank.accounts[found]!.data != accounts[named + k]!.data && receipt.bank.accounts[found]!.data.size <= 200 then
            IO.println s!"      data was {Hex.encode accounts[named + k]!.data}"
            IO.println s!"      data now {Hex.encode receipt.bank.accounts[found]!.data}"
        Sys.exit 0
    -- ---- the block's end
    let mut closing : Array Sbpf.Account := Array.emptyWithCapacity 8
    -- the footer says when the block was produced: the clock takes the second, and an account keeps the nanoseconds
    let clockNow ← world.get Sbpf.clockSysvar
    closing := closing.push { clockNow with data := clockData slot (if turning then block.producedAt / 1000000000 else Wire.u64 clockNow.data 8) epoch (epoch + 1) (block.producedAt / 1000000000) }
    closing := closing.push ⟨nanosecondClock, Sbpf.systemProgram, 946560, u64 block.producedAt, false⟩
    -- the footer's certificates: who voted on the slot eight back (they are credited, and the leader with
    -- them), and who made the previous block final (their roots advance)
    let certs := Alpenglow.parse block.certificates
    if certs.error != "" then
      fail s!"slot {slot}: {certs.error}"
    if certs.rewardSlot != 0 && certs.rewardSlot + 8 != slot then
      fail s!"slot {slot}: its footer rewards slot {certs.rewardSlot}, which is not eight slots back"
    let mut voteKeys : Array ByteArray := Array.emptyWithCapacity 1024
    let mut voteStates : Array Alpenglow.VoteState := Array.emptyWithCapacity 1024
    let mut voteAccounts : Array Sbpf.Account := Array.emptyWithCapacity 1024
    let mut leaderReward : UInt64 := 0
    let mut leaderCredited := "nobody"
    let genesis ← world.get genesisCertificate
    let migrationEpoch := if genesis.data.size >= 8 && manifest.slotsPerEpoch != 0 then Wire.u64 genesis.data 0 / manifest.slotsPerEpoch else 0xFFFFFFFFFFFFFFFE
    for pass in [0:2] do
      let about := if pass == 0 then certs.rewardSlot else certs.finalSlot
      if about != 0 then
        let stakes := stakesOf manifest (if manifest.slotsPerEpoch == 0 then 0 else about / manifest.slotsPerEpoch)
        -- (the validators in order: the same for every block of an epoch)
        if stakes.epoch != rankedEpoch || rankedOrder.size == 0 then
          rankedOrder := Alpenglow.ranks stakes.voters
          rankedEpoch := stakes.epoch
        let ranked := rankedOrder
        -- when the slot in question ended, counted back from when this block was produced (slots are 200 ms)
        let nanos := block.producedAt - 200000000 * (slot - about)
        let inflation ← world.get voteRewardAccount
        let mut possible : UInt64 := 0
        let mut perEpoch : UInt64 := 0
        if Wire.u64 inflation.data 16 == epoch then
          possible := Wire.u64 inflation.data 0
          perEpoch := Wire.u64 inflation.data 8
        else if inflation.data.size >= 49 && inflation.data[24]! == 1 && Wire.u64 inflation.data 41 == epoch then
          possible := Wire.u64 inflation.data 25
          perEpoch := Wire.u64 inflation.data 33
        for rank in [0:ranked.size] do
          if Alpenglow.namedByAny (if pass == 0 then certs.rewardBits else certs.finalBits) rank then
            let v := ranked[rank]!
            let mut at_ := keyIndex voteKeys v.vote
            if at_ == Sbpf.notFound then
              let account ← world.get v.vote
              let parsed := Alpenglow.VoteState.parse account.data
              if account.owner == Bank.voteProgram && parsed.ok then
                at_ := voteKeys.size
                voteKeys := voteKeys.push v.vote
                voteStates := voteStates.push parsed
                voteAccounts := voteAccounts.push account
            if at_ != Sbpf.notFound then
              let mut st := voteStates[at_]!
              if pass == 0 then
                st := st.voted about nanos
                let reward := Alpenglow.ratio possible v.stake perEpoch stakes.total
                leaderReward := Alpenglow.saturating leaderReward (reward - reward / 2)
                if reward / 2 != 0 then
                  st := st.credit migrationEpoch epoch (reward / 2)
              else
                st := (st.rooted about).voted about nanos
              voteStates := voteStates.set! at_ st
    -- the leader is credited the other half of every reward
    if certs.rewardSlot != 0 && leaderReward != 0 then
      let leaderVote := LeaderSchedule.leaderAt leaderVotes slot
      let mut at_ := keyIndex voteKeys leaderVote
      if at_ == Sbpf.notFound && leaderVote.size == 32 then
        let account ← world.get leaderVote
        let parsed := Alpenglow.VoteState.parse account.data
        if account.owner == Bank.voteProgram && parsed.ok then
          at_ := voteKeys.size
          voteKeys := voteKeys.push leaderVote
          voteStates := voteStates.push parsed
          voteAccounts := voteAccounts.push account
      if at_ != Sbpf.notFound then
        voteStates := voteStates.set! at_ (voteStates[at_]!.credit migrationEpoch epoch leaderReward)
        leaderCredited := Base58.encode leaderVote
    for k in [0:voteKeys.size] do
      let data := voteStates[k]!.bytes
      if data.size != 0 then
        closing := closing.push { voteAccounts[k]! with data := data }
    -- the block's hash joins the recent blockhashes
    let oldRecent ← world.get recentBlockhashesSysvar
    closing := closing.push { oldRecent with data := recentBlockhashesWith oldRecent.data block.blockhash 5000 }
    -- the fees: half of what was paid per signature is burned, the rest goes to whoever collects for the leader
    let burned := signatureFees * 50 / 100
    let deposit := (fees - signatureFees) + (signatureFees - burned)
    let leader := LeaderSchedule.leaderAt leaderCollectors slot
    -- (what is burned, and what cannot be delivered, leaves the supply)
    supply := supply - burned - deposit
    if deposit != 0 && leader.size == 32 then
      -- (the footer may just have rewritten this very account: a leader's vote account can collect its fees)
      let mut collector ← world.get leader
      let mut rewritten := Sbpf.notFound
      for k in [0:closing.size] do
        if closing[k]!.key == leader then
          collector := closing[k]!
          rewritten := k
      -- the collector is the leader's vote account (no questions asked), or a system account that this
      -- leaves exempt from rent; anything else, and the fees are burned
      let isVote := leader == LeaderSchedule.leaderAt leaderVotes slot
      let after := collector.lamports + deposit
      let rentOk := after >= machine.rentMinimum collector.data.size
        || (collector.lamports != 0 && collector.lamports < machine.rentMinimum collector.data.size)
      if isVote || (collector.owner == Sbpf.systemProgram && !(Bank.reserved leader) && (leader == incinerator || rentOk)) then
        if rewritten != Sbpf.notFound then
          closing := closing.set! rewritten { collector with lamports := after }
        else
          closing := closing.push { collector with lamports := after }
        supply := supply + deposit
        if lines then
          IO.println s!"reward {Base58.encode leader} {deposit} {after}"
    -- this slot had a block
    let oldHistory ← world.get slotHistorySysvar
    closing := closing.push { oldHistory with data := slotHistoryWith oldHistory.data slot }
    -- what was sent to the incinerator in this slot is gone
    let ashes ← world.get incinerator
    for was in touched do
      if was.key == incinerator && ashes.lamports != 0 then
        closing := closing.push (absent incinerator)
        supply := supply - ashes.lamports
    for a in closing do
      let was ← world.get a.key
      if Sbpf.accountAt touchedSlots touched a.key == Sbpf.notFound then
        touchedSlots := Sbpf.accountLink touchedSlots touched a.key touched.size
        touched := touched.push was
        touchedHashes := touchedHashes.push (world.hashOf a.key)
      world := world.keep a true
    latest := block.blockhash
    recent := recent ++ latest
    if recent.size > 32 * 151 then
      recent := recent.extract (recent.size - 32 * 151) recent.size
    let usFooter := (← Sys.nowUs) - mark
    mark ← Sys.nowUs
    -- ---- the lattice hash moves by exactly what changed
    -- (the accounts as they are now are hashed together: sixteen chunks at a time, whoever's they are)
    let mut nows : Array Sbpf.Account := Array.emptyWithCapacity touched.size
    let mut inputs : Array ByteArray := Array.emptyWithCapacity touched.size
    for was in touched do
      let now ← world.get was.key
      nows := nows.push now
      if now.lamports != 0 then
        inputs := inputs.push (LtHash.accountInput now.lamports now.data now.executable now.owner now.key)
    let roots := Blake3.rootNodes inputs Fast.quick
    let mut hashed := 0
    let mut sumFile := LtHash.toFile sum
    for k in [0:touched.size] do
      let was := touched[k]!
      let now := nows[k]!
      let before := if touchedHashes[k]!.size == 2048 then touchedHashes[k]!
        else LtHash.contribution was.lamports was.data was.executable was.owner was.key
      let mut after := ByteArray.empty
      if now.lamports != 0 then
        after := roots[hashed]!.bytesBy 2048 Fast.quick
        hashed := hashed + 1
      sumFile := LtHash.addToFile (LtHash.addToFile sumFile before true Fast.quick) after false Fast.quick
      world := world.noteHash now.key after
    sum := LtHash.ofFile sumFile
    if lines then
      for was in touched do
        let now ← world.get was.key
        IO.println s!"changed {Base58.encode was.key} {now.lamports} {Base58.encode now.owner} {now.data.size} {Hex.encode ((Sha256.hash now.data).extract 0 8)} was {was.lamports} {was.data.size} {Hex.encode ((Sha256.hash was.data).extract 0 8)}"
    let usHash := (← Sys.nowUs) - mark
    if timing then
      IO.println s!"timing: accounts read {usLoad / 1000} ms, transactions run {usRun / 1000} ms, changes kept {usKeep / 1000} ms, footer and closing {usFooter / 1000} ms, lattice hash {usHash / 1000} ms"
    let inner := Sha256.hash (bankHash ++ u64 signatures ++ latest)
    bankHash := Sha256.hash (inner ++ LtHash.bytes sum)
    -- what the signature checkers found
    let waited ← Sys.nowUs
    let mut bad : UInt64 := 0
    for fd in hearChecker do
      let answer ← Sys.read fd 8
      bad := bad + (if answer.size == 8 then Wire.u64 answer 0 else 0xFFFFFFFF)
    signaturesBad := signaturesBad + bad
    if checkers != 0 then
      signaturesChecked := signaturesChecked + signatures
    if timing && checkers != 0 then
      IO.println s!"timing: waited {((← Sys.nowUs) - waited) / 1000} ms for the signature checks"
    let took := (← Sys.nowMs) - started
    n := n + 1
    if !live || bankHash != block.bankHash then
      IO.println s!"slot {slot}: {block.transactions.size} transactions ({failedCount} failed), {signatures} signatures, {Fmt.thousands units} compute units, {touched.size} accounts changed ({voteKeys.size} vote accounts by the footer), fees {fees} · {took} ms"
      if lines then
        IO.println s!"footer: final slot {certs.finalSlot} ({certs.finalBits.size} bitmaps), reward slot {certs.rewardSlot} ({certs.rewardBits.size} bitmaps), leader reward {leaderReward} to {leaderCredited}, migration epoch {migrationEpoch}"
      IO.println s!"  bank hash  {Base58.encode bankHash}"
      IO.println s!"  the block's {Base58.encode block.bankHash}  {if bankHash == block.bankHash then "MATCH" else "(differs)"}{if checkers == 0 then "" else if bad == 0 then " · signatures valid" else s!" · {bad} SIGNATURES DO NOT VERIFY"}"
    -- (how it is going, for the node to show: see `Export.json`)
    if live && (bankHash != block.bankHash || (← Sys.nowMs) - reported >= 5000) then
      let _ ← Sys.writeFileAtomic s!"{blocksDir}/replay.json" s!"\{\"slot\": {slot}, \"executed\": {n}, \"certificates\": {certified}, \"behind\": {if tip > slot then tip - slot else 0}, \"savedSlot\": {savedSlot}, \"at\": {← Sys.nowMs}, \"stopped\": {bankHash != block.bankHash}}".toUTF8
    if live && bankHash != block.bankHash then
      fail s!"stopped at slot {slot}, built on slot {parent}. The state saved is that of slot {savedSlot}, and the blocks since are in {blocksDir}"
    if follow && block.bankHash.size == 32 then
      bankHash := block.bankHash
    -- ---- with enough held, or after ten minutes, the changes go to the log
    let now ← Sys.nowMs
    if live && (world.full || now - savedAt > 600000) then
      let held := world.held.size
      world ← checkpoint world dir blocksDir savedSlot slot bankHash latest sum supply height recent (stakeKeys.extract manifest.stakeKeys.size stakeKeys.size)
      savedSlot := slot
      savedAt := now
      IO.println s!"state        saved at slot {slot}: {held} accounts were held, the log is {Fmt.thousands world.overlays[0]!.flushed} bytes · {(← Sys.nowMs) - now} ms"
    else if world.full then
      world ← world.save slot
    if live && now - reported >= 5000 then
      IO.println s!"slot {slot}: {n} blocks executed, every bank hash matching, {certified} certificates checked · {(now - reported) / (n - reportedAt).toUInt64} ms a block · {if tip > slot then tip - slot else 0} slots behind"
      reported := now
      reportedAt := n
  if live then
    let _ ← checkpoint world dir blocksDir savedSlot slot bankHash latest sum supply height recent (stakeKeys.extract manifest.stakeKeys.size stakeKeys.size)
    IO.println s!"state        saved at slot {slot}, bank hash {Base58.encode bankHash}"
  for fd in askChecker do
    Sys.close fd
  if checkers != 0 then
    IO.println s!"signatures   {Fmt.thousands signaturesChecked} checked in {checkers} processes, {signaturesBad} did not verify"

end RunReplay
