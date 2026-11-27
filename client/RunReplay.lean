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
  "usage: leansol replay --state DIR --blocks DIR [--from SLOT] [--count N] [options]\n" ++
  "\n" ++
  "  --state DIR    the store loaded by `leansol snapshot`\n" ++
  "  --blocks DIR   blocks saved by `leansol block SLOT --save DIR/SLOT.block`\n" ++
  "  --from SLOT    the first block to execute (default: the one after the snapshot's)\n" ++
  "  --count N      how many blocks (default 1)\n" ++
  "  --lines        print one line per transaction: its outcome, fee, compute units and balances\n" ++
  "  --follow       after a block whose hash differs, continue from the block's own hash\n" ++
  "  --timing       say where each block's time went\n" ++
  "  --trace N      print the log of transaction N of the first block\n"

def fail (message : String) : IO Unit := do
  IO.eprintln s!"leansol replay: {message}"
  Sys.exit 1

/-- The store a snapshot left, and what has been written since. -/
structure World where
  shards : Array Accounts.Shard
  overlay : Accounts.Shard
  /-- Accounts read or written lately, as they are now, found by address (`Sbpf.accountAt`): most of what a
  block touches was touched by the block before it. -/
  slots : Array UInt64
  held : Array Sbpf.Account
  heldBytes : Nat
  /-- For each account held: what it adds to the lattice hash as it is now, where that has been worked
  out (empty where it has not, or the account has changed since). -/
  hashes : Array ByteArray

def absent (key : ByteArray) : Sbpf.Account := ⟨key, Sbpf.systemProgram, 0, ByteArray.empty, false⟩

def ofRecord (r : ByteArray) : Sbpf.Account :=
  if r.size < Accounts.headerSize || Accounts.recLamports r == 0 then absent (r.extract 0 32)
  else ⟨r.extract 0 32, r.extract 32 64, Accounts.recLamports r, Accounts.recData r, Accounts.recExecutable r⟩

/-- The account at `key` as of now: what a replayed block left there, or else what the snapshot holds. `pending` is the unwritten end of the overlay's log. -/
def World.get (w : World) (pending : ByteArray) (key : ByteArray) : IO Sbpf.Account := do
  let at_ := Sbpf.accountAt w.slots w.held key
  if at_ != Sbpf.notFound then
    return w.held[at_]!
  let (_, loc) ← w.overlay.locate pending key 0
  if loc != Accounts.none_ then
    return ofRecord (← w.overlay.recordAt pending loc)
  let shard := w.shards[Accounts.shardOf key 0 w.shards.size]!
  let (_, found) ← shard.locate ByteArray.empty key 0
  if found == Accounts.none_ then
    return absent key
  return ofRecord (← shard.recordAt ByteArray.empty found)

def heldSlots : Nat := 524288

/-- Remembers an account as it is now. When too much is held, everything is forgotten and it starts over. -/
def World.keep (w : World) (a : Sbpf.Account) : World :=
  let ⟨shards, overlay, slots, held, bytes, hashes⟩ := w
  if held.size >= 150000 || bytes > 3000000000 then
    let empty : Array Sbpf.Account := Array.emptyWithCapacity 1024
    let fresh := empty.push a
    let none : Array ByteArray := Array.emptyWithCapacity 1024
    ⟨shards, overlay, Sbpf.accountLink (Array.replicate heldSlots 0) fresh a.key 0, fresh, a.data.size, none.push ByteArray.empty⟩
  else
    let at_ := Sbpf.accountAt slots held a.key
    if at_ != Sbpf.notFound then ⟨shards, overlay, slots, held.set! at_ a, bytes + a.data.size, hashes.set! at_ ByteArray.empty⟩
    else ⟨shards, overlay, Sbpf.accountLink slots held a.key held.size, held.push a, bytes + a.data.size, hashes.push ByteArray.empty⟩

/-- What the account at `key` adds to the lattice hash, if that is known for its present state (else empty). -/
def World.hashOf (w : World) (key : ByteArray) : ByteArray :=
  let at_ := Sbpf.accountAt w.slots w.held key
  if at_ != Sbpf.notFound then w.hashes[at_]! else ByteArray.empty

/-- Notes what the account at `key`, as it is now, adds to the lattice hash. -/
def World.noteHash (w : World) (key : ByteArray) (c : ByteArray) : World :=
  let at_ := Sbpf.accountAt w.slots w.held key
  if at_ == Sbpf.notFound then w
  else
    let ⟨shards, overlay, slots, held, bytes, hashes⟩ := w
    ⟨shards, overlay, slots, held, bytes, hashes.set! at_ c⟩

/-- `get`, remembering what was read. -/
def World.fetch (w : World) (pending : ByteArray) (key : ByteArray) : IO (World × Sbpf.Account) := do
  let at_ := Sbpf.accountAt w.slots w.held key
  if at_ != Sbpf.notFound then
    let a := w.held[at_]!
    return (w, a)
  let a ← w.get pending key
  return (w.keep a, a)

/-- Files a new version of an account in the overlay. Returns the world and the record, which the caller appends to `pending`. -/
def World.put (w : World) (pending : ByteArray) (a : Sbpf.Account) (slot : UInt64) : IO (World × ByteArray) := do
  let r := Accounts.record (a.key ++ a.owner ++ a.data) 0 32 a.lamports Accounts.noRent slot a.executable 64 a.data.size
  let (entry, loc) ← w.overlay.locate pending a.key 0
  let overlay ← w.overlay.point entry (loc == Accounts.none_) (Accounts.Shard.keyOf r 0) (w.overlay.flushed + pending.size.toUInt64)
  let filed : World := { w with overlay := overlay }
  return (filed.keep a, r)

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

def main : IO Unit := do
  let argc ← Sys.argc
  let mut stateDir := ""
  let mut blocksDir := ""
  let mut first : UInt64 := 0
  let mut count := 1
  let mut lines := false
  -- for looking into a block that does not match: carry on from the block's own bank hash, so that what
  -- later blocks read of it (the slot hashes) is right and their transactions can still be compared
  let mut follow := false
  -- say where each block's time went
  let mut timing := false
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
      else if a == "--from" then
        first := RunBlock.number v
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
  let manifest := Snapshot.parse (← Sys.readAt mfd 0 (← Sys.fileSize mfd).toNat)
  Sys.close mfd
  if manifest.error != "" then
    fail s!"{stateDir}/manifest.bin: {manifest.error}"
  Sys.mkdir s!"{stateDir}/replay"
  let overlay ← Accounts.Shard.create s!"{stateDir}/replay" 0 seed
  if overlay.failed then
    fail s!"cannot create the overlay in {stateDir}/replay"
  let mut world : World := ⟨shards, overlay, Array.replicate heldSlots 0, Array.emptyWithCapacity 1024, 0, Array.emptyWithCapacity 1024⟩
  let mut pending := ByteArray.emptyWithCapacity 4300000
  -- ---- what the bank carries from block to block
  let mut slot := manifest.slot
  let mut bankHash := manifest.hash
  let mut sum := LtHash.ofBytes manifest.ltHash
  let mut latest := manifest.blockhash
  -- recent blockhashes, newest last, with their positions: a transaction must name one of the last 150
  let mut recent := ByteArray.emptyWithCapacity (40 * 512)
  for k in [0:manifest.queue.size / 56] do
    if manifest.lastHashIndex - Wire.u64 manifest.queue (56 * k + 40) <= 150 then
      recent := recent ++ manifest.queue.extract (56 * k) (56 * k + 32)
  let mut machine := Sbpf.Machine.create ⟨0, 0, 0, 0, 0⟩ 200000
  let leaderVotes := LeaderSchedule.table manifest 1
  let leaderCollectors := LeaderSchedule.table manifest 2
  if first == 0 then
    first := slot + 1
  if first != slot + 1 then
    fail s!"the state is that of slot {slot}: the next block to execute is {slot + 1}"
  IO.println s!"state        slot {slot}, bank hash {Base58.encode bankHash}"
  let mut rankedOrder : Array Snapshot.Voter := Array.emptyWithCapacity 0
  let mut rankedEpoch : UInt64 := 0
  for n in [0:count] do
    let parent := slot
    slot := parent + 1
    let file ← Sys.readFile s!"{blocksDir}/{slot}.block" 0x8000000
    if file.size < 104 + Shred.dataPayload || (file.size - 104) % Shred.dataPayload != 0 then
      fail s!"{blocksDir}/{slot}.block is not a saved block"
    let mut shreds : Array ByteArray := Array.emptyWithCapacity ((file.size - 104) / Shred.dataPayload)
    for k in [0:(file.size - 104) / Shred.dataPayload] do
      shreds := shreds.push (file.extract (104 + Shred.dataPayload * k) (104 + Shred.dataPayload * (k + 1)))
    let block := Block.contents shreds
    if block.error != "" then
      fail s!"slot {slot}: {block.error}"
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
    let oldHashes ← world.get pending Sbpf.slotHashesSysvar
    let newHashes := { oldHashes with data := slotHashesWith oldHashes.data parent bankHash }
    let oldClock ← world.get pending Sbpf.clockSysvar
    let epoch := if manifest.slotsPerEpoch == 0 then 0 else manifest.firstNormalEpoch + (slot - manifest.firstNormalSlot) / manifest.slotsPerEpoch
    let newClock := { oldClock with data := clockData slot (Wire.u64 oldClock.data 8) epoch (epoch + 1) (Wire.u64 oldClock.data 32) }
    for a in #[newHashes, newClock] do
      let was ← world.get pending a.key
      touchedSlots := Sbpf.accountLink touchedSlots touched was.key touched.size
      touched := touched.push was
      touchedHashes := touchedHashes.push (world.hashOf was.key)
      let (next, r) ← world.put pending a slot
      world := next
      pending := pending ++ r
    let rent ← world.get pending Sbpf.rentSysvar
    let schedule ← world.get pending Sbpf.epochScheduleSysvar
    let rewards ← world.get pending Sbpf.epochRewardsSysvar
    let history ← world.get pending Sbpf.stakeHistorySysvar
    let restart ← world.get pending Sbpf.lastRestartSlotSysvar
    let clock : Sbpf.Clock := ⟨slot, Wire.u64 newClock.data 8, epoch, epoch + 1, Wire.u64 newClock.data 32⟩
    let sysvars : Sbpf.Sysvars := ⟨rent.data, schedule.data, rewards.data, newHashes.data, history.data, Wire.u64 restart.data 0⟩
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
          let table ← world.get pending l.table
          if pass == 0 then
            accounts := accounts.push table
          for index in (if pass == 0 then l.writable else l.readonly) do
            let at_ := 56 + 32 * index.toNat
            if at_ + 32 <= table.data.size then
              keys := keys.push (table.data.extract at_ (at_ + 32))
      let named := accounts.size
      for key in keys do
        let (remembering, a) ← world.fetch pending key
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
        if a.owner == Sbpf.loaderId && Sbpf.loaderKind a == 2 && !(Bank.hasProgram ⟨machine, #[], latest, 5000⟩ a.key) then
          accounts := accounts.push (← world.get pending (a.data.extract 4 36))
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
          let (next, r) ← world.put pending now slot
          world := next
          pending := pending ++ r
          if pending.size >= 4194304 then
            world := { world with overlay := ← world.overlay.flush pending }
            pending := ByteArray.emptyWithCapacity 4300000
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
              let code ← world.get pending id
              if code.owner == Sbpf.loaderId && code.data.size >= 36 then
                let holder ← world.get pending (code.data.extract 4 36)
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
    let clockNow ← world.get pending Sbpf.clockSysvar
    closing := closing.push { clockNow with data := clockData slot (Wire.u64 clockNow.data 8) epoch (epoch + 1) (block.producedAt / 1000000000) }
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
    let genesis ← world.get pending genesisCertificate
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
        let inflation ← world.get pending voteRewardAccount
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
              let account ← world.get pending v.vote
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
        let account ← world.get pending leaderVote
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
    let oldRecent ← world.get pending recentBlockhashesSysvar
    closing := closing.push { oldRecent with data := recentBlockhashesWith oldRecent.data block.blockhash 5000 }
    -- the fees: half of what was paid per signature is burned, the rest goes to whoever collects for the leader
    let burned := signatureFees * 50 / 100
    let deposit := (fees - signatureFees) + (signatureFees - burned)
    let leader := LeaderSchedule.leaderAt leaderCollectors slot
    if deposit != 0 && leader.size == 32 then
      -- (the footer may just have rewritten this very account: a leader's vote account can collect its fees)
      let mut collector ← world.get pending leader
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
        if lines then
          IO.println s!"reward {Base58.encode leader} {deposit} {after}"
    -- this slot had a block
    let oldHistory ← world.get pending slotHistorySysvar
    closing := closing.push { oldHistory with data := slotHistoryWith oldHistory.data slot }
    -- what was sent to the incinerator in this slot is gone
    let ashes ← world.get pending incinerator
    for was in touched do
      if was.key == incinerator && ashes.lamports != 0 then
        closing := closing.push (absent incinerator)
    for a in closing do
      let was ← world.get pending a.key
      if Sbpf.accountAt touchedSlots touched a.key == Sbpf.notFound then
        touchedSlots := Sbpf.accountLink touchedSlots touched a.key touched.size
        touched := touched.push was
        touchedHashes := touchedHashes.push (world.hashOf a.key)
      let (next, r) ← world.put pending a slot
      world := next
      pending := pending ++ r
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
      let now ← world.get pending was.key
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
        let now ← world.get pending was.key
        IO.println s!"changed {Base58.encode was.key} {now.lamports} {Base58.encode now.owner} {now.data.size} {Hex.encode ((Sha256.hash now.data).extract 0 8)} was {was.lamports} {was.data.size} {Hex.encode ((Sha256.hash was.data).extract 0 8)}"
    let usHash := (← Sys.nowUs) - mark
    if timing then
      IO.println s!"timing: accounts read {usLoad / 1000} ms, transactions run {usRun / 1000} ms, changes kept {usKeep / 1000} ms, footer and closing {usFooter / 1000} ms, lattice hash {usHash / 1000} ms"
    let inner := Sha256.hash (bankHash ++ u64 signatures ++ latest)
    bankHash := Sha256.hash (inner ++ LtHash.bytes sum)
    let took := (← Sys.nowMs) - started
    IO.println s!"slot {slot}: {block.transactions.size} transactions ({failedCount} failed), {signatures} signatures, {Fmt.thousands units} compute units, {touched.size} accounts changed ({voteKeys.size} vote accounts by the footer), fees {fees} · {took} ms"
    if lines then
      IO.println s!"footer: final slot {certs.finalSlot} ({certs.finalBits.size} bitmaps), reward slot {certs.rewardSlot} ({certs.rewardBits.size} bitmaps), leader reward {leaderReward} to {leaderCredited}, migration epoch {migrationEpoch}"
    IO.println s!"  bank hash  {Base58.encode bankHash}"
    IO.println s!"  the block's {Base58.encode block.bankHash}  {if bankHash == block.bankHash then "MATCH" else "(differs)"}"
    if follow && block.bankHash.size == 32 then
      bankHash := block.bankHash

end RunReplay
