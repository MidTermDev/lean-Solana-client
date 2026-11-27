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
  "  --trace N      print the log of transaction N of the first block\n"

def fail (message : String) : IO Unit := do
  IO.eprintln s!"leansol replay: {message}"
  Sys.exit 1

/-- The store a snapshot left, and what has been written since. -/
structure World where
  shards : Array Accounts.Shard
  overlay : Accounts.Shard

def absent (key : ByteArray) : Sbpf.Account := ⟨key, Sbpf.systemProgram, 0, ByteArray.empty, false⟩

def ofRecord (r : ByteArray) : Sbpf.Account :=
  if r.size < Accounts.headerSize || Accounts.recLamports r == 0 then absent (r.extract 0 32)
  else ⟨r.extract 0 32, r.extract 32 64, Accounts.recLamports r, Accounts.recData r, Accounts.recExecutable r⟩

/-- The account at `key` as of now: what a replayed block left there, or else what the snapshot holds. `pending` is the unwritten end of the overlay's log. -/
def World.get (w : World) (pending : ByteArray) (key : ByteArray) : IO Sbpf.Account := do
  let (_, loc) ← w.overlay.locate pending key 0
  if loc != Accounts.none_ then
    return ofRecord (← w.overlay.recordAt pending loc)
  let shard := w.shards[Accounts.shardOf key 0 w.shards.size]!
  let (_, found) ← shard.locate ByteArray.empty key 0
  if found == Accounts.none_ then
    return absent key
  return ofRecord (← shard.recordAt ByteArray.empty found)

/-- Files a new version of an account in the overlay. Returns the world and the record, which the caller appends to `pending`. -/
def World.put (w : World) (pending : ByteArray) (a : Sbpf.Account) (slot : UInt64) : IO (World × ByteArray) := do
  let r := Accounts.record (a.key ++ a.owner ++ a.data) 0 32 a.lamports Accounts.noRent slot a.executable 64 a.data.size
  let (entry, loc) ← w.overlay.locate pending a.key 0
  let overlay ← w.overlay.point entry (loc == Accounts.none_) (Accounts.Shard.keyOf r 0) (w.overlay.flushed + pending.size.toUInt64)
  return ({ w with overlay := overlay }, r)

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

def recentBlockhashesSysvar : ByteArray := Base58.decode "SysvarRecentB1ockHashes11111111111111111111"
def slotHistorySysvar : ByteArray := Base58.decode "SysvarS1otHistory11111111111111111111111111"
def incinerator : ByteArray := Base58.decode "1nc1nerator11111111111111111111111111111111"
def alpenglowFeature : ByteArray := Base58.decode "A1pengvuM6JEcyNuTnMqepBKhwHE3N6PmUrdATGawhJS"

/-- Where the chain keeps its clock to the nanosecond: an address derived from the Alpenglow feature's. -/
def nanosecondClock : ByteArray := (Sbpf.findProgramAddress #["alpenclock".toUTF8] alpenglowFeature).1

def main : IO Unit := do
  let argc ← Sys.argc
  let mut stateDir := ""
  let mut blocksDir := ""
  let mut first : UInt64 := 0
  let mut count := 1
  let mut lines := false
  let mut trace := Sbpf.notFound
  let mut cap : UInt64 := 0
  let mut i := 2
  while i < argc do
    let a ← Sys.arg i
    if a == "--lines" then
      lines := true
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
  let mut world : World := ⟨shards, overlay⟩
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
  let leaderTable := LeaderSchedule.table manifest
  if first == 0 then
    first := slot + 1
  if first != slot + 1 then
    fail s!"the state is that of slot {slot}: the next block to execute is {slot + 1}"
  IO.println s!"state        slot {slot}, bank hash {Base58.encode bankHash}"
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
    -- every account this block changes, as it was before the block
    let mut touched : Array Sbpf.Account := Array.emptyWithCapacity 4096
    -- ---- a new bank: the parent's hash joins the recent slot hashes, and the clock moves to this slot
    let oldHashes ← world.get pending Sbpf.slotHashesSysvar
    let newHashes := { oldHashes with data := slotHashesWith oldHashes.data parent bankHash }
    let oldClock ← world.get pending Sbpf.clockSysvar
    let epoch := if manifest.slotsPerEpoch == 0 then 0 else manifest.firstNormalEpoch + (slot - manifest.firstNormalSlot) / manifest.slotsPerEpoch
    let newClock := { oldClock with data := clockData slot (Wire.u64 oldClock.data 8) epoch (epoch + 1) (Wire.u64 oldClock.data 32) }
    for a in #[newHashes, newClock] do
      let was ← world.get pending a.key
      touched := touched.push was
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
        accounts := accounts.push (← world.get pending key)
      if lines then
        IO.println s!"begin {t}"
      for k in [named:named + keys.size] do
        let a := accounts[k]!
        if a.owner == Sbpf.loaderId && Sbpf.loaderKind a == 2 && !(Bank.hasProgram ⟨machine, #[], latest, 5000⟩ a.key) then
          accounts := accounts.push (← world.get pending (a.data.extract 4 36))
      -- a transaction names a recent blockhash, or else the value in a nonce account
      let mut known := false
      for k in [0:recent.size / 32] do
        if Wire.eqAt recent (32 * k) msg.blockhash 0 32 then
          known := true
      let capped := if n == 0 && t == trace then cap else 0
      let bank : Bank.Bank := ⟨{ machine with cap := capped }, accounts, (if known then msg.blockhash else latest), 5000⟩
      let receipt := bank.process tx false
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
          let mut seen := false
          for b in touched do
            if b.key == was.key then
              seen := true
          if !seen then
            touched := touched.push was
          let (next, r) ← world.put pending now slot
          world := next
          pending := pending ++ r
          if pending.size >= 4194304 then
            world := { world with overlay := ← world.overlay.flush pending }
            pending := ByteArray.emptyWithCapacity 4300000
      if lines then
        IO.println s!"tx {t} {Base58.encode tx.signatures[0]!} err={if receipt.error == "" then "-" else receipt.error} charged={receipt.charged} fee={receipt.fee} cu={receipt.units} bal={balances}"
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
      if n == 0 && t == trace then
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
        Sys.exit 0
    -- ---- the block's end
    let mut closing : Array Sbpf.Account := Array.emptyWithCapacity 8
    -- the footer says when the block was produced: the clock takes the second, and an account keeps the nanoseconds
    let clockNow ← world.get pending Sbpf.clockSysvar
    closing := closing.push { clockNow with data := clockData slot (Wire.u64 clockNow.data 8) epoch (epoch + 1) (block.producedAt / 1000000000) }
    closing := closing.push ⟨nanosecondClock, Sbpf.systemProgram, 946560, u64 block.producedAt, false⟩
    -- (votes and their rewards, from the footer's certificates: not applied yet)
    -- the block's hash joins the recent blockhashes
    let oldRecent ← world.get pending recentBlockhashesSysvar
    closing := closing.push { oldRecent with data := recentBlockhashesWith oldRecent.data block.blockhash 5000 }
    -- the fees: half of what was paid per signature is burned, the rest goes to whoever collects for the leader
    let burned := signatureFees * 50 / 100
    let deposit := (fees - signatureFees) + (signatureFees - burned)
    let leader := LeaderSchedule.leaderAt leaderTable slot
    if deposit != 0 && leader.size == 32 then
      let collector ← world.get pending leader
      if collector.owner == Sbpf.systemProgram then
        closing := closing.push { collector with lamports := collector.lamports + deposit }
        if lines then
          IO.println s!"reward {Base58.encode leader} {deposit} {collector.lamports + deposit}"
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
      let mut seen := false
      for b in touched do
        if b.key == a.key then
          seen := true
      if !seen then
        touched := touched.push was
      let (next, r) ← world.put pending a slot
      world := next
      pending := pending ++ r
    latest := block.blockhash
    recent := recent ++ latest
    if recent.size > 32 * 151 then
      recent := recent.extract (recent.size - 32 * 151) recent.size
    -- ---- the lattice hash moves by exactly what changed
    for was in touched do
      let now ← world.get pending was.key
      sum := LtHash.mixAccount sum was.lamports was.data was.executable was.owner was.key true
      sum := LtHash.mixAccount sum now.lamports now.data now.executable now.owner now.key false
    let inner := Sha256.hash (bankHash ++ u64 signatures ++ latest)
    bankHash := Sha256.hash (inner ++ LtHash.bytes sum)
    let took := (← Sys.nowMs) - started
    IO.println s!"slot {slot}: {block.transactions.size} transactions ({failedCount} failed), {signatures} signatures, {Fmt.thousands units} compute units, {touched.size} accounts changed, fees {fees} · {took} ms"
    IO.println s!"  bank hash  {Base58.encode bankHash}"
    IO.println s!"  the block's {Base58.encode block.bankHash}  {if bankHash == block.bankHash then "MATCH" else "(differs)"}"

end RunReplay
