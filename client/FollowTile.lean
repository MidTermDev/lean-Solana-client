import Solana.LeaderSchedule
import Layout
import Directory
import Solana.Block
import RunBlock

/-!
# Following the chain

With a shred port open, shreds arrive on their own (see `TurbineTile`). This
is what turns them into verified blocks:

* each shred must be on a Merkle path to a root signed by the slot's leader;
* shreds are filed by slot and by set of 32;
* when a set is missing data shreds but 32 of its 64 shreds are here, the
  missing ones are rebuilt from the coding shreds;
* when every data shred of a slot is here, the block is checked
  (`Solana.Block`) against its parent, if the parent was seen too.
-/

namespace Follow

/-- One set of 32 data and 32 coding shreds. -/
structure Group where
  /-- the root its shreds lead to, once one has been checked against the leader's signature -/
  root : ByteArray
  code : Array ByteArray
  codeCount : Nat
  rebuilt : Bool
  deriving Inhabited

structure Slot where
  slot : UInt64
  leader : ByteArray
  data : Array ByteArray
  count : Nat
  /-- index of the last data shred, or `Wire.bad` -/
  last : Nat
  groups : Array Group
  done : Bool
  /-- no known key signed this slot's shreds: do not search again for each of them -/
  unknown : Bool
  /-- the missing shreds were asked for by repair (once) -/
  asked : Bool
  /-- some of its shreds came by repair and have not been checked one by one yet -/
  unchecked : Bool
  /-- the leader is the one the schedule names for the slot, not whoever turned out to have signed it -/
  scheduled : Bool
  deriving Inhabited

-- The shared table of verified blocks: 256 entries of 256 bytes, indexed by slot.
--   +0 slot (written last)   +8 linked (0 or 1)   +16 parent slot   +24 hash count of the first entry
--   +32 blockhash   +64 last Merkle root   +96 root named by the first set   +128 first entry's hash
--   +160 what the first entry's transactions mix in   +192 whether they mix anything in

/-- Records a verified block: what its child needs to link to it, and what it needs to link to its parent. -/
def remember (base : UInt64) (r : Block.Report) (lastRoot : ByteArray) : IO Unit := do
  let at_ := base + (r.slot % 256) * 256
  let mixin := if r.firstMixin.size == 32 then r.firstMixin else r.blockhash
  let body := r.blockhash ++ lastRoot ++ r.firstChained ++ r.firstHash ++ mixin
  Mem.store64 at_ 0
  Mem.store64 (at_ + 8) 0
  Mem.store64 (at_ + 16) r.parentSlot
  Mem.store64 (at_ + 24) r.firstCount
  Mem.copy (at_ + 32) (Unsafe.addr body + 24) 160
  Mem.store64 (at_ + 192) (if r.firstMixin.size == 32 then 1 else 0)
  Mem.store64 at_ r.slot

/-- If the block of `slot` and its parent are both in the table and the link
between them has not been checked yet, checks it. Returns 1 if it holds, 2
if the block does not follow that parent, 0 if there was nothing to do.
Safe to call from several tiles at once: only one of them counts the link. -/
def link (base slot : UInt64) : IO UInt64 := do
  let at_ := base + (slot % 256) * 256
  if slot == 0 || (← Mem.load64 at_) != slot || (← Mem.load64 (at_ + 8)) != 0 then
    return 0
  let parent ← Mem.load64 (at_ + 16)
  let from_ := base + (parent % 256) * 256
  if (← Mem.load64 from_) != parent then
    return 0
  let buf := Sys.scratch 320
  Mem.copy (Unsafe.addr buf + 24) (at_ + 32) 160
  Mem.copy (Unsafe.addr buf + 184) (from_ + 32) 64
  let both ← Sys.setSize buf 224
  let count ← Mem.load64 (at_ + 24)
  let mixes ← Mem.load64 (at_ + 192)
  -- (either entry may have been replaced while it was being read)
  if (← Mem.load64 at_) != slot || (← Mem.load64 from_) != parent then
    return 0
  let mixin := if mixes == 1 then both.extract 128 160 else ByteArray.empty
  let ok := Block.follows (both.extract 160 192) (both.extract 192 224) (both.extract 64 96) count mixin (both.extract 96 128)
  if (← Mem.cas64 (at_ + 8) 0 (if ok then 1 else 2)) != 0 then
    return 0
  return if ok then 1 else 2

def emptyGroup : Group := ⟨ByteArray.empty, Array.replicate 32 ByteArray.empty, 0, false⟩

/-- A slot with nothing received yet. If the schedule covers it, its leader is known before any shred arrives,
and only that key's signature will do. -/
def newSlot (schedule : ByteArray) (slot : UInt64) : Slot :=
  let leader := LeaderSchedule.leaderAt schedule slot
  ⟨slot, leader, Array.replicate 1024 ByteArray.empty, 0, Wire.bad, Array.emptyWithCapacity 32, false, false, false, false, leader.size == 32⟩

/-- The data shreds `[32 g, 32 g + 32)` of a slot. -/
def groupData (s : Slot) (g : Nat) : Array ByteArray := Id.run do
  let mut out : Array ByteArray := Array.emptyWithCapacity 32
  for i in [32 * g:32 * g + 32] do
    out := out.push (if i < s.data.size then s.data[i]! else ByteArray.empty)
  return out

/-- Files a data shred. -/
def put (s : Slot) (index : Nat) (p : ByteArray) (flags : UInt64) : Slot := Id.run do
  if index >= Shred.maxData then
    return s
  let mut data := s.data
  while index >= data.size do
    data := data.push ByteArray.empty
  if data[index]!.size != 0 then
    return s
  let last := if flags &&& Shred.flagLastInSlot == Shred.flagLastInSlot then index else s.last
  return { s with data := data.set! index p, count := s.count + 1, last := last }

/-- Rebuilds, from coding shreds, whatever data shreds of group `g` are
missing, if enough of the set is here. Returns the slot and how many shreds
were rebuilt. -/
def rebuild (s : Slot) (g : Nat) : Slot × Nat := Id.run do
  let group := s.groups[g]!
  if group.rebuilt || group.codeCount == 0 then
    return (s, 0)
  let present := groupData s g
  let mut have_ := 0
  for d in present do
    if d.size != 0 then
      have_ := have_ + 1
  if have_ == 32 || have_ + group.codeCount < 32 then
    return (s, 0)
  let mut out := { s with groups := s.groups.set! g { group with rebuilt := true } }
  let full := Shred.recoverSet present group.code
  let mut rebuilt := 0
  if full.size == 32 then
    for i in [0:32] do
      if present[i]!.size == 0 then
        let h := Shred.parse full[i]!
        if h.ok && h.isData && h.slot == s.slot && h.index.toNat == 32 * g + i then
          out := put out (32 * g + i) full[i]! h.flags
          rebuilt := rebuilt + 1
  return (out, rebuilt)

/-- `rebuild` for every group of a slot. Returns the slot, the shreds rebuilt and the sets they were in. -/
def settle (s : Slot) : Slot × Nat × Nat := Id.run do
  let mut out := s
  let mut shreds := 0
  let mut sets := 0
  for g in [0:s.groups.size] do
    let (next, n) := rebuild out g
    out := next
    if n != 0 then
      shreds := shreds + n
      sets := sets + 1
  return (out, shreds, sets)

/-- If every data shred of the slot is here, checks the block and reports
it. The block is checked on its own at once; its link to its parent is
checked through the shared table, now if the parent has been verified
already, or when the parent is (by whichever tile verifies it). -/
def finish (m : Ipc.Metrics) (seenBase : UInt64) (spool : String) (s : Slot) (candidates : ByteArray) : IO Slot := do
  if s.done || s.last == Wire.bad || s.count != s.last + 1 then
    return s
  let mut shreds : Array ByteArray := Array.emptyWithCapacity (s.last + 1)
  for i in [0:s.last + 1] do
    shreds := shreds.push s.data[i]!
  let t0 ← Sys.nowMs
  -- shreds that arrived by turbine were checked one by one against the leader's key; a slot filled in
  -- by repair is checked whole, and its leader looked for if it was not known
  let r := if s.unchecked then Block.verifyWith shreds (if s.leader.size == 32 then s.leader else candidates) 0 ByteArray.empty ByteArray.empty false
    else Block.verifyWith shreds s.leader 0 ByteArray.empty ByteArray.empty true
  let t1 ← Sys.nowMs
  -- its shreds are no longer needed
  let closed := { s with done := true, data := Array.emptyWithCapacity 0, groups := Array.emptyWithCapacity 0 }
  if r.error != "" then
    -- A block whose signer is not among the nodes known so far (the first moments after starting,
    -- before gossip has named everyone) has not been shown to be wrong: it could not be checked.
    let reason := r.error.toUTF8
    let unknown := "any known node".toUTF8
    if s.leader.size != 32 && reason.size >= unknown.size && Wire.eqAt reason (reason.size - unknown.size) unknown 0 unknown.size then
      m.add M.blocksMissed 1
      IO.eprintln s!"leansol: slot {s.slot} could not be checked: its leader is not yet known from gossip"
    else
      m.add M.blocksBad 1
      IO.eprintln s!"leansol: slot {s.slot} failed verification: {r.error}"
    return closed
  remember seenBase r (Block.rootOf shreds[shreds.size - 1]!)
  -- (saved for the process that executes blocks, unless the disk is nearly full: it fetches what it lacks)
  if spool != "" && (← Sys.freeSpace spool) > 40000000000 then
    let unknown := Sbpf.zeros ByteArray.empty 32
    let _ ← Sys.writeFileMode s!"{spool}/{s.slot}.block" (RunBlock.pack r unknown unknown shreds) 0x1a4
  m.add M.blocksOk 1
  m.add M.blocksFollowed 1
  if s.scheduled then
    m.add M.blocksScheduled 1
  -- this block to its parent, and any child that was verified before it
  for k in [0:9] do
    let outcome ← link seenBase (s.slot + k.toUInt64)
    if outcome == 1 then
      m.add M.blocksLinked 1
    else if outcome == 2 then
      m.add M.blocksUnlinked 1
  if s.slot > (← m.get M.blockSlot) then
    m.set M.blockSlot s.slot
    m.set M.blockTxs r.transactions.toUInt64
    m.set M.blockShreds r.shreds.toUInt64
    m.set M.blockVerifyMs (t1 - t0)
    for i in [0:4] do
      m.set (M.blockLeader + i) (Wire.u64 r.leader (8 * i))
      m.set (M.blockHash + i) (Wire.u64 r.blockhash (8 * i))
  m.add M.blockTxTotal r.transactions.toUInt64
  m.add M.blockSigTotal r.signatures.toUInt64
  m.add M.blockShredTotal r.shreds.toUInt64
  m.add M.blockEntryTotal r.entries.toUInt64
  return closed

end Follow

open Follow in
/-- Receives shreds from the turbine tile and turns them into verified blocks. -/
def followTile (sh : Shared) (cfg : Config) (which : Nat) : IO Unit := do
  Sys.dieWithParent
  let m := sh.metrics
  let mut slots : Array Slot := Array.emptyWithCapacity 64
  let mut checkedWaiting : UInt64 := 0
  -- a socket of its own, to ask validators for the shreds turbine did not bring
  let sock ← Sys.udpSocket
  let _ ← Sys.bind sock 0 0
  Sys.setTimeout sock 20 20
  Sys.setRecvBuffer sock 4194304
  let mut snap ← Directory.read sh.directory
  let mut turn := which
  -- keys that led recently, newest first, then every key known from gossip
  let mut leaders := ByteArray.emptyWithCapacity (32 * 256)
  let mut known := ByteArray.empty
  let mut refreshed : UInt64 := 0
  let mut newest : UInt64 := 0
  repeat
    let now ← Sys.nowMs
    if now - refreshed > 3000 then
      refreshed := now
      snap ← Directory.read sh.directory
      known := snap.keys
    if now - checkedWaiting >= 30 then
      -- blocks that are complete and waiting for their parent to be verified
      checkedWaiting := now
      -- A slot that is still not whole well after it ended: ask for what is missing, once.
      let mut late := Wire.bad
      for i in [0:slots.size] do
        if !slots[i]!.done && !slots[i]!.asked && slots[i]!.slot + 8 <= newest then
          late := i
      -- (right after starting, gossip has named nobody to ask yet: the slot waits)
      if late != Wire.bad && snap.count != 0 then
        let s := slots[late]!
        let mut peers : Array RunBlock.Peer := Array.emptyWithCapacity 16
        let mut row := turn * 257
        turn := turn + 1
        for _ in [0:snap.count] do
          row := (row + 61) % (if snap.count == 0 then 1 else snap.count)
          let repair := snap.field row Nodes.fRepair
          if peers.size < 16 && repair != 0 && snap.field row Nodes.fShred == cfg.shredVersion then
            peers := peers.push ⟨snap.keys.extract (32 * row) (32 * row + 32), addrIp repair, addrPort repair, 0⟩
        let (got, _) ← RunBlock.fetchFrom sock cfg.seed cfg.pubkey peers s.slot 0 2500 s.data s.last
        m.add M.blockRequests got.requests.toUInt64
        let mut next := { s with asked := true }
        if got.complete then
          let mut data : Array ByteArray := Array.emptyWithCapacity (got.last + 1)
          for i in [0:got.last + 1] do
            data := data.push got.shreds[i]!
          m.add M.slotsRepaired 1
          next := { next with data := data, count := got.last + 1, last := got.last, unchecked := true, unknown := false }
          next ← finish m sh.seenBase cfg.spool next (leaders ++ known)
        slots := slots.set! late next
    match ← sh.toBlocks[which]!.recv 50 with
    | none => pure ()
    | some msg =>
      -- a shred, then the Merkle root it leads to, as computed by the tile that received it
      let p := msg.data.extract 0 (msg.data.size - 32)
      let root := msg.data.extract (msg.data.size - 32) msg.data.size
      let h := Shred.parse p
      -- far behind what has already been seen: a late or replayed shred
      if h.ok && h.version == cfg.shredVersion && h.fecSet % 32 == 0 && h.slot + 48 > newest then
        if h.slot > newest then
          newest := h.slot
          -- A new slot has begun, so the ones before it are ending: rebuild what they still miss.
          for i in [0:slots.size] do
            if !slots[i]!.done && !slots[i]!.unknown then
              let (settled, shreds, sets) := settle slots[i]!
              m.add M.shredsRecovered shreds.toUInt64
              m.add M.setsRecovered sets.toUInt64
              slots := slots.set! i (← finish m sh.seenBase cfg.spool settled (leaders ++ known))
        -- the slot's record
        let mut at_ := Wire.bad
        for i in [0:slots.size] do
          if slots[i]!.slot == h.slot then
            at_ := i
        if at_ == Wire.bad then
          if slots.size >= 48 then
            -- make room: drop the oldest
            let mut oldest := 0
            for i in [0:slots.size] do
              if slots[i]!.slot < slots[oldest]!.slot then
                oldest := i
            if !slots[oldest]!.done then
              m.add M.slotsIncomplete 1
            slots := slots.set! oldest (newSlot cfg.schedule h.slot)
            at_ := oldest
          else
            slots := slots.push (newSlot cfg.schedule h.slot)
            at_ := slots.size - 1
        let mut s := slots[at_]!
        let g := (h.fecSet / 32).toNat
        let mut repeated := false
        if g < s.groups.size then
          repeated := if h.isData then h.index.toNat < s.data.size && s.data[h.index.toNat]!.size != 0
            else h.size < 32 && s.groups[g]!.code[h.size.toNat]!.size != 0
        if repeated then
          -- relayed to us by more than one node
          m.add M.shredsDuplicate 1
        else if !s.done && !s.unknown && !s.unchecked && g < 1024 then
          let mut groups := s.groups
          while g >= groups.size do
            groups := groups.push emptyGroup
          let mut group := groups[g]!
          let mut accept := root.size == 32
          if accept && group.root.size == 0 then
            -- the first shred of this set: its root must be signed by the slot's leader
            if s.leader.size == 32 then
              accept := Ed25519.verify s.leader (p.extract 0 64) root
            else
              let candidates := leaders ++ known
              let who := Block.signer candidates 0 (p.extract 0 64) root
              accept := who != Wire.bad
              if !accept then
                s := { s with unknown := true }
              else
                let leader := candidates.extract who (who + 32)
                s := { s with leader := leader }
                let mut next := leader
                for i in [0:leaders.size / 32] do
                  if i < 255 && leaders.extract (32 * i) (32 * i + 32) != leader then
                    next := next ++ leaders.extract (32 * i) (32 * i + 32)
                leaders := next
            if accept then
              group := { group with root := root }
          else if accept then
            accept := root == group.root
          if !accept then
            m.add M.shredsRejected 1
          else
            let endKnown := s.last != Wire.bad
            if h.isData then
              s := put s h.index.toNat p h.flags
            else if h.parentOffset == 32 && h.flags == 32 && h.size < 32 then
              -- a coding shred of a 32 + 32 set, filed by its position
              group := { group with code := group.code.set! h.size.toNat p, codeCount := group.codeCount + 1 }
            s := { s with groups := groups.set! g group }
            -- Rebuild what is missing only once the slot is ending: while it is still arriving, most
            -- of what is missing is merely late.
            if h.slot < newest || endKnown then
              let (next, n) := rebuild s g
              s := next
              if n != 0 then
                m.add M.shredsRecovered n.toUInt64
                m.add M.setsRecovered 1
            else if s.last != Wire.bad then
              -- the slot's end has just become known: every set gets its chance
              let (next, shreds, sets) := settle s
              s := next
              m.add M.shredsRecovered shreds.toUInt64
              m.add M.setsRecovered sets.toUInt64
            s ← finish m sh.seenBase cfg.spool s (leaders ++ known)
        slots := slots.set! at_ s
