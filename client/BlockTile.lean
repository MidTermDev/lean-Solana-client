import Layout
import Directory
import RunBlock

/-!
# The block tile

Every few seconds: pick a recent slot, ask a couple of dozen validators for
its shreds with the repair protocol, and check the block (`Solana.Block`):
Merkle paths, the leader's signature, the link to the parent block, the
proof of history, every transaction signature. The results go to the shared
metrics page.

It has its own UDP socket and only ever receives answers to what it asked,
so it works behind a firewall that lets nothing else in. That is also why it
samples blocks rather than following all of them: repair is a favour
validators do for nodes that missed something, not a feed.
-/

/-- Stores a 32-byte value in four metric words. -/
def setKey (m : Ipc.Metrics) (at_ : Nat) (key : ByteArray) : IO Unit := do
  for i in [0:4] do
    m.set (at_ + i) (Wire.u64 key (8 * i))

def blockTile (sh : Shared) (cfg : Config) : IO Unit := do
  Sys.dieWithParent
  let m := sh.metrics
  let sock ← Sys.udpSocket
  let _ ← Sys.bind sock 0 0
  Sys.setTimeout sock 20 20
  Sys.setRecvBuffer sock 8388608
  -- keys that led recently, newest first: the next leader is usually one of them
  let mut leaders := ByteArray.emptyWithCapacity (32 * 64)
  let mut lastSlot : UInt64 := 0
  let mut turn := 0
  repeat
    IO.sleep (cfg.blockInterval * 1000).toUInt32
    let tip ← m.get M.tipSlot
    let snap ← Directory.read sh.directory
    -- validators that serve repair on our cluster
    let mut known : Array RunBlock.Peer := Array.emptyWithCapacity 4096
    for row in [0:snap.count] do
      let repair := snap.field row Nodes.fRepair
      if repair != 0 && snap.field row Nodes.fShred == cfg.shredVersion then
        known := known.push ⟨snap.keys.extract (32 * row) (32 * row + 32), addrIp repair, addrPort repair, 0⟩
    if tip > 64 && known.size >= 8 then
      -- a slot old enough that validators have all of it, and not one already done
      let slot := if tip - 24 > lastSlot then tip - 24 else lastSlot + 1
      lastSlot := slot
      let mut peers : Array RunBlock.Peer := Array.emptyWithCapacity 24
      let stride := if known.size > 24 then known.size / 24 else 1
      turn := turn + 1
      for k in [0:24] do
        if turn % stride + k * stride < known.size then
          peers := peers.push known[turn % stride + k * stride]!
      let t0 ← Sys.nowMs
      let (got, asked) ← RunBlock.fetch sock cfg.seed cfg.pubkey peers slot 0 6000
      m.add M.blockRequests got.requests.toUInt64
      if !got.complete then
        m.add M.blocksMissed 1
      else
        let shreds := RunBlock.slice got.shreds 0 (got.last + 1)
        -- the end of the parent block: its blockhash and its last Merkle root tie this block to it
        let parent := slot - (Shred.parse shreds[0]!).parentOffset
        let (tail, _) ← RunBlock.fetch sock cfg.seed cfg.pubkey asked parent 64 3000
        m.add M.blockRequests tail.requests.toUInt64
        let (previous, previousRoot) := RunBlock.ending tail
        let t1 ← Sys.nowMs
        let r := Block.verify shreds (leaders ++ snap.keys) 0 previous previousRoot
        let t2 ← Sys.nowMs
        if r.error != "" then
          m.add M.blocksBad 1
        else
          m.add M.blocksOk 1
          m.set M.blockSlot slot
          m.set M.blockTxs r.transactions.toUInt64
          m.set M.blockShreds r.shreds.toUInt64
          m.set M.blockVerifyMs (t2 - t1)
          m.set M.blockFetchMs (t1 - t0)
          m.add M.blockTxTotal r.transactions.toUInt64
          m.add M.blockSigTotal r.signatures.toUInt64
          m.add M.blockShredTotal r.shreds.toUInt64
          m.add M.blockEntryTotal r.entries.toUInt64
          setKey m M.blockLeader r.leader
          setKey m M.blockHash r.blockhash
          -- remember the leader, most recent first, without repeats
          let mut next := r.leader
          for i in [0:leaders.size / 32] do
            if i < 63 && leaders.extract (32 * i) (32 * i + 32) != r.leader then
              next := next ++ leaders.extract (32 * i) (32 * i + 32)
          leaders := next
