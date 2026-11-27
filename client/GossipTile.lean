import Layout
import Net.Ip
import Solana.Gossip
import Solana.Table
import Directory

/-!
# gossip

The protocol state machine. It owns the node's identity key and the CRDS
store, answers pings, and every 200 ms asks a handful of peers for the
records it does not have yet.

Its input is already authenticated: the verify tiles only forward records
whose signature checked out.
-/

/-- Records remembered before the store is flushed and refilled. -/
def storeCap : Nat := 400000

/-- Everything the node has learned. A plain immutable value: `ingest`
takes the old state and returns the new one, updating in place because the
tile holds the only reference. -/
structure State where
  /-- 64-bit prefixes of the hashes of every record held, for duplicate checks. -/
  seen : Set64
  /-- The same prefixes in arrival order (bloom partitioning scans these). -/
  prefixes : Array UInt64
  /-- Full 32-byte record hashes, back to back (bloom filters hash these). -/
  hashes : ByteArray
  nodes : Nodes
  /-- Records accepted, per CRDS type. -/
  kinds : Array UInt64
  fresh : UInt64
  dups : UInt64

namespace State

def create (cap : Nat) : State :=
  ⟨Set64.create (1 <<< 20), Array.emptyWithCapacity cap, ByteArray.emptyWithCapacity (cap * 32),
    Nodes.create 32768, Array.replicate 16 0, 0, 0⟩

/-- Row of the node that owns the record, adding it if there is room. -/
def rowFor (nodes : Nodes) (v : ByteArray) (origin : Nat) : Nodes × Nat :=
  let row := nodes.find v origin
  if row != Nodes.notFound then (nodes, row)
  else if nodes.count < nodes.capacity then
    let count := nodes.count
    (nodes.append v origin, count)
  else (nodes, Nodes.notFound)

/-- Folds one verified record (`signature ++ data`) into the state. -/
def ingest (st : State) (v : ByteArray) : State := Id.run do
  let h := Sha256.hash v
  let pre := Wire.u64 h 0
  let key := if pre == 0 then 1 else pre
  if st.seen.contains key then
    return { st with dups := st.dups + 1 }
  let ⟨seen, prefixes, hashes, nodes, kinds, fresh, dups⟩ := st
  let mut seen := seen
  let mut prefixes := prefixes
  let mut hashes := hashes
  if prefixes.size >= storeCap then
    seen := Set64.create (1 <<< 20)
    prefixes := Array.emptyWithCapacity storeCap
    hashes := ByteArray.emptyWithCapacity (storeCap * 32)
  seen := seen.insert key
  prefixes := prefixes.push pre
  hashes := hashes ++ h
  let info := Crds.scan v 64
  let mut nodes := nodes
  let mut kinds := kinds
  if info.kind < 14 then
    kinds := kinds.set! info.kind (kinds[info.kind]! + 1)
  if info.kind == Crds.kindContactInfo then
    let c := Crds.parseContact v info.body
    if Wire.ok c.stop then
      let (ns, row) := rowFor nodes v info.origin
      nodes := ns
      if row != Nodes.notFound && c.wallclock >= nodes.get row Nodes.fWallclock then
        nodes := nodes.set row Nodes.fWallclock c.wallclock
        nodes := nodes.set row Nodes.fVersion ((c.major <<< 32) ||| (c.minor <<< 16) ||| c.patch)
        -- stored plus one so that zero means "no contact info yet"
        nodes := nodes.set row Nodes.fClient (c.client + 1)
        nodes := nodes.set row Nodes.fAddr ((c.gossipIp.toUInt64 <<< 16) ||| c.gossipPort.toUInt64)
        nodes := nodes.set row Nodes.fShred c.shredVersion
        nodes := nodes.set row Nodes.fRepair c.repair
        nodes := nodes.set row Nodes.fTvu c.tvu
  else if info.kind == Crds.kindSnapshotHashes then
    let slot := Crds.snapshotSlot v info.body
    let (ns, row) := rowFor nodes v info.origin
    nodes := ns
    if row != Nodes.notFound && slot > nodes.get row Nodes.fSnapshot && slot < 0x10000000000 then
      nodes := nodes.set row Nodes.fSnapshot slot
  return ⟨seen, prefixes, hashes, nodes, kinds, fresh + 1, dups⟩

end State

def xorshift (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

/-- How many top bits of a record hash select a bloom partition. Agave
rejects pull requests with fewer than 6; beyond that, enough that each
partition holds at most about a thousand records. -/
def maskBitsFor (count : Nat) : UInt64 := Id.run do
  let mut bits : UInt64 := 6
  while bits < 20 && ((1024 : UInt64) <<< bits) < count.toUInt64 do
    bits := bits + 1
  return bits

/-- Sends one round of pull requests: to every entrypoint and to a few
random peers, each for a random partition of the hash space. -/
def pullRound (sh : Shared) (cfg : Config) (st : State) (rng : UInt64) : IO UInt64 := do
  let wall ← Sys.nowMs
  let contact := Gossip.signValue cfg.seed cfg.pubkey
    (Gossip.contactInfo cfg.pubkey wall cfg.outsetUs cfg.shredVersion cfg.publicIp cfg.port cfg.tvuPort)
  let maskBits := maskBitsFor st.prefixes.size
  sh.metrics.set M.maskBits maskBits
  let mut r := rng
  let mut targets := cfg.entrypoints
  let n := st.nodes.count
  if n > 0 then
    for _ in [0:cfg.fanout] do
      r := xorshift r
      let row := (r % n.toUInt64).toNat
      let addr := st.nodes.get row Nodes.fAddr
      if addr != 0 && Ip.isPublic (addrIp addr) && addrPort addr != 0 &&
          st.nodes.get row Nodes.fShred == cfg.shredVersion then
        targets := targets.push addr
  for t in targets do
    r := xorshift r
    let part := r >>> (64 - maskBits)
    r := xorshift r
    let k0 := r
    r := xorshift r
    let k1 := r
    r := xorshift r
    let keys : Array UInt64 := #[k0, k1, r]
    -- the filter lists what we already hold in this partition
    let mut bits := Gossip.zeroBloom
    for i in [0:st.prefixes.size] do
      if st.prefixes[i]! >>> (64 - maskBits) == part then
        bits := Gossip.bloomAdd bits keys st.hashes (i * 32)
    let _ ← sh.toNet.push t (Gossip.pullRequest keys bits part maskBits contact)
    sh.metrics.add M.pullsTx 1
    -- Also tell each of them who we are. A node is only known to the cluster if it pushes its own
    -- contact info: validators do not learn it from pull requests, and before believing a pushed one
    -- they ping the gossip address it names.
    let _ ← sh.toNet.push t (Gossip.pushMessage cfg.pubkey contact)
  return r

/-- Writes the cluster summary into the shared metrics page and the node
table into the shared directory. -/
def publish (st : State) (sh : Shared) : IO Unit := do
  let m := sh.metrics
  let nodes := st.nodes
  Directory.write sh.directory nodes
  let mut clients : Array UInt64 := Array.replicate 16 0
  let mut vkeys : Array UInt64 := Array.emptyWithCapacity 64
  let mut vcounts : Array UInt64 := Array.emptyWithCapacity 64
  -- the three newest snapshot slots, each vouched for by a different node
  let mut t0 : UInt64 := 0
  let mut t1 : UInt64 := 0
  let mut t2 : UInt64 := 0
  let mut known : UInt64 := 0
  let mut reporters : UInt64 := 0
  for row in [0:nodes.count] do
    let client := nodes.get row Nodes.fClient
    if client != 0 then
      known := known + 1
      let bucket := if client - 1 < 14 then (client - 1).toNat else 14
      clients := clients.set! bucket (clients[bucket]! + 1)
      let ver := nodes.get row Nodes.fVersion
      let mut found := false
      for j in [0:vkeys.size] do
        if vkeys[j]! == ver then
          vcounts := vcounts.set! j (vcounts[j]! + 1)
          found := true
          break
      if !found then
        vkeys := vkeys.push ver
        vcounts := vcounts.push 1
    let snap := nodes.get row Nodes.fSnapshot
    if snap != 0 then
      reporters := reporters + 1
    if snap > t0 then
      t2 := t1
      t1 := t0
      t0 := snap
    else if snap > t1 then
      t2 := t1
      t1 := snap
    else if snap > t2 then
      t2 := snap
  m.set M.nodes known
  -- report a tip only once three nodes agree it is at least this high
  m.set M.tipSlot t2
  m.set M.tipReporters reporters
  m.set M.stored st.prefixes.size.toUInt64
  m.set M.valuesNew st.fresh
  m.set M.valuesDup st.dups
  for k in [0:14] do
    m.set (M.kinds + k) st.kinds[k]!
  for c in [0:16] do
    m.set (M.clients + c) clients[c]!
  for i in [0:8] do
    let mut best := 0
    let mut bestCount : UInt64 := 0
    for j in [0:vkeys.size] do
      if vcounts[j]! > bestCount then
        best := j
        bestCount := vcounts[j]!
    if bestCount == 0 then
      m.set (M.versions + 2 * i) 0
      m.set (M.versions + 2 * i + 1) 0
    else
      m.set (M.versions + 2 * i) vkeys[best]!
      m.set (M.versions + 2 * i + 1) bestCount
      vcounts := vcounts.set! best 0

def gossipTile (sh : Shared) (cfg : Config) : IO Unit := do
  let mut st := State.create storeCap
  let rnd ← IO.getRandomBytes 8
  let mut rng := Wire.u64 rnd 0 ||| 1
  let mut lastPull := 0
  let mut lastStats := 0
  let n := sh.toGossip.size
  repeat
    let mut busy := false
    for i in [0:n] do
      let ring := sh.toGossip[i]!
      for _ in [0:512] do
        match (← ring.pop) with
        | none => break
        | some msg =>
          busy := true
          if tagKind msg.tag == kindValue then
            st := st.ingest msg.data
          else if tagKind msg.tag == kindPing then
            -- prove we own this address: sign the hash of the token
            let _ ← sh.toNet.push (tagAddr msg.tag) (Gossip.pong cfg.seed cfg.pubkey msg.data)
            sh.metrics.add M.pongsTx 1
    let now ← IO.monoMsNow
    if now - lastPull >= 200 then
      lastPull := now
      rng ← pullRound sh cfg st rng
    if now - lastStats >= 500 then
      lastStats := now
      publish st sh
    if !busy then
      -- nothing queued: sleep on the futex until a verify tile publishes
      let seq ← sh.gossipWaiter.prepare
      let mut idle := true
      for i in [0:n] do
        if !(← sh.toGossip[i]!.isEmpty) then
          idle := false
      if idle then
        sh.gossipWaiter.commit seq 50
      else
        sh.gossipWaiter.cancel
