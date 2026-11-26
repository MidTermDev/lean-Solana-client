import Layout
import Crypto.Ed25519
import Solana.Crds

/-!
# verify

The only tiles that run Ed25519. Each takes raw datagrams from `net-rx`,
splits gossip messages into individual records, checks every signature, and
forwards only what verified. Nothing unsigned or malformed reaches the
gossip tile, so that tile can treat its input as authenticated.
-/

/-- Hands a message to the gossip tile, waiting briefly if its ring is full. -/
def forward (ring : Ipc.Ring) (tag : UInt64) (data : ByteArray) : IO Unit := do
  for _ in [0:200] do
    if (← ring.push tag data) then
      return
    IO.sleep 1

def verifyPacket (sh : Shared) (tile : Nat) (msg : Ipc.Msg) : IO Unit := do
  let b := msg.data
  let m := sh.metrics
  let out := sh.toGossip[tile]!
  let kind := Wire.u32 b 0
  if kind == 4 then
    -- Ping { from, token, signature over the token }
    m.add M.pingsRx 1
    if b.size == 132 && Ed25519.verify (b.extract 4 36) (b.extract 68 132) (b.extract 36 68) then
      forward out ((kindPing <<< 48) ||| msg.tag) (b.extract 36 68)
    else
      m.add M.sigBad 1
  else if kind == 1 || kind == 2 then
    -- PullResponse / PushMessage: sender key, then a vector of CrdsValues
    m.add (if kind == 1 then M.pullRespRx else M.pushRx) 1
    let count := Wire.u64 b 36
    if count > 64 then
      m.add M.malformed 1
      return
    let mut o := 44
    for _ in [0:count.toNat] do
      let info := Crds.scan b (o + 64)
      if !(Wire.ok info.stop) then
        m.add M.malformed 1
        break
      let t0 ← IO.monoNanosNow
      let good := Ed25519.verify (b.extract info.origin (info.origin + 32)) (b.extract o (o + 64))
        (b.extract (o + 64) info.stop)
      let t1 ← IO.monoNanosNow
      m.add (M.tileBusyUs + tile) ((t1 - t0) / 1000).toUInt64
      m.add (M.tileSigs + tile) 1
      if good then
        m.add M.sigOk 1
        forward out ((kindValue <<< 48) ||| msg.tag) (b.extract o info.stop)
      else
        m.add M.sigBad 1
      o := info.stop
  else if kind == 0 then
    -- someone pulling from us; this client only listens
    m.add M.pullReqRx 1
  else
    m.add M.otherRx 1

def verifyTile (sh : Shared) (tile : Nat) : IO Unit := do
  let ring := sh.toVerify[tile]!
  repeat
    match (← ring.recv 500) with
    | none => pure ()
    | some msg => verifyPacket sh tile msg
