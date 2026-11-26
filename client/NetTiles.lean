import Layout

/-!
# net-rx and net-tx

Two tiles share the one UDP socket. `net-rx` blocks in `recvfrom` and fans
datagrams out to the verify tiles; `net-tx` sleeps on its ring's futex and
sends whatever the gossip tile queues. Neither looks inside a packet.
-/

def netRx (sh : Shared) : IO Unit := do
  let n := sh.toVerify.size
  let mut next := 0
  repeat
    let dg ← Sys.recvFrom sh.sock 1500
    if dg.data.size == 0 then
      continue
    sh.metrics.add M.rxPackets 1
    sh.metrics.add M.rxBytes dg.data.size.toUInt64
    -- a full ring drops the packet (and counts it); gossip tolerates loss
    let _ ← sh.toVerify[next]!.push (packAddr dg.ip dg.port) dg.data
    next := (next + 1) % n

def netTx (sh : Shared) : IO Unit := do
  repeat
    match (← sh.toNet.recv 500) with
    | none => pure ()
    | some msg =>
      let r ← Sys.sendTo sh.sock (addrIp msg.tag) (addrPort msg.tag) msg.data
      if !(Sys.isErr r) then
        sh.metrics.add M.txPackets 1
        sh.metrics.add M.txBytes msg.data.size.toUInt64
