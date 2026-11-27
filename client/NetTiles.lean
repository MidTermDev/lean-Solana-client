import Layout
import Solana.Shred

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
    if sh.tvuSock == sh.sock && (dg.data.size == Shred.dataPayload || dg.data.size == Shred.codePayload)
        && Wire.u32 dg.data 0 > 5 then
      -- Gossip and shreds share this socket. A gossip message starts with its kind, a number from 0 to 5;
      -- a shred starts with a signature and has one of two exact sizes.
      routeShred sh dg.data
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
