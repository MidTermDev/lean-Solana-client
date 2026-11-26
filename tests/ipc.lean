import Ipc

/-! Two processes, one ring, one futex: the producer sends 200000 numbered
messages, the consumer checks order and content and reports through a
shared counter page. -/

def consume (ring : Ipc.Ring) (m : Ipc.Metrics) (total : Nat) : IO Unit := do
  let mut expect : UInt64 := 0
  let mut sum : UInt64 := 0
  while expect < total.toUInt64 do
    match (← ring.recv 1000) with
    | none => pure ()
    | some msg =>
      if msg.tag != expect || msg.data.size != 5 + (expect % 7).toNat then
        m.set 1 1
      sum := sum + msg.data[0]!.toUInt64
      expect := expect + 1
  m.set 0 sum
  m.set 2 1

def main : IO Unit := do
  let total := 200000
  let w ← Ipc.Waiter.create
  let ring ← Ipc.Ring.create 1024 256 w
  let m ← Ipc.Metrics.create
  let pid ← Sys.fork
  if pid == 0 then
    consume ring m total
    Sys.exit 0
  let mut sent := 0
  let mut sum : UInt64 := 0
  let mut retries := 0
  while sent < total do
    let mut payload := ByteArray.emptyWithCapacity 16
    payload := payload.push sent.toUInt8
    for _ in [0:4 + sent % 7] do
      payload := payload.push 0xAB
    if (← ring.push sent.toUInt64 payload) then
      sum := sum + sent.toUInt8.toUInt64
      sent := sent + 1
    else
      retries := retries + 1
      IO.sleep 1
  -- wait for the consumer to finish
  let mut waited := 0
  while (← m.get 2) == 0 && waited < 5000 do
    IO.sleep 1
    waited := waited + 1
  let got ← m.get 0
  let bad ← m.get 1
  IO.println s!"sent {sent} messages, checksum match: {got == sum}, order errors: {bad}, consumer done: {(← m.get 2) == 1}"
