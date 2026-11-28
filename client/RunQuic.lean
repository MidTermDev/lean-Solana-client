import Net.Quic
import RunBlock

/-! `leansol quic IP:PORT [PROTOCOL]`: opens a QUIC connection to a validator, as one validator does to
another (TLS 1.3 with both sides' identity keys), says who answered, and closes it. A check of the
transport, with a throwaway identity unless `--identity FILE` gives one. -/

namespace RunQuic

def usage : String :=
  "usage: leansol quic IP:PORT [PROTOCOL] [--identity FILE]\n" ++
  "  PROTOCOL   what is spoken over the connection: solana-tpu (the default), alpenglow-v1\n"

def fail (why : String) : IO Unit := do
  IO.eprintln s!"leansol quic: {why}"
  Sys.exit 1

def main : IO Unit := do
  let argc ← Sys.argc
  let mut target := ""
  let mut protocol := "solana-tpu"
  let mut identityFile := ""
  let mut i := 2
  while i < argc do
    let a ← Sys.arg i
    if a == "--identity" && i + 1 < argc then
      identityFile := ← Sys.arg (i + 1)
      i := i + 2
    else
      if target == "" then
        target := a
      else
        protocol := a
      i := i + 1
  let (ip, port) := RunBlock.parseAddr target
  if target == "" || ip == 0 then
    fail usage
  let mut seed ← IO.getRandomBytes 32
  if identityFile != "" then
    seed := (← Sys.readFile identityFile 64).extract 0 32
    if seed.size != 32 then
      fail s!"{identityFile} holds no identity key"
  let identity := Ed25519.publicKey seed
  let sock ← Sys.udpSocket
  let _ ← Sys.bind sock 0 0
  Sys.setTimeout sock 20 100
  let fresh ← IO.getRandomBytes 80
  let name := s!"{Ip.toString ip}.{port}.sol"
  let (first, hello) := Quic.connect (fresh.extract 0 32) (fresh.extract 32 64) (fresh.extract 64 72) (fresh.extract 72 80) seed identity name protocol
  let mut c := first
  IO.println s!"to {target} as {Base58.encode identity}, speaking {protocol}"
  let _ ← Sys.sendTo sock ip port hello
  let started ← Sys.nowMs
  let mut last := started
  let mut said := 0
  repeat
    let now ← Sys.nowMs
    if now - started > 5000 || c.closed || (c.established && now - started > 1500) then
      break
    let got ← Sys.recvFrom sock 2048
    let mut out : Array ByteArray := Array.emptyWithCapacity 0
    if got.data.size != 0 then
      let (after, answers) := c.receive got.data
      c := after
      out := answers
      last := now
    else if now - last > 300 then
      let (after, answers) := c.again
      c := after
      out := answers
      last := now
    for d in out do
      let _ ← Sys.sendTo sock ip port d
    if said == 0 && c.tls.stage >= 1 then
      IO.println s!"  {now - started} ms: keys agreed"
      said := 1
    if said == 1 && c.tls.stage == 2 then
      IO.println s!"  {now - started} ms: the handshake is complete; the other side is {Base58.encode c.tls.peer}"
      said := 2
    if said == 2 && c.established then
      IO.println s!"  {now - started} ms: and it has confirmed it"
      said := 3
  if c.closed then
    IO.println s!"  {c.error}"
  else if !c.established then
    IO.println s!"  no connection after 5 seconds (reached stage {c.tls.stage})"
  else
    let (_, bye) := c.goodbye
    let _ ← Sys.sendTo sock ip port bye
    IO.println "  closed"

end RunQuic
