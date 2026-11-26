import Layout
import NetTiles
import VerifyTile
import GossipTile
import Dashboard
import Net.Dns

/-!
# lean-solana-client

The supervisor: parse the command line, find the cluster, create the shared
memory, fork the tiles, then sit in a loop drawing the dashboard and making
sure every tile is still alive.
-/

def usage : String :=
  "lean-solana-client — a Solana gossip client written in Lean, compiled by leanc\n" ++
  "\n" ++
  "usage: leansol [options]\n" ++
  "  --cluster NAME      mainnet (default), testnet or devnet\n" ++
  "  --entrypoint HOST   gossip entrypoint to join through (host or host:port; repeatable)\n" ++
  "  --port N            UDP port to bind (default: chosen by the kernel)\n" ++
  "  --tiles N           number of signature-verification processes (default 4, max 16)\n" ++
  "  --fanout N          peers pulled from every 200 ms, besides entrypoints (default 12)\n" ++
  "  --duration SECONDS  exit after this long (default: run until interrupted)\n" ++
  "  --plain             one status line per second instead of the dashboard\n" ++
  "  --help              this text\n"

/-- Splits `host:port`; the port defaults to 8001. -/
def splitHostPort (s : String) : String × UInt16 := Id.run do
  let b := s.toUTF8
  for i in [0:b.size] do
    if b[i]! == 58 then
      let port := (String.fromUTF8! (b.extract (i + 1) b.size)).toNat!
      return (String.fromUTF8! (b.extract 0 i), port.toUInt16)
  return (s, 8001)

def die (msg : String) : IO Unit := do
  IO.eprintln s!"leansol: {msg}"
  Sys.exit 1

/-- Forks a child. Returns true in the child, after arranging for it to die with the supervisor. -/
def spawn (pids : Array UInt64) : IO (Array UInt64 × Bool) := do
  let pid ← Sys.fork
  if pid == 0 then
    Sys.dieWithParent
    return (pids, true)
  if Sys.isErr pid then
    die "fork failed"
  return (pids.push pid, false)

def killAll (pids : Array UInt64) : IO Unit := do
  for pid in pids do
    Sys.kill pid 9

def main : IO Unit := do
  -- ------------------------------------------------------------ command line
  let argc ← Sys.argc
  let mut cluster := "mainnet"
  let mut hosts : Array String := #[]
  let mut port : UInt16 := 0
  let mut tiles := 4
  let mut fanout := 12
  let mut duration := 0
  let mut plain := !(← Sys.isTty 1)
  let mut i := 1
  while i < argc do
    let a ← Sys.arg i
    let hasValue := i + 1 < argc
    if a == "--help" || a == "-h" then
      IO.print usage
      return
    else if a == "--plain" then
      plain := true
      i := i + 1
    else if !hasValue then
      IO.eprint usage
      Sys.exit 2
    else
      let v ← Sys.arg (i + 1)
      if a == "--cluster" then
        cluster := v
      else if a == "--entrypoint" then
        hosts := hosts.push v
      else if a == "--port" then
        port := v.toNat!.toUInt16
      else if a == "--tiles" then
        tiles := v.toNat!
      else if a == "--fanout" then
        fanout := v.toNat!
      else if a == "--duration" then
        duration := v.toNat!
      else
        IO.eprint usage
        Sys.exit 2
      i := i + 2
  if tiles == 0 || tiles > 16 then
    die "--tiles must be between 1 and 16"
  if hosts.size == 0 then
    let domain := if cluster == "mainnet" then "mainnet-beta.solana.com"
      else if cluster == "testnet" then "testnet.solana.com"
      else if cluster == "devnet" then "devnet.solana.com"
      else ""
    if domain == "" then
      die s!"unknown cluster '{cluster}' (expected mainnet, testnet or devnet)"
    hosts := #["entrypoint." ++ domain, "entrypoint2." ++ domain, "entrypoint3." ++ domain]

  -- ------------------------------------------------- find the cluster and us
  let mut entrypoints : Array UInt64 := #[]
  let mut publicIp : UInt32 := 0
  let mut shredVersion : UInt64 := 0
  for h in hosts do
    let (host, eport) := splitHostPort h
    let ip ← Dns.resolve host
    if ip == 0 then
      IO.eprintln s!"leansol: cannot resolve {host}, skipping"
      continue
    entrypoints := entrypoints.push (packAddr ip eport)
    if shredVersion == 0 then
      -- the entrypoint tells us our public address and the cluster's shred version
      let echo ← Gossip.ipEcho ip eport
      if echo.shredVersion != 0 then
        publicIp := echo.ip
        shredVersion := echo.shredVersion
    IO.eprintln s!"leansol: entrypoint {host} is {Ip.toString ip}:{eport}"
  if entrypoints.size == 0 then
    die "no entrypoint could be resolved"
  if shredVersion == 0 then
    die "no entrypoint answered the IP echo request (is outbound TCP to the gossip port blocked?)"

  -- ------------------------------------------------------- identity & socket
  let seed ← IO.getRandomBytes 32
  let pubkey := Ed25519.publicKey seed
  let sock ← Sys.udpSocket
  if Sys.isErr sock then
    die "cannot create a UDP socket"
  if Sys.isErr (← Sys.bind sock 0 port) then
    die s!"cannot bind UDP port {port}"
  Sys.setRecvBuffer sock 0x800000
  Sys.setTimeout sock 20 500
  let boundPort ← Sys.localPort sock
  let cfg : Config := ⟨seed, pubkey, publicIp, boundPort, shredVersion, entrypoints, (← Sys.nowMs) * 1000, fanout⟩
  IO.eprintln s!"leansol: we are {Ip.toString publicIp}:{boundPort}, identity {Base58.encode pubkey}, shred version {shredVersion}"

  -- ---------------------------------------------------------- shared memory
  let metrics ← Ipc.Metrics.create
  let gossipWaiter ← Ipc.Waiter.create
  let mut toVerify : Array Ipc.Ring := #[]
  let mut toGossip : Array Ipc.Ring := #[]
  for _ in [0:tiles] do
    toVerify := toVerify.push (← Ipc.Ring.create 4096 1536 (← Ipc.Waiter.create))
    toGossip := toGossip.push (← Ipc.Ring.create 4096 1536 gossipWaiter)
  let toNet ← Ipc.Ring.create 4096 1536 (← Ipc.Waiter.create)
  let sh : Shared := ⟨metrics, sock, toVerify, toGossip, toNet, gossipWaiter⟩

  -- ---------------------------------------------------------------- the tiles
  let mut pids : Array UInt64 := #[]
  let (p1, child1) ← spawn pids
  pids := p1
  if child1 then
    netRx sh
    return
  let (p2, child2) ← spawn pids
  pids := p2
  if child2 then
    netTx sh
    return
  for t in [0:tiles] do
    let (p, child) ← spawn pids
    pids := p
    if child then
      verifyTile sh t
      return
  let (p3, child3) ← spawn pids
  pids := p3
  if child3 then
    gossipTile sh cfg
    return

  -- ----------------------------------------------------------- the supervisor
  let startMs ← IO.monoMsNow
  let mut prev ← Dash.sample sh
  if !plain then
    IO.print "\x1b[2J"
  repeat
    IO.sleep (if plain then 1000 else 500)
    let dead ← Sys.reapChild
    if dead != 0 then
      killAll pids
      die s!"tile process {dead} exited unexpectedly"
    let cur ← Dash.sample sh
    if plain then
      IO.println (← Dash.logLine sh startMs prev cur)
    else
      IO.print (← Dash.frame sh cfg cluster startMs prev cur)
    prev := cur
    if duration != 0 && cur.ms - startMs >= duration * 1000 then
      break
  killAll pids
  let m := sh.metrics
  IO.println s!"nodes seen: {← m.get M.nodes}, signatures verified: {← m.get M.sigOk}, bad: {← m.get M.sigBad}, chain tip: {← m.get M.tipSlot}"
