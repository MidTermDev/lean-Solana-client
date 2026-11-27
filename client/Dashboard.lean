import Layout
import Fmt
import Net.Ip
import Solana.Crds
import Encoding.Base58

/-!
# The dashboard

Drawn by the supervisor from the shared metrics page. The tiles never
print; they only bump counters.
-/

namespace Dash

def esc : String := "\x1b["
def reset : String := "\x1b[0m"
def bold : String := "\x1b[1m"
def dim : String := "\x1b[2m"
def green : String := "\x1b[32m"
def cyan : String := "\x1b[36m"
def yellow : String := "\x1b[33m"
def red : String := "\x1b[31m"
def magenta : String := "\x1b[35m"

/-- Ends a line: clear whatever was there before, then newline. -/
def eol : String := "\x1b[K\n"

/-- One snapshot of the counters the dashboard turns into rates. -/
structure Sample where
  ms : Nat
  rxPackets : UInt64
  rxBytes : UInt64
  txPackets : UInt64
  txBytes : UInt64
  sigs : UInt64
  busyUs : Array UInt64

def sample (sh : Shared) : IO Sample := do
  let m := sh.metrics
  let mut busy : Array UInt64 := Array.emptyWithCapacity 8
  for i in [0:sh.toVerify.size] do
    busy := busy.push (← m.get (M.tileBusyUs + i))
  return ⟨← IO.monoMsNow, ← m.get M.rxPackets, ← m.get M.rxBytes, ← m.get M.txPackets, ← m.get M.txBytes,
    (← m.get M.sigOk) + (← m.get M.sigBad), busy⟩

/-- `delta` per second over `ms` milliseconds. -/
def perSec (delta : UInt64) (ms : Nat) : UInt64 :=
  if ms == 0 then 0 else delta * 1000 / ms.toUInt64

def row (label value : String) : String :=
  "   " ++ Fmt.padRight label 20 ++ Fmt.padLeft value 13

/-- The full-screen view. -/
def frame (sh : Shared) (cfg : Config) (startMs : Nat) (prev cur : Sample) : IO String := do
  let m := sh.metrics
  let dt := cur.ms - prev.ms
  let up := ((cur.ms - startMs) / 1000).toUInt64
  let id := Base58.encode cfg.pubkey
  let mut s := "\x1b[H"
  s := s ++ s!" {bold}{magenta}◆ lean-solana-client{reset}  {dim}compiled by leanc · no libc · futex IPC{reset}{eol}"
  s := s ++ s!"   {cfg.cluster} · shred version {cfg.shredVersion} · up {Fmt.clock up}{eol}"
  s := s ++ s!"   identity {cyan}{id}{reset}{eol}"
  s := s ++ s!"   gossip   {Ip.toString cfg.publicIp}:{cfg.port}{eol}"
  if cfg.httpAddr != 0 then
    let url := s!"http://{Ip.toString (addrIp cfg.httpAddr)}:{addrPort cfg.httpAddr}"
    s := s ++ s!"   http     {url}/metrics · {url}/nodes.json{eol}"
  s := s ++ eol

  let nodes ← m.get M.nodes
  let tip ← m.get M.tipSlot
  let sigOk ← m.get M.sigOk
  let sigBad ← m.get M.sigBad
  let malformed ← m.get M.malformed
  s := s ++ s!" {bold}CLUSTER{reset}  {dim}every record below passed an Ed25519 check written in Lean{reset}{eol}"
  s := s ++ row "nodes in gossip" (Fmt.thousands nodes) ++ "     " ++
    row "chain tip (gossip)" (if tip == 0 then "…" else Fmt.thousands tip) ++ eol
  s := s ++ row "signatures verified" (green ++ Fmt.padLeft (Fmt.thousands sigOk) 13 ++ reset) ++ "     " ++
    row "bad signatures" ((if sigBad == 0 then dim else red) ++ Fmt.padLeft (Fmt.thousands sigBad) 13 ++ reset) ++ eol
  s := s ++ row "records stored" (Fmt.thousands (← m.get M.stored)) ++ "     " ++
    row "malformed" (Fmt.thousands malformed) ++ eol ++ eol

  -- clients and versions side by side
  s := s ++ s!" {bold}CLIENTS{reset}{Fmt.spaces 40}{bold}VERSIONS{reset}{eol}"
  let mut cIds : Array Nat := Array.emptyWithCapacity 16
  let mut cCounts : Array UInt64 := Array.emptyWithCapacity 16
  for c in [0:15] do
    let count ← m.get (M.clients + c)
    if count != 0 then
      cIds := cIds.push c
      cCounts := cCounts.push count
  for line in [0:6] do
    -- next most common client
    let mut best := 0
    let mut bestCount : UInt64 := 0
    for j in [0:cCounts.size] do
      if cCounts[j]! > bestCount then
        best := j
        bestCount := cCounts[j]!
    let mut left := Fmt.spaces 47
    if bestCount != 0 then
      let name := if cIds[best]! == 14 then "other" else Crds.clientName cIds[best]!.toUInt64
      left := "   " ++ Fmt.padRight name 22 ++ Fmt.padLeft (Fmt.thousands bestCount) 6 ++ "  " ++ cyan ++
        Fmt.bar bestCount nodes 14 ++ reset
      cCounts := cCounts.set! best 0
    let vkey ← m.get (M.versions + 2 * line)
    let vcount ← m.get (M.versions + 2 * line + 1)
    let mut right := ""
    if vcount != 0 then
      right := Fmt.padRight (versionString vkey) 10 ++ Fmt.padLeft (Fmt.thousands vcount) 6 ++ "  " ++ cyan ++
        Fmt.bar vcount nodes 14 ++ reset
    s := s ++ left ++ right ++ eol
  s := s ++ eol

  -- record types, most common first
  s := s ++ s!" {bold}RECORDS{reset}  "
  let mut kCounts : Array UInt64 := Array.emptyWithCapacity 14
  for k in [0:14] do
    kCounts := kCounts.push (← m.get (M.kinds + k))
  for i in [0:5] do
    let mut best := 0
    let mut bestCount : UInt64 := 0
    for k in [0:14] do
      if kCounts[k]! > bestCount then
        best := k
        bestCount := kCounts[k]!
    if bestCount != 0 then
      s := s ++ (if i == 0 then "" else s!" {dim}·{reset} ") ++ s!"{Crds.kindName best} {Fmt.thousands bestCount}"
      kCounts := kCounts.set! best 0
  s := s ++ eol ++ eol

  -- the processes
  let nverify := sh.toVerify.size
  let ntiles := nverify + 3 + (if cfg.httpAddr != 0 then 1 else 0)
  s := s ++ s!" {bold}TILES{reset}  {dim}{ntiles} processes · shared-memory rings · one futex each{reset}{eol}"
  s := s ++ s!"   {yellow}net-rx {reset}  {Fmt.padLeft (Fmt.thousands (perSec (cur.rxPackets - prev.rxPackets) dt)) 7} pkt/s" ++
    s!"  {Fmt.padLeft (Fmt.rate (perSec (cur.rxBytes - prev.rxBytes) dt)) 11}" ++
    s!"   total {Fmt.thousands cur.rxPackets}{eol}"
  let mut load := ""
  let mut queued : UInt64 := 0
  let mut dropped : UInt64 := 0
  for i in [0:nverify] do
    -- share of wall time this tile spent inside Ed25519
    let pct := if dt == 0 then 0 else (cur.busyUs[i]! - prev.busyUs[i]!) / (dt.toUInt64 * 10)
    load := load ++ Fmt.padLeft s!"{pct}%" 5
    queued := queued + (← sh.toVerify[i]!.depth)
    dropped := dropped + (← sh.toVerify[i]!.dropped)
  s := s ++ s!"   {yellow}verify {reset}  {Fmt.padLeft (Fmt.thousands (perSec (cur.sigs - prev.sigs) dt)) 7} sig/s" ++
    s!"  load{load}   queued {queued}  dropped {dropped}{eol}"
  let mut gq : UInt64 := 0
  for i in [0:nverify] do
    gq := gq + (← sh.toGossip[i]!.depth)
  s := s ++ s!"   {yellow}gossip {reset}  pulls {Fmt.thousands (← m.get M.pullsTx)}" ++
    s!" · pings answered {Fmt.thousands (← m.get M.pongsTx)}" ++
    s!" · bloom partitions {(1 : UInt64) <<< (← m.get M.maskBits)}   queued {gq}{eol}"
  s := s ++ s!"   {yellow}net-tx {reset}  {Fmt.padLeft (Fmt.thousands (perSec (cur.txPackets - prev.txPackets) dt)) 7} pkt/s" ++
    s!"  {Fmt.padLeft (Fmt.rate (perSec (cur.txBytes - prev.txBytes) dt)) 11}" ++
    s!"   total {Fmt.thousands cur.txPackets}{eol}{eol}"
  s := s ++ s!" {dim}ctrl-c to quit{reset}{eol}\x1b[J"
  return s

/-- One line per tick, for logs and pipes. -/
def logLine (sh : Shared) (startMs : Nat) (prev cur : Sample) : IO String := do
  let m := sh.metrics
  let dt := cur.ms - prev.ms
  let up := ((cur.ms - startMs) / 1000).toUInt64
  return s!"[{Fmt.clock up}] nodes={← m.get M.nodes} tip={← m.get M.tipSlot} verified={← m.get M.sigOk}" ++
    s!" bad={← m.get M.sigBad} malformed={← m.get M.malformed} stored={← m.get M.stored}" ++
    s!" sig/s={perSec (cur.sigs - prev.sigs) dt} rx={perSec (cur.rxBytes - prev.rxBytes) dt}B/s" ++
    s!" pulls={← m.get M.pullsTx} pongs={← m.get M.pongsTx}" ++
    s!" blocks={← m.get M.blocksOk} block={← m.get M.blockSlot} txs={← m.get M.blockTxTotal}" ++
    s!" invalid={← m.get M.blocksBad} unavailable={← m.get M.blocksMissed}" ++
    s!" shreds={← m.get M.shredsRx} data={← m.get M.shredsData} code={← m.get M.shredsCode} badshreds={← m.get M.shredsBad}" ++
    s!" followed={← m.get M.blocksFollowed} linked={← m.get M.blocksLinked} scheduled={← m.get M.blocksScheduled} rebuilt={← m.get M.shredsRecovered}/{← m.get M.setsRecovered}" ++
    s!" rejected={← m.get M.shredsRejected} dup={← m.get M.shredsDuplicate} dropped={← m.get M.shredsDropped} incomplete={← m.get M.slotsIncomplete} repaired={← m.get M.slotsRepaired} forked={← m.get M.blocksUnlinked}"

end Dash
