import Layout
import Directory
import Tally
import Net.Ip
import Solana.Crds
import Encoding.Json
import Encoding.Base58

/-!
# Export: the node's view of the cluster, for machines

Two renderings of the same shared state:

* `json`: one document with the summary and every node (identity, gossip
  address, client, version, latest snapshot slot);
* `prometheus`: the counters and the client/version breakdown in the
  Prometheus text exposition format.

Both read only the shared pages, so any process can produce them.
-/

namespace Export

/-- Name for the client-id column of the directory (stored plus one). -/
def clientLabel (stored : UInt64) : String :=
  if stored == 0 then "unknown" else Crds.clientName (stored - 1)

/-- Rows that have a verified `ContactInfo`. -/
def hasContact (snap : Directory.Snapshot) (row : Nat) : Bool :=
  snap.field row Nodes.fClient != 0

/-- How many nodes run each client and each version. Client keys are the
bucket numbers of `Crds.clientName` (14 = other). -/
def census (snap : Directory.Snapshot) : Tally × Tally := Id.run do
  let mut clients := Tally.create 16
  let mut versions := Tally.create 64
  for row in [0:snap.count] do
    if hasContact snap row then
      let id := snap.field row Nodes.fClient - 1
      clients := clients.add (if id < 14 then id else 14)
      versions := versions.add (snap.field row Nodes.fVersion)
  return (clients, versions)

def uptimeSeconds (sh : Shared) : IO UInt64 := do
  let start ← sh.metrics.get M.startMs
  let now ← IO.monoMsNow
  return (now.toUInt64 - start) / 1000

/-- The view as one JSON document: the summary, and with `withNodes` one
entry per node as well. -/
def json (sh : Shared) (cfg : Config) (withNodes : Bool) : IO String := do
  let m := sh.metrics
  let snap ← Directory.read sh.directory
  let (clients, versions) := census snap
  let mut s := "{\n"
  s := s ++ s!"  \"cluster\": {Json.quote cfg.cluster},\n"
  s := s ++ s!"  \"shredVersion\": {cfg.shredVersion},\n"
  s := s ++ s!"  \"identity\": \"{Base58.encode cfg.pubkey}\",\n"
  s := s ++ s!"  \"timestampMs\": {← Sys.nowMs},\n"
  s := s ++ s!"  \"uptimeSeconds\": {← uptimeSeconds sh},\n"
  s := s ++ s!"  \"tipSlot\": {← m.get M.tipSlot},\n"
  s := s ++ s!"  \"tipReporters\": {← m.get M.tipReporters},\n"
  s := s ++ s!"  \"nodeCount\": {← m.get M.nodes},\n"
  s := s ++ s!"  \"signaturesVerified\": {← m.get M.sigOk},\n"
  s := s ++ s!"  \"signaturesBad\": {← m.get M.sigBad},\n"
  s := s ++ s!"  \"recordsMalformed\": {← m.get M.malformed},\n"
  s := s ++ s!"  \"recordsStored\": {← m.get M.stored},\n"
  s := s ++ s!"  \"rxPackets\": {← m.get M.rxPackets},\n"
  s := s ++ s!"  \"rxBytes\": {← m.get M.rxBytes},\n"
  s := s ++ s!"  \"txPackets\": {← m.get M.txPackets},\n"
  s := s ++ s!"  \"txBytes\": {← m.get M.txBytes},\n"
  s := s ++ s!"  \"pullRequestsSent\": {← m.get M.pullsTx},\n"
  s := s ++ s!"  \"pingsAnswered\": {← m.get M.pongsTx},\n"
  -- per verify tile: microseconds spent inside Ed25519 since start
  s := s ++ "  \"verifyBusyMicros\": ["
  for i in [0:sh.toVerify.size] do
    s := s ++ (if i == 0 then "" else ", ") ++ s!"{← m.get (M.tileBusyUs + i)}"
  s := s ++ "],\n"
  -- breakdowns, most common first
  s := s ++ "  \"clients\": {"
  let mut first := true
  for i in clients.order do
    let key := clients.keys[i]!
    let name := if key == 14 then "other" else Crds.clientName key
    s := s ++ (if first then "" else ", ") ++ s!"\"{name}\": {clients.counts[i]!}"
    first := false
  s := s ++ "},\n  \"versions\": {"
  first := true
  for i in versions.order do
    s := s ++ (if first then "" else ", ") ++ s!"\"{versionString versions.keys[i]!}\": {versions.counts[i]!}"
    first := false
  s := s ++ "},\n  \"records\": {"
  first := true
  for k in [0:14] do
    let count ← m.get (M.kinds + k)
    if count != 0 then
      s := s ++ (if first then "" else ", ") ++ s!"\"{Crds.kindName k}\": {count}"
      first := false
  if !withNodes then
    return s ++ "}\n}\n"
  s := s ++ "},\n  \"nodes\": [\n"
  first := true
  for row in [0:snap.count] do
    if hasContact snap row then
      let addr := snap.field row Nodes.fAddr
      let snapshot := snap.field row Nodes.fSnapshot
      let client := snap.field row Nodes.fClient
      s := s ++ (if first then "    {" else ",\n    {")
      s := s ++ s!"\"identity\": \"{Base58.encode (snap.keys.extract (row * 32) (row * 32 + 32))}\", "
      s := s ++ (if addr == 0 then "\"gossip\": null, "
        else s!"\"gossip\": \"{Ip.toString (addrIp addr)}:{addrPort addr}\", ")
      s := s ++ s!"\"client\": \"{clientLabel client}\", \"clientId\": {client - 1}, "
      s := s ++ s!"\"version\": \"{versionString (snap.field row Nodes.fVersion)}\", "
      s := s ++ s!"\"shredVersion\": {snap.field row Nodes.fShred}, "
      s := s ++ s!"\"wallclockMs\": {snap.field row Nodes.fWallclock}, "
      s := s ++ (if snapshot == 0 then "\"snapshotSlot\": null}" else s!"\"snapshotSlot\": {snapshot}}")
      first := false
  s := s ++ "\n  ]\n}\n"
  return s

/-- One metric: help text, type, and a single unlabelled sample. -/
def sample (name kind help : String) (value : UInt64) : String :=
  s!"# HELP {name} {help}\n# TYPE {name} {kind}\n{name} {value}\n"

/-- The Prometheus text exposition (format version 0.0.4). -/
def prometheus (sh : Shared) (cfg : Config) : IO String := do
  let m := sh.metrics
  let snap ← Directory.read sh.directory
  let (clients, versions) := census snap
  let mut s := ""
  s := s ++ "# HELP leansol_info Constant 1, labelled with what this node is.\n# TYPE leansol_info gauge\n"
  s := s ++ "leansol_info{" ++ s!"cluster={Json.quote cfg.cluster},shred_version=\"{cfg.shredVersion}\"," ++
    s!"identity=\"{Base58.encode cfg.pubkey}\"" ++ "} 1\n"
  s := s ++ sample "leansol_uptime_seconds" "gauge" "Seconds since the node started." (← uptimeSeconds sh)
  s := s ++ sample "leansol_nodes" "gauge" "Nodes with a signature-checked ContactInfo." (← m.get M.nodes)
  s := s ++ sample "leansol_tip_slot" "gauge"
    "Third-highest snapshot slot announced in gossip: at least three signers vouch for it." (← m.get M.tipSlot)
  s := s ++ sample "leansol_tip_reporters" "gauge" "Nodes that have announced a snapshot slot."
    (← m.get M.tipReporters)
  s := s ++ sample "leansol_records_stored" "gauge" "Distinct records currently remembered." (← m.get M.stored)
  s := s ++ sample "leansol_signatures_verified_total" "counter" "Records whose Ed25519 signature verified."
    (← m.get M.sigOk)
  s := s ++ sample "leansol_signatures_bad_total" "counter" "Records or pings whose signature did not verify."
    (← m.get M.sigBad)
  s := s ++ sample "leansol_records_malformed_total" "counter" "Messages that could not be parsed."
    (← m.get M.malformed)
  s := s ++ sample "leansol_rx_packets_total" "counter" "UDP datagrams received." (← m.get M.rxPackets)
  s := s ++ sample "leansol_rx_bytes_total" "counter" "UDP payload bytes received." (← m.get M.rxBytes)
  s := s ++ sample "leansol_tx_packets_total" "counter" "UDP datagrams sent." (← m.get M.txPackets)
  s := s ++ sample "leansol_tx_bytes_total" "counter" "UDP payload bytes sent." (← m.get M.txBytes)
  s := s ++ sample "leansol_pull_requests_sent_total" "counter" "Gossip pull requests sent." (← m.get M.pullsTx)
  s := s ++ sample "leansol_pings_answered_total" "counter" "Ping challenges answered with a pong."
    (← m.get M.pongsTx)
  let mut dropped : UInt64 := 0
  for i in [0:sh.toVerify.size] do
    dropped := dropped + (← sh.toVerify[i]!.dropped) + (← sh.toGossip[i]!.dropped)
  s := s ++ sample "leansol_ring_dropped_total" "counter" "Messages dropped because an IPC ring was full."
    (dropped + (← sh.toNet.dropped))
  s := s ++ "# HELP leansol_records_total Records accepted, by CRDS type.\n# TYPE leansol_records_total counter\n"
  for k in [0:14] do
    s := s ++ "leansol_records_total{" ++ s!"type=\"{Crds.kindName k}\"" ++ "} " ++ s!"{← m.get (M.kinds + k)}\n"
  s := s ++ "# HELP leansol_nodes_by_client Nodes per validator client.\n# TYPE leansol_nodes_by_client gauge\n"
  for i in clients.order do
    let key := clients.keys[i]!
    let name := if key == 14 then "other" else Crds.clientName key
    s := s ++ "leansol_nodes_by_client{" ++ s!"client=\"{name}\"" ++ "} " ++ s!"{clients.counts[i]!}\n"
  s := s ++ "# HELP leansol_nodes_by_version Nodes per software version.\n# TYPE leansol_nodes_by_version gauge\n"
  for i in versions.order do
    s := s ++ "leansol_nodes_by_version{" ++ s!"version=\"{versionString versions.keys[i]!}\"" ++ "} " ++
      s!"{versions.counts[i]!}\n"
  return s

end Export
