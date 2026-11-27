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
  -- blocks fetched from validators and checked by the block tile
  let mut leader := ByteArray.emptyWithCapacity 32
  let mut blockhash := ByteArray.emptyWithCapacity 32
  for i in [0:4] do
    leader := Wire.putU64 leader (← m.get (M.blockLeader + i))
    blockhash := Wire.putU64 blockhash (← m.get (M.blockHash + i))
  let checked ← m.get M.blocksOk
  s := s ++ "  \"blocks\": {"
  s := s ++ s!"\"verified\": {checked}, \"invalid\": {← m.get M.blocksBad}, \"unavailable\": {← m.get M.blocksMissed}, "
  s := s ++ s!"\"transactions\": {← m.get M.blockTxTotal}, \"signatures\": {← m.get M.blockSigTotal}, "
  s := s ++ s!"\"shreds\": {← m.get M.blockShredTotal}, \"entries\": {← m.get M.blockEntryTotal}, "
  s := s ++ s!"\"repairRequests\": {← m.get M.blockRequests}, "
  -- the turbine feed: every block, as its shreds arrive
  s := s ++ s!"\"following\": {if cfg.tvuPort != 0 then "true" else "false"}, "
  s := s ++ s!"\"followed\": {← m.get M.blocksFollowed}, \"linked\": {← m.get M.blocksLinked}, "
  s := s ++ s!"\"onAnotherFork\": {← m.get M.blocksUnlinked}, \"slotsRepaired\": {← m.get M.slotsRepaired}, "
  s := s ++ s!"\"slotsIncomplete\": {← m.get M.slotsIncomplete}, \"shredsReceived\": {← m.get M.shredsRx}, "
  s := s ++ s!"\"shredBytes\": {← m.get M.shredBytes}, \"shredsDuplicate\": {← m.get M.shredsDuplicate}, "
  s := s ++ s!"\"shredsRebuilt\": {← m.get M.shredsRecovered}, \"setsRebuilt\": {← m.get M.setsRecovered}, "
  s := s ++ s!"\"shredsRejected\": {← m.get M.shredsRejected}, \"shredsDropped\": {← m.get M.shredsDropped}, "
  if checked == 0 then
    s := s ++ "\"last\": null},\n"
  else
    s := s ++ s!"\"last\": \{\"slot\": {← m.get M.blockSlot}, \"leader\": \"{Base58.encode leader}\", "
    s := s ++ s!"\"blockhash\": \"{Base58.encode blockhash}\", \"transactions\": {← m.get M.blockTxs}, "
    s := s ++ s!"\"shreds\": {← m.get M.blockShreds}, \"fetchMs\": {← m.get M.blockFetchMs}, "
    s := s ++ s!"\"verifyMs\": {← m.get M.blockVerifyMs}}},\n"
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
      let repair := snap.field row Nodes.fRepair
      s := s ++ (if repair == 0 then "\"repair\": null, "
        else s!"\"repair\": \"{Ip.toString (addrIp repair)}:{addrPort repair}\", ")
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
  s := s ++ sample "leansol_blocks_verified_total" "counter"
    "Blocks fetched from validators whose shreds, leader signature, proof of history and transaction signatures all verified."
    (← m.get M.blocksOk)
  s := s ++ sample "leansol_blocks_invalid_total" "counter" "Blocks fetched that failed a check." (← m.get M.blocksBad)
  s := s ++ sample "leansol_blocks_unavailable_total" "counter"
    "Slots for which no complete block could be fetched (skipped by the leader, or timed out)." (← m.get M.blocksMissed)
  s := s ++ sample "leansol_block_slot" "gauge" "Slot of the last block verified." (← m.get M.blockSlot)
  s := s ++ sample "leansol_block_transactions_total" "counter" "Transactions in verified blocks." (← m.get M.blockTxTotal)
  s := s ++ sample "leansol_block_signatures_total" "counter" "Transaction signatures verified in blocks."
    (← m.get M.blockSigTotal)
  s := s ++ sample "leansol_block_shreds_total" "counter" "Data shreds of verified blocks." (← m.get M.blockShredTotal)
  s := s ++ sample "leansol_blocks_followed_total" "counter" "Blocks assembled from the turbine feed and verified."
    (← m.get M.blocksFollowed)
  s := s ++ sample "leansol_blocks_linked_total" "counter"
    "Verified blocks whose first entry and first shred set follow the verified parent block." (← m.get M.blocksLinked)
  s := s ++ sample "leansol_blocks_other_fork_total" "counter"
    "Verified blocks that do not follow the block verified for their parent slot." (← m.get M.blocksUnlinked)
  s := s ++ sample "leansol_slots_repaired_total" "counter" "Slots completed by asking validators for missing shreds."
    (← m.get M.slotsRepaired)
  s := s ++ sample "leansol_slots_incomplete_total" "counter" "Slots that began arriving and were never completed."
    (← m.get M.slotsIncomplete)
  s := s ++ sample "leansol_shreds_received_total" "counter" "Shreds received over turbine." (← m.get M.shredsRx)
  s := s ++ sample "leansol_shred_bytes_total" "counter" "Bytes of shreds received over turbine." (← m.get M.shredBytes)
  s := s ++ sample "leansol_shreds_duplicate_total" "counter" "Shreds received more than once." (← m.get M.shredsDuplicate)
  s := s ++ sample "leansol_shreds_rebuilt_total" "counter" "Data shreds rebuilt from coding shreds."
    (← m.get M.shredsRecovered)
  s := s ++ sample "leansol_shreds_rejected_total" "counter"
    "Shreds not on a Merkle path to a root signed by a known node." (← m.get M.shredsRejected)
  s := s ++ sample "leansol_shreds_dropped_total" "counter" "Shreds dropped because a follow tile fell behind."
    (← m.get M.shredsDropped)
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
