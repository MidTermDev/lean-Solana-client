import Ipc
import Solana.Shred

/-!
# What the tiles share

The client is a handful of single-purpose processes ("tiles", after
Firedancer). They share nothing but the mappings described here, all
created by the supervisor before it forks:

                       +--------+   ring    +-----------+   ring    +--------+
    UDP socket ------> | net-rx | --------> | verify x N | --------> | gossip |
                       +--------+           +-----------+           +--------+
                                                                        |  ring
    UDP socket <------------------------------------------------- +--------+
                                                                  | net-tx |
                                                                  +--------+

A `block` tile, with a socket of its own, asks validators for the shreds of
recent blocks and checks them (see `BlockTile`).

An optional `http` tile serves the same state to the outside (Prometheus
metrics and JSON) from the shared pages, without involving the other tiles.

Every arrow between tiles is an `Ipc.Ring`; every tile that waits, waits on
a futex. The metrics page is the only other shared state: plain counters the
supervisor reads to draw the dashboard.
-/

-- Slots in the shared metrics page.
namespace M

def rxPackets : Nat := 0
def rxBytes : Nat := 1
def txPackets : Nat := 2
def txBytes : Nat := 3
def sigOk : Nat := 4
def sigBad : Nat := 5
def malformed : Nat := 6
def pingsRx : Nat := 7
def pongsTx : Nat := 8
def pullsTx : Nat := 9
def pullRespRx : Nat := 10
def pushRx : Nat := 11
def pullReqRx : Nat := 12
def otherRx : Nat := 13
def valuesNew : Nat := 14
def valuesDup : Nat := 15
def nodes : Nat := 16
def tipSlot : Nat := 17
def stored : Nat := 18
def maskBits : Nat := 19
def tipReporters : Nat := 20
/-- Monotonic clock (ms) when the supervisor started. -/
def startMs : Nat := 21
/-- 14 counters, one per CRDS record type. -/
def kinds : Nat := 32
/-- 16 buckets: client ids 0..13, then "other". -/
def clients : Nat := 64
/-- 8 pairs of (packed version, node count), most common first. -/
def versions : Nat := 96
/-- Per verify tile: signatures checked. -/
def tileSigs : Nat := 128
/-- Per verify tile: microseconds spent verifying. -/
def tileBusyUs : Nat := 160
-- The block tile: blocks fetched from validators and checked.
def blocksOk : Nat := 192
def blocksBad : Nat := 193
/-- Slots for which no complete block arrived (skipped by their leader, or the fetch timed out). -/
def blocksMissed : Nat := 194
def blockSlot : Nat := 195
def blockTxs : Nat := 196
def blockShreds : Nat := 197
def blockVerifyMs : Nat := 198
def blockFetchMs : Nat := 199
def blockTxTotal : Nat := 200
def blockSigTotal : Nat := 201
def blockShredTotal : Nat := 202
def blockEntryTotal : Nat := 203
/-- 4 words: the leader of the last verified block. -/
def blockLeader : Nat := 204
/-- 4 words: its blockhash. -/
def blockHash : Nat := 208
def blockRequests : Nat := 212
-- The turbine tile: shreds that arrive unasked, relayed by validators.
def shredsRx : Nat := 216
def shredsData : Nat := 217
def shredsCode : Nat := 218
def shredsBad : Nat := 219
def shredBytes : Nat := 220
/-- Shreds the block tile could not take because it had fallen behind. -/
def shredsDropped : Nat := 221
/-- Data shreds rebuilt from coding shreds, and the sets that needed it. -/
def shredsRecovered : Nat := 222
def setsRecovered : Nat := 223
/-- Shreds refused: not on a Merkle path to a root signed by a known node. -/
def shredsRejected : Nat := 224
/-- Blocks assembled from the turbine feed, and those whose parent was in hand to link to. -/
def blocksFollowed : Nat := 225
def blocksLinked : Nat := 226
/-- Slots that began arriving but were never completed. -/
def slotsIncomplete : Nat := 227
def shredsDuplicate : Nat := 228
/-- Slots completed by asking validators for the shreds turbine did not bring. -/
def slotsRepaired : Nat := 229
/-- Blocks that turned out not to follow the block verified for their parent slot (another fork). -/
def blocksUnlinked : Nat := 230
/-- Blocks verified against the leader the schedule names for their slot (not merely a node known from gossip). -/
def blocksScheduled : Nat := 231

end M

/-- Who we are and where the cluster is. Fixed before the tiles start. -/
structure Config where
  seed : ByteArray
  pubkey : ByteArray
  publicIp : UInt32
  port : UInt16
  shredVersion : UInt64
  /-- Entrypoint addresses, packed as `ip <<< 16 ||| port`. -/
  entrypoints : Array UInt64
  outsetUs : UInt64
  fanout : Nat
  cluster : String
  /-- Where the HTTP endpoint listens (packed address), or 0 when it is off. -/
  httpAddr : UInt64
  /-- Seconds between the blocks the block tile fetches and checks; 0 turns it off. -/
  blockInterval : UInt64
  /-- The UDP port shreds are received on (and advertised in gossip), or 0 for none. -/
  tvuPort : UInt16
  /-- How many tiles assemble and verify blocks from those shreds. -/
  followTiles : Nat
  /-- The leader schedule (`LeaderSchedule.table`), computed from the stakes in a loaded snapshot; empty without one. -/
  schedule : ByteArray
  /-- Where every verified block is saved for `leansol replay --live` to execute; empty for nowhere. -/
  spool : String

/-- The shared mappings and the socket, inherited by every tile across `fork`. -/
structure Shared where
  metrics : Ipc.Metrics
  sock : UInt64
  toVerify : Array Ipc.Ring
  toGossip : Array Ipc.Ring
  toNet : Ipc.Ring
  gossipWaiter : Ipc.Waiter
  /-- Base of the shared node directory (see `Directory`). -/
  directory : UInt64
  /-- Listening socket of the HTTP endpoint, or `noFd`. -/
  httpFd : UInt64
  /-- The socket shreds arrive on, or `noFd`. -/
  tvuSock : UInt64
  /-- Shreds on their way to the follow tiles: one ring per tile, a slot's shreds always on the same one. -/
  toBlocks : Array Ipc.Ring
  /-- A small shared table of the blocks verified so far, so that a tile can find the parent of a
  block another tile verified (see `FollowTile`). -/
  seenBase : UInt64

def noFd : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- Message tags: the sender's address in the low 48 bits, a kind above. -/
def tagAddr (tag : UInt64) : UInt64 := tag &&& 0xFFFFFFFFFFFF

def tagKind (tag : UInt64) : UInt64 := tag >>> 48

def kindValue : UInt64 := 1
def kindPing : UInt64 := 2

def packAddr (ip : UInt32) (port : UInt16) : UInt64 := (ip.toUInt64 <<< 16) ||| port.toUInt64

def addrIp (addr : UInt64) : UInt32 := (addr >>> 16).toUInt32

def addrPort (addr : UInt64) : UInt16 := addr.toUInt16

/-- A packed `major <<< 32 ||| minor <<< 16 ||| patch` as `major.minor.patch`. -/
def versionString (key : UInt64) : String :=
  s!"{key >>> 32}.{(key >>> 16) &&& 0xffff}.{key &&& 0xffff}"

/-- Hands a shred that arrived from the network to the follow tile that
handles its slot, with the Merkle root it leads to appended (computing it
here keeps the follow tiles free for the work that cannot be shared out). -/
def routeShred (sh : Shared) (data : ByteArray) : IO Unit := do
  let m := sh.metrics
  m.add M.shredsRx 1
  m.add M.shredBytes data.size.toUInt64
  let h := Shred.parse data
  let root := Shred.merkleRoot data h
  if !h.ok || root.size != 32 then
    m.add M.shredsBad 1
  else
    m.add (if h.isData then M.shredsData else M.shredsCode) 1
    if !(← sh.toBlocks[h.slot.toNat % sh.toBlocks.size]!.push 0 (data ++ root)) then
      m.add M.shredsDropped 1
