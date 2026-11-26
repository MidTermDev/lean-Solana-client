import Ipc

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

/-- The shared mappings and the socket, inherited by every tile across `fork`. -/
structure Shared where
  metrics : Ipc.Metrics
  sock : UInt64
  toVerify : Array Ipc.Ring
  toGossip : Array Ipc.Ring
  toNet : Ipc.Ring
  gossipWaiter : Ipc.Waiter

/-- Message tags: the sender's address in the low 48 bits, a kind above. -/
def tagAddr (tag : UInt64) : UInt64 := tag &&& 0xFFFFFFFFFFFF

def tagKind (tag : UInt64) : UInt64 := tag >>> 48

def kindValue : UInt64 := 1
def kindPing : UInt64 := 2

def packAddr (ip : UInt32) (port : UInt16) : UInt64 := (ip.toUInt64 <<< 16) ||| port.toUInt64

def addrIp (addr : UInt64) : UInt32 := (addr >>> 16).toUInt32

def addrPort (addr : UInt64) : UInt16 := addr.toUInt16
