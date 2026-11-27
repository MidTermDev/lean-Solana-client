import Sys
import Solana.Table

/-!
# The node directory

The gossip tile owns the node table. To let other processes read it without
stopping the tile, it periodically copies the table into this shared mapping
under a *seqlock*: a counter that is odd while a write is in progress.
Readers copy the data out and retry if the counter moved underneath them.
The writer never waits for anyone.

Layout: `+0` sequence counter, `+8` row count, `+4096` keys (32 bytes per
row), then `Nodes.fields` words per row.
-/

namespace Directory

def capacity : Nat := 32768
def keysAt : UInt64 := 4096
/-- Bytes of one row of fields. -/
def row : Nat := Nodes.fields * 8
def infoAt : UInt64 := 4096 + 32768 * 32
def bytes : UInt64 := 4096 + 32768 * 32 + 32768 * row.toUInt64

def create : IO UInt64 := Sys.mmapShared bytes

/-- Publishes the table. Called by the gossip tile only. -/
def write (base : UInt64) (nodes : Nodes) : IO Unit := do
  let keys := nodes.keys
  let info := nodes.info
  let n := if nodes.count < capacity then nodes.count.toUInt64 else capacity.toUInt64
  let seq ← Mem.load64 base
  Mem.store64 base (seq + 1)
  let kp := Unsafe.addr keys
  let ip := Unsafe.arrayAddr info
  Mem.copy (base + keysAt) (kp + 24) (n * 32)
  Mem.copy (base + infoAt) (ip + 24) (n * row.toUInt64)
  Mem.store64 (base + 8) n
  Mem.store64 base (seq + 2)

/-- A private, consistent copy of the directory. -/
structure Snapshot where
  count : Nat
  keys : ByteArray
  info : ByteArray

/-- Copies the directory out, retrying while the writer is mid-update. -/
def read (base : UInt64) : IO Snapshot := do
  for _ in [0:2000] do
    let s1 ← Mem.load64 base
    if s1 % 2 == 1 then
      Mem.pause
      continue
    let n ← Mem.load64 (base + 8)
    if n > capacity.toUInt64 then
      continue
    let keys := Sys.scratch (n.toNat * 32)
    let kp := Unsafe.addr keys
    Mem.copy (kp + 24) (base + keysAt) (n * 32)
    let keys ← Sys.setSize keys (n * 32)
    let info := Sys.scratch (n.toNat * row)
    let ip := Unsafe.addr info
    Mem.copy (ip + 24) (base + infoAt) (n * row.toUInt64)
    let info ← Sys.setSize info (n * row.toUInt64)
    let s2 ← Mem.load64 base
    if s1 == s2 then
      return ⟨n.toNat, keys, info⟩
  return ⟨0, ByteArray.empty, ByteArray.empty⟩

/-- One field of one row of a snapshot. -/
def Snapshot.field (s : Snapshot) (row field : Nat) : UInt64 :=
  Wire.u64 s.info (row * Directory.row + field * 8)

end Directory
