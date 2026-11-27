import Solana.Wire

/-!
# Hash tables for the CRDS store

Open-addressing tables over flat arrays. They are plain immutable Lean
values; every operation takes the table and returns the new one. Because
the callers hold the only reference, destructuring the old table hands its
arrays over and `set!`/`push` update them in place: functional code, no
copying.
-/

/-- A set of non-zero 64-bit keys. -/
structure Set64 where
  slots : Array UInt64
  count : Nat

namespace Set64

/-- An empty set with `cap` slots (a power of two). -/
def create (cap : Nat) : Set64 := ⟨Array.replicate cap 0, 0⟩

def contains (s : Set64) (k : UInt64) : Bool := Id.run do
  let mask := s.slots.size - 1
  let mut i := k.toNat &&& mask
  for _ in [0:s.slots.size] do
    let e := s.slots[i]!
    if e == k then
      return true
    if e == 0 then
      return false
    i := (i + 1) &&& mask
  return false

/-- Adds `k`. The caller keeps the set at most half full. -/
def insert (s : Set64) (k : UInt64) : Set64 := Id.run do
  let ⟨slots, count⟩ := s
  let mask := slots.size - 1
  let mut i := k.toNat &&& mask
  for _ in [0:slots.size] do
    let e := slots[i]!
    if e == k then
      return ⟨slots, count⟩
    if e == 0 then
      return ⟨slots.set! i k, count + 1⟩
    i := (i + 1) &&& mask
  return ⟨slots, count⟩

end Set64

/-- The node table: one row per validator identity seen in gossip.

`index` maps the first 8 bytes of a public key to a row number (plus one);
`keys` holds the 32-byte keys back to back; `info` holds `fields` words per row. -/
structure Nodes where
  index : Array UInt64
  keys : ByteArray
  info : Array UInt64
  count : Nat

namespace Nodes

def fields : Nat := 14
def fWallclock : Nat := 0
def fVersion : Nat := 1
def fClient : Nat := 2
def fAddr : Nat := 3
def fShred : Nat := 4
def fSnapshot : Nat := 5
/-- where the node serves repair requests, packed as `ip <<< 16 ||| port` (0 = not known) -/
def fRepair : Nat := 6
/-- where the node receives shreds, packed the same way -/
def fTvu : Nat := 7
/-- The node's RPC port, as `ip <<< 16 ||| port`; 0 if it advertises none. -/
def fRpc : Nat := 8
/-- The newest full snapshot the node announces: its slot, and its hash in the four words that follow. -/
def fFullSlot : Nat := 9
def fFullHash : Nat := 10

def notFound : Nat := 0xFFFFFFFF

def create (cap : Nat) : Nodes :=
  ⟨Array.replicate (cap * 2) 0, ByteArray.emptyWithCapacity (cap * 32), Array.emptyWithCapacity (cap * fields), 0⟩

def capacity (n : Nodes) : Nat := n.index.size / 2

/-- Row of the node whose key is `b[o .. o + 32)`, or `notFound`. -/
def find (n : Nodes) (b : ByteArray) (o : Nat) : Nat := Id.run do
  let mask := n.index.size - 1
  let mut i := (Wire.u64 b o).toNat &&& mask
  for _ in [0:n.index.size] do
    let e := n.index[i]!.toNat
    if e == 0 then
      return notFound
    if Wire.eqAt n.keys ((e - 1) * 32) b o 32 then
      return e - 1
    i := (i + 1) &&& mask
  return notFound

def get (n : Nodes) (row field : Nat) : UInt64 := n.info[row * fields + field]!

def set (n : Nodes) (row field : Nat) (v : UInt64) : Nodes :=
  let ⟨index, keys, info, count⟩ := n
  ⟨index, keys, info.set! (row * fields + field) v, count⟩

/-- Appends a row for a key that is not present. The table must not be full. -/
def append (n : Nodes) (b : ByteArray) (o : Nat) : Nodes := Id.run do
  let ⟨index, keys, info, count⟩ := n
  let mask := index.size - 1
  let mut i := (Wire.u64 b o).toNat &&& mask
  while index[i]! != 0 do
    i := (i + 1) &&& mask
  let mut info := info
  for _ in [0:fields] do
    info := info.push 0
  return ⟨index.set! i (count + 1).toUInt64, keys ++ b.extract o (o + 32), info, count + 1⟩

end Nodes
