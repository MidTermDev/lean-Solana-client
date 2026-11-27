import Crypto.Sha256
import Crypto.ReedSolomon
import Solana.Wire

/-!
# Shreds

A leader does not send a block. It cuts the block's bytes into pieces of
about a kilobyte, each small enough for one UDP packet, and sends those:
**shreds**. For every 32 data shreds it adds 32 *coding* shreds computed
from them, so that any 32 of the 64 are enough to rebuild the other 32.

All 64 shreds of such a set are the leaves of a Merkle tree. The leader
signs the root, once, and every shred carries that signature and its own
path to the root, so one shred on its own can be checked against the
leader's key. Each set also carries the root of the set before it, which
chains the sets of a block (and the blocks of a fork) together.

    data shred                                       1,203 bytes
    +-----------+---------+--------------------+------------------+--------+
    | signature | headers | data               | root of the      | Merkle |
    | 64        | 24      | (up to capacity)   | previous set, 32 | path   |
    +-----------+---------+--------------------+------------------+--------+
                 variant, slot, index, version, set index, parent offset, flags, size
-/

namespace Shred

def dataPayload : Nat := 1203
def codePayload : Nat := 1228
/-- The most data shreds a slot can have. -/
def maxData : Nat := 32768
def flagDataComplete : UInt64 := 0x40
def flagLastInSlot : UInt64 := 0xC0

/-- What a shred's headers say. `ok` is false if it is not a shred this code understands. -/
structure Header where
  ok : Bool
  isData : Bool
  slot : UInt64
  index : UInt64
  version : UInt64
  fecSet : UInt64
  proofSize : Nat
  resigned : Bool
  /-- data: how many slots back the parent block is; code: number of data shreds in the set -/
  parentOffset : UInt64
  /-- data: flags; code: number of coding shreds in the set -/
  flags : UInt64
  /-- data: where the data ends in the shred; code: position among the coding shreds -/
  size : UInt64
  deriving Inhabited

def malformed : Header := ⟨false, false, 0, 0, 0, 0, 0, false, 0, 0, 0⟩

/-- Bytes available for data (or erasure code) in a shred with this Merkle path length. -/
def capacity (isData : Bool) (proofSize : Nat) (resigned : Bool) : Nat :=
  let total := if isData then dataPayload else codePayload
  let fixed := (if isData then 88 else 89) + 32 + 20 * proofSize + (if resigned then 64 else 0)
  if fixed > total then 0 else total - fixed

/-- Offset of the previous set's root; the Merkle path follows it. -/
def chainOffset (h : Header) : Nat := (if h.isData then 88 else 89) + capacity h.isData h.proofSize h.resigned

def parse (p : ByteArray) : Header :=
  if p.size < 89 then malformed
  else
    let variant := Wire.u8 p 64
    let kind := variant &&& 0xF0
    -- only the current variants: Merkle shreds that chain to the previous set, optionally re-signed
    if kind != 0x60 && kind != 0x70 && kind != 0x90 && kind != 0xB0 then malformed
    else
      let isData := kind == 0x90 || kind == 0xB0
      let proofSize := (variant &&& 15).toNat
      let resigned := kind == 0x70 || kind == 0xB0
      let h : Header := ⟨true, isData, Wire.u64 p 65, Wire.u32 p 73, Wire.u16 p 77, Wire.u32 p 79, proofSize, resigned,
        Wire.u16 p 83, if isData then Wire.u8 p 85 else Wire.u16 p 85, if isData then Wire.u16 p 86 else Wire.u16 p 87⟩
      if p.size < (if isData then dataPayload else codePayload) || capacity isData proofSize resigned == 0 then malformed
      else if isData && (h.size < 88 || h.size.toNat > 88 + capacity true proofSize resigned || h.index < h.fecSet) then malformed
      else h

def leafPrefix : ByteArray := (ByteArray.empty.push 0) ++ "SOLANA_MERKLE_SHREDS_LEAF".toUTF8
def nodePrefix : ByteArray := (ByteArray.empty.push 1) ++ "SOLANA_MERKLE_SHREDS_NODE".toUTF8

/-- The root of the Merkle tree a shred belongs to, computed from the shred
and the path it carries. This is what the leader signed. -/
def merkleRoot (p : ByteArray) (h : Header) : ByteArray := Id.run do
  let proofAt := chainOffset h + 32
  if !h.ok || proofAt + 20 * h.proofSize > p.size then
    return ByteArray.empty
  -- its position among the 64: data shreds first, then coding shreds
  let mut index := if h.isData then (h.index - h.fecSet).toNat else (h.parentOffset + h.size).toNat
  let mut node := Sha256.hash (leafPrefix ++ p.extract 64 proofAt)
  for i in [0:h.proofSize] do
    let other := p.extract (proofAt + 20 * i) (proofAt + 20 * i + 20)
    node := if index % 2 == 0 then Sha256.hash (nodePrefix ++ node.extract 0 20 ++ other)
      else Sha256.hash (nodePrefix ++ other ++ node.extract 0 20)
    index := index / 2
  if index != 0 then
    return ByteArray.empty
  return node

/-- The root of the previous set, which this shred's set chains to. -/
def chainedRoot (p : ByteArray) (h : Header) : ByteArray := p.extract (chainOffset h) (chainOffset h + 32)

/-- The piece of the block a data shred carries. -/
def data (p : ByteArray) (h : Header) : ByteArray := p.extract 88 h.size.toNat

/-- The part of a shred that is erasure-coded: for a data shred everything
after the signature up to the previous set's root, for a coding shred the
code itself. All 64 shreds of a set have such a piece of the same size. -/
def piece (p : ByteArray) (h : Header) : ByteArray := p.extract (if h.isData then 64 else 89) (chainOffset h)

/-- The Merkle tree over leaf hashes, level after level in one array, as
Solana builds it: nodes are joined in pairs by hashing the first 20 bytes
of each, and a level with an odd number pairs its last node with itself. -/
def tree (leaves : Array ByteArray) : Array ByteArray := Id.run do
  let mut nodes := leaves
  let mut size := leaves.size
  while size > 1 do
    let offset := nodes.size - size
    for k in [0:(size + 1) / 2] do
      let left := nodes[offset + 2 * k]!
      let right := nodes[offset + (if 2 * k + 1 < size then 2 * k + 1 else size - 1)]!
      nodes := nodes.push (Sha256.hash (nodePrefix ++ left.extract 0 20 ++ right.extract 0 20))
    size := (size + 1) / 2
  return nodes

/-- The path from leaf `index` to the root: the 20-byte sibling at each level. -/
def path (nodes : Array ByteArray) (index count : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity 160
  let mut i := index
  let mut size := count
  let mut offset := 0
  while size > 1 do
    let sibling := if (i ^^^ 1) < size then i ^^^ 1 else size - 1
    out := out ++ nodes[offset + sibling]!.extract 0 20
    offset := offset + size
    size := (size + 1) / 2
    i := i / 2
  return out

/-- Rebuilds the missing data shreds of one set of 32 data and 32 coding
shreds from the shreds that did arrive. `data` and `code` hold the set's
shreds by position (empty where missing); at least one coding shred and 32
shreds in all must be present.

A rebuilt shred is exactly as trustworthy as a received one, because the
rebuilt set must hash to the Merkle root the leader signed. The tree has the
32 data shreds under its left half and the 32 coding shreds under its right.
The left half is recomputed from the data shreds, received and rebuilt. The
right half's hash does not need the missing coding shreds: every data
shred's own path ends with it, and if no data shred arrived at all then all
32 coding shreds did. Returns every data shred, byte for byte as the leader
made it, Merkle path included, or an empty array. -/
def recoverSet (data code : Array ByteArray) : Array ByteArray := Id.run do
  let nobody : Array ByteArray := Array.emptyWithCapacity 0
  if data.size != 32 || code.size != 32 then
    return nobody
  let mut model := ByteArray.empty
  for c in code do
    if c.size != 0 && model.size == 0 then
      model := c
  if model.size == 0 then
    return nobody
  let mh := parse model
  if mh.proofSize != 6 then
    return nobody
  let root := merkleRoot model mh
  let chained := chainedRoot model mh
  let mut pieces : Array ByteArray := Array.emptyWithCapacity 64
  let mut codeHalf := ByteArray.empty
  for d in data do
    if d.size == 0 then
      pieces := pieces.push ByteArray.empty
    else
      let h := parse d
      pieces := pieces.push (piece d h)
      -- the last entry of a data shred's path is the hash of the coding half
      let at_ := chainOffset h + 32 + 100
      codeHalf := d.extract at_ (at_ + 20)
  let mut leavesOfCode : Array ByteArray := Array.emptyWithCapacity 32
  for c in code do
    if c.size == 0 then
      pieces := pieces.push ByteArray.empty
    else
      let h := parse c
      pieces := pieces.push (piece c h)
      if codeHalf.size == 0 then
        leavesOfCode := leavesOfCode.push (Sha256.hash (leafPrefix ++ c.extract 64 (chainOffset h + 32)))
  let all := ReedSolomon.reconstruct 32 64 pieces false
  if all.size != 64 then
    return nobody
  if codeHalf.size == 0 then
    if leavesOfCode.size != 32 then
      return nobody
    let nodes := tree leavesOfCode
    codeHalf := nodes[nodes.size - 1]!.extract 0 20
  let mut leaves : Array ByteArray := Array.emptyWithCapacity 32
  for i in [0:32] do
    leaves := leaves.push (Sha256.hash (leafPrefix ++ all[i]! ++ chained))
  let nodes := tree leaves
  if Sha256.hash (nodePrefix ++ nodes[nodes.size - 1]!.extract 0 20 ++ codeHalf) != root then
    return nobody
  let mut out := data
  for i in [0:32] do
    if data[i]!.size == 0 then
      let mut p := model.extract 0 64 ++ all[i]! ++ chained ++ path nodes i 32 ++ codeHalf
      while p.size < dataPayload do
        p := p.push 0
      out := out.set! i p
  return out

end Shred
