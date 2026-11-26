import Crypto.Sha256
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

end Shred
