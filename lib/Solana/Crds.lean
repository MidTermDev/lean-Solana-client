import Solana.Wire

/-!
# CRDS: the records Solana nodes gossip

The cluster's shared state is a "cluster replicated data store": a set of
signed records (`CrdsValue = signature ++ CrdsData`), each owned by the node
whose key signed it. This file knows the wire layout of every record type
well enough to find where each record ends and who signed it, and decodes
the two types the client actually uses: `ContactInfo` and `SnapshotHashes`.

Record boundaries matter because the format is not self-delimiting: a
packet carries several records back to back, and each one's signature
covers exactly its own bytes. Layouts follow agave's `gossip/src/crds_data.rs`.
-/

namespace Crds

open Wire

/-- CrdsData variant numbers. -/
def kindLegacyContactInfo : Nat := 0
def kindVote : Nat := 1
def kindLowestSlot : Nat := 2
def kindEpochSlots : Nat := 5
def kindDuplicateShred : Nat := 9
def kindSnapshotHashes : Nat := 10
def kindContactInfo : Nat := 11
def kindCount : Nat := 14

def kindName (k : Nat) : String :=
  if k == 0 then "LegacyContactInfo"
  else if k == 1 then "Vote"
  else if k == 2 then "LowestSlot"
  else if k == 3 then "LegacySnapshotHashes"
  else if k == 4 then "AccountsHashes"
  else if k == 5 then "EpochSlots"
  else if k == 6 then "LegacyVersion"
  else if k == 7 then "Version"
  else if k == 8 then "NodeInstance"
  else if k == 9 then "DuplicateShred"
  else if k == 10 then "SnapshotHashes"
  else if k == 11 then "ContactInfo"
  else if k == 12 then "RestartLastVotedForkSlots"
  else if k == 13 then "RestartHeaviestFork"
  else "Unknown"

/-- bincode `SocketAddr`: u32 tag, then 4 + 2 bytes (IPv4) or 16 + 2 bytes (IPv6). -/
def skipSockAddr (b : ByteArray) (o : Nat) : Nat :=
  let tag := u32 b o
  if tag == 0 then adv b o 10
  else if tag == 1 then adv b o 22
  else bad

/-- `BitVec<u8>`: optional byte buffer, then the bit length. -/
def skipBitVec (b : ByteArray) (o : Nat) : Nat :=
  let tag := u8 b o
  let o := adv b o 1
  let o := if tag == 1 then skipVec b o 1 else o
  adv b o 8

/-- A legacy transaction (votes are the only transactions gossip carries). -/
def skipTransaction (b : ByteArray) (o : Nat) : Nat := Id.run do
  let o := skipShortVec b o 64
  let o := adv b o 3
  let o := skipShortVec b o 32
  let o := adv b o 32
  let n := varint b o
  let mut q := skipVarint b o
  if n > 64 then
    return bad
  for _ in [0:n.toNat] do
    q := adv b q 1
    q := skipShortVec b q 1
    q := skipShortVec b q 1
  return q

/-- A decoded `ContactInfo`: who a node is, what it runs, where its gossip port is. -/
structure Contact where
  stop : Nat
  wallclock : UInt64
  shredVersion : UInt64
  major : UInt64
  minor : UInt64
  patch : UInt64
  client : UInt64
  gossipIp : UInt32
  gossipPort : UInt16
  /-- where it answers requests for shreds it has (`ip <<< 16 ||| port`, or 0) -/
  repair : UInt64
  /-- where it receives shreds (`ip <<< 16 ||| port`, or 0) -/
  tvu : UInt64
  deriving Inhabited

/-- Decodes the `ContactInfo` whose public key starts at `p`. `stop` is
`Wire.bad` when the record is malformed. -/
def parseContact (b : ByteArray) (p : Nat) : Contact := Id.run do
  let o := adv b p 32
  let wallclock := varint b o
  let o := skipVarint b o
  let o := adv b o 8
  let shred := u16 b o
  let o := adv b o 2
  let major := varint b o
  let o := skipVarint b o
  -- the top two bits of `minor` carry the prerelease tag
  let minor := varint b o &&& 0x3fff
  let o := skipVarint b o
  let patch := varint b o
  let o := skipVarint b o
  let o := adv b o 8
  let client := varint b o
  let o := skipVarint b o
  -- addresses
  let naddrs := varint b o
  let mut q := skipVarint b o
  if naddrs > 16 then
    q := bad
  let mut ips : Array UInt32 := Array.emptyWithCapacity 4
  for _ in [0:naddrs.toNat] do
    let tag := u32 b q
    if tag == 0 then
      ips := ips.push ((u8 b (q + 4) <<< 24) ||| (u8 b (q + 5) <<< 16) ||| (u8 b (q + 6) <<< 8) ||| u8 b (q + 7)).toUInt32
      q := adv b q 8
    else if tag == 1 then
      ips := ips.push 0
      q := adv b q 20
    else
      q := bad
  -- sockets: (key, address index, port offset from the previous entry)
  let nsock := varint b q
  q := skipVarint b q
  if nsock > 32 then
    q := bad
  let mut port : UInt64 := 0
  let mut gossipIp : UInt32 := 0
  let mut gossipPort : UInt16 := 0
  let mut repair : UInt64 := 0
  let mut tvu : UInt64 := 0
  for _ in [0:nsock.toNat] do
    let key := u8 b q
    let idx := (u8 b (q + 1)).toNat
    q := adv b q 2
    port := (port + varint b q) &&& 0xffff
    q := skipVarint b q
    if key == 0 && idx < ips.size && ok q then
      gossipIp := ips[idx]!
      gossipPort := port.toUInt16
    -- socket 4 serves repair requests, socket 10 receives shreds (both UDP)
    if key == 4 && idx < ips.size && ok q then
      repair := (ips[idx]!.toUInt64 <<< 16) ||| port
    if key == 10 && idx < ips.size && ok q then
      tvu := (ips[idx]!.toUInt64 <<< 16) ||| port
  -- extensions: (type, length, bytes)
  let next := varint b q
  q := skipVarint b q
  if next > 32 then
    q := bad
  for _ in [0:next.toNat] do
    q := adv b q 1
    let len := varint b q
    q := skipVarint b q
    q := skipN b q len 1
  return ⟨q, wallclock, shred, major, minor, patch, client, gossipIp, gossipPort, repair, tvu⟩

/-- Offset one past the record of the given kind whose body starts at `p`. -/
def stopOf (b : ByteArray) (kind p : Nat) : Nat := Id.run do
  if kind == 0 then
    -- LegacyContactInfo: key, ten socket addresses, wallclock, shred version
    let mut o := adv b p 32
    for _ in [0:10] do
      o := skipSockAddr b o
    return adv b o 10
  if kind == 1 then
    -- Vote: index, from, transaction, wallclock
    return adv b (skipTransaction b (adv b p 33)) 8
  if kind == 2 then
    -- LowestSlot: index, from, root, lowest, slots, stash, wallclock
    let o := skipVec b (adv b p 49) 8
    let n := u64 b o
    let mut q := adv b o 8
    if n > 16 then
      return bad
    for _ in [0:n.toNat] do
      q := skipVec b (adv b q 12) 1
    return adv b q 8
  if kind == 3 || kind == 4 then
    -- (Legacy)SnapshotHashes / AccountsHashes: from, [(slot, hash)], wallclock
    return adv b (skipVec b (adv b p 32) 40) 8
  if kind == 5 then
    -- EpochSlots: index, from, [compressed slots], wallclock
    let o := adv b p 33
    let n := u64 b o
    let mut q := adv b o 8
    if n > 64 then
      return bad
    for _ in [0:n.toNat] do
      let tag := u32 b q
      q := adv b q 20
      if tag == 0 then
        q := skipVec b q 1
      else if tag == 1 then
        q := skipBitVec b q
      else
        return bad
    return adv b q 8
  if kind == 6 || kind == 7 then
    -- (Legacy)Version: from, wallclock, 3 x u16, Option<u32> commit [, feature set]
    let o := adv b p 46
    let o := if u8 b o == 1 then adv b o 5 else adv b o 1
    return (if kind == 7 then adv b o 4 else o)
  if kind == 8 then
    -- NodeInstance: from, wallclock, timestamp, token
    return adv b p 56
  if kind == 9 then
    -- DuplicateShred: index, from, wallclock, slot, 4 + 3 bytes of header, chunk
    return skipVec b (adv b p 57) 1
  if kind == 10 then
    -- SnapshotHashes: from, full (slot, hash), [incremental (slot, hash)], wallclock
    return adv b (skipVec b (adv b p 72) 40) 8
  if kind == 11 then
    return (parseContact b p).stop
  if kind == 12 then
    -- RestartLastVotedForkSlots: from, wallclock, offsets, last slot, hash, shred version
    let o := adv b p 40
    let tag := u32 b o
    let o := adv b o 4
    if tag == 1 then
      return adv b (skipBitVec b o) 42
    if tag != 0 then
      return bad
    let n := u64 b o
    let mut q := adv b o 8
    if n > 65536 then
      return bad
    for _ in [0:n.toNat] do
      q := skipVarint b q
    return adv b q 42
  if kind == 13 then
    -- RestartHeaviestFork: from, wallclock, slot, hash, stake, shred version
    return adv b p 90
  return bad

/-- Where a record is and who owns it. -/
structure Info where
  kind : Nat
  origin : Nat
  body : Nat
  stop : Nat

/-- Locates the record whose `CrdsData` starts at `o` (just after its signature).
`origin` is the offset of the 32-byte key that must have signed `[o, stop)`. -/
def scan (b : ByteArray) (o : Nat) : Info :=
  let kind := (u32 b o).toNat
  let p := adv b o 4
  if !(ok p) || kind >= 14 then ⟨kind, 0, 0, bad⟩
  else
    let stop := stopOf b kind p
    -- Vote, LowestSlot and EpochSlots put a one-byte index before the key,
    -- DuplicateShred a two-byte one
    let origin := if kind == 1 || kind == 2 || kind == 5 then p + 1 else if kind == 9 then p + 2 else p
    ⟨kind, origin, p, stop⟩

/-- The newest slot a `SnapshotHashes` record (body at `p`) vouches for. -/
def snapshotSlot (b : ByteArray) (p : Nat) : UInt64 := Id.run do
  let mut best := u64 b (p + 32)
  let n := u64 b (p + 72)
  if n > 64 then
    return best
  for i in [0:n.toNat] do
    let s := u64 b (p + 80 + 40 * i)
    if s > best then
      best := s
  return best

/-- Human-readable name for the client id in a node's version. -/
def clientName (id : UInt64) : String :=
  if id == 0 then "SolanaLabs"
  else if id == 1 then "Jito"
  else if id == 2 then "Frankendancer"
  else if id == 3 then "Agave"
  else if id == 4 then "AgavePaladin"
  else if id == 5 then "Firedancer"
  else if id == 6 then "AgaveBam"
  else if id == 7 then "Sig"
  else if id == 8 then "Rakurai"
  else if id == 9 then "HarmonicFiredancer"
  else if id == 10 then "HarmonicAgave"
  else if id == 11 then "HarmonicFrankendancer"
  else if id == 12 then "FireBAM"
  else if id == 13 then "Raiku"
  else "other"

end Crds
