import Sys
import Solana.Wire

/-!
# The accounts store

Every account of the chain, on disk, findable by address.

The store is a directory of *shards*; an account belongs to the shard its
address selects, so shards never need to talk to one another and each can
be filled by its own process. A shard is two files:

* `accounts-NN.bin`, a log: accounts appended one after another, each a
  96-byte header and its data. Nothing is rewritten in place; a newer
  version of an account is appended and the old one is simply no longer
  pointed to.
* `index-NN.bin`, a hash table of 16-byte entries: eight bytes of the
  address, and where in the log the account is. Eight bytes are not the
  whole address, so a lookup confirms the address in the log; entries are
  placed by a hash seeded per store, so nobody can choose addresses that
  pile up in one place.

While a shard is being filled the table lives in memory and is written out
at the end.
-/

namespace Accounts

/-- Bytes before an account's data in the log: address 32, owner 32,
lamports 8, rent epoch 8, slot 8, data length 4, flags 1 (bit 0: executable), padding 3. -/
def headerSize : Nat := 96

/-- "Not in the store". -/
def none_ : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- Which of `shards` shards an address belongs to. (The index uses the address's first eight bytes; this uses the next two.) -/
def shardOf (b : ByteArray) (o shards : Nat) : Nat :=
  (b[o + 8]!.toNat + 256 * b[o + 9]!.toNat) % shards

/-- An account as the log holds it: header then data, padded to a multiple of 8. -/
def record (b : ByteArray) (pubkey owner : Nat) (lamports rentEpoch slot : UInt64) (executable : Bool) (data dataLen : Nat) : ByteArray := Id.run do
  let mut r := ByteArray.emptyWithCapacity (headerSize + dataLen + 8)
  r := b.copySlice pubkey r 0 32
  r := b.copySlice owner r 32 32
  r := Wire.putU64 (Wire.putU64 (Wire.putU64 r lamports) rentEpoch) slot
  r := Wire.putU32 r dataLen.toUInt64
  r := r.push (if executable then 1 else 0)
  r := (r.push 0).push 0
  r := r.push 0
  r := b.copySlice data r headerSize dataLen
  while r.size % 8 != 0 do
    r := r.push 0
  return r

def recLamports (r : ByteArray) : UInt64 := Wire.u64 r 64
def recRentEpoch (r : ByteArray) : UInt64 := Wire.u64 r 72
def recSlot (r : ByteArray) : UInt64 := Wire.u64 r 80
def recDataLen (r : ByteArray) : Nat := (Wire.u32 r 88).toNat
def recExecutable (r : ByteArray) : Bool := Wire.u8 r 92 &&& 1 == 1

structure Shard where
  /-- the index: address of the table, and its size as a power of two -/
  table : UInt64
  bits : Nat
  used : Nat
  seed : UInt64
  /-- the log: its file, and how much of it is on disk -/
  fd : UInt64
  flushed : UInt64
  /-- set when the disk refused a write or memory ran out -/
  failed : Bool

-- While a shard is being filled, the end of its log is still in memory:
-- the functions below that read the log take those `pending` bytes too. The
-- caller owns them (and appends to them in place), which is why they are not
-- a field of the shard.

namespace Shard

def path (dir : String) (kind : String) (id : Nat) : String :=
  s!"{dir}/{kind}-{if id < 10 then "0" else ""}{id}.bin"

/-- Where in a table of `2 ^ bits` entries a key's search starts. -/
@[inline] def home (seed key : UInt64) (bits : Nat) : UInt64 :=
  ((key ^^^ seed) * 0x9E3779B97F4A7C15) >>> (64 - bits).toUInt64

/-- The eight bytes of an address the index keeps (never zero: zero marks an empty entry). -/
@[inline] def keyOf (b : ByteArray) (o : Nat) : UInt64 :=
  let k := Wire.u64 b o
  if k == 0 then 1 else k

/-- A new, empty shard to be filled. -/
def create (dir : String) (id : Nat) (seed : UInt64) : IO Shard := do
  -- (read as well as written: an address seen again is checked against the log)
  let fd ← Sys.openFile (path dir "accounts" id) 0x242
  let bits := 12
  let table ← Sys.mapMemory (16 <<< bits.toUInt64)
  return ⟨table, bits, 0, seed, fd, 0, Sys.isErr fd || table == 0⟩

/-- Writes the pending bytes to the log. The caller then starts a new, empty run of pending bytes. -/
def flush (s : Shard) (pending : ByteArray) : IO Shard := do
  if pending.size == 0 then
    return s
  let ok ← Sys.writeFully s.fd pending
  return { s with flushed := s.flushed + pending.size.toUInt64, failed := s.failed || !ok }

/-- `len` bytes of the log at `loc`, whether they are on disk yet or not. -/
def bytesAt (s : Shard) (pending : ByteArray) (loc : UInt64) (len : Nat) : IO ByteArray := do
  if loc >= s.flushed then
    let o := (loc - s.flushed).toNat
    return pending.extract o (o + len)
  Sys.readAt s.fd loc len

/-- The whole record at `loc`; shorter than a record if the log cannot be read. -/
def recordAt (s : Shard) (pending : ByteArray) (loc : UInt64) : IO ByteArray := do
  let head ← s.bytesAt pending loc headerSize
  if head.size < headerSize then
    return ByteArray.empty
  let dataLen := recDataLen head
  if dataLen == 0 then
    return head
  return head ++ (← s.bytesAt pending (loc + headerSize.toUInt64) dataLen)

/-- Looks an address up. Returns the address of its index entry (or of the
empty entry where it would go) and where its record is (`none_` if it has
none). An entry address of 0 means the log could not be read. -/
def locate (s : Shard) (pending : ByteArray) (b : ByteArray) (o : Nat) : IO (UInt64 × UInt64) := do
  let key := keyOf b o
  let mask := ((1 : UInt64) <<< s.bits.toUInt64) - 1
  let mut i := home s.seed key s.bits
  repeat
    let entry := s.table + 16 * i
    let k ← Mem.load64 entry
    if k == 0 then
      return (entry, none_)
    if k == key then
      -- the same eight bytes: the log says whether it is the same address
      let loc ← Mem.load64 (entry + 8)
      let head ← s.bytesAt pending loc 32
      if head.size != 32 then
        return (0, none_)
      if Wire.eqAt head 0 b o 32 then
        return (entry, loc)
    i := (i + 1) &&& mask
  return (0, none_)

/-- Doubles the table. -/
def grow (s : Shard) : IO Shard := do
  let bits := s.bits + 1
  let table ← Sys.mapMemory (16 <<< bits.toUInt64)
  if table == 0 then
    return { s with failed := true }
  let mask := ((1 : UInt64) <<< bits.toUInt64) - 1
  for i in [0:1 <<< s.bits] do
    let entry := s.table + 16 * i.toUInt64
    let k ← Mem.load64 entry
    if k != 0 then
      let mut j := home s.seed k bits
      let mut taken ← Mem.load64 (table + 16 * j)
      while taken != 0 do
        j := (j + 1) &&& mask
        taken ← Mem.load64 (table + 16 * j)
      Mem.store64 (table + 16 * j) k
      Mem.store64 (table + 16 * j + 8) (← Mem.load64 (entry + 8))
  Sys.unmap s.table (16 <<< s.bits.toUInt64)
  return { s with table := table, bits := bits }

/-- Points an index entry at the record at `loc` of the log. `entry` must
come from `locate` for that record's address (whose first eight bytes are
`key`), with no change to the index in between; `fresh` says the address
had no entry. -/
def point (s : Shard) (entry : UInt64) (fresh : Bool) (key loc : UInt64) : IO Shard := do
  Mem.store64 (entry + 8) loc
  if !fresh then
    return s
  Mem.store64 entry key
  let next := { s with used := s.used + 1 }
  -- keep the table at most five eighths full
  if next.used * 8 > (5 <<< next.bits) then
    return ← next.grow
  return next

/-- Finishes filling: writes the rest of the log, and the index. -/
def close (s : Shard) (pending : ByteArray) (dir : String) (id : Nat) : IO Shard := do
  let done ← s.flush pending
  Sys.close done.fd
  let fd ← Sys.openFile (path dir "index" id) 0x241
  let ok ← Sys.writeFrom fd s.table (16 <<< s.bits.toUInt64)
  Sys.close fd
  return { done with failed := done.failed || Sys.isErr fd || !ok }

/-- Opens a filled shard for reading (there are no pending bytes then). -/
def openRead (dir : String) (id : Nat) (seed : UInt64) : IO Shard := do
  let fd ← Sys.openFile (path dir "accounts" id) 0
  let ifd ← Sys.openFile (path dir "index" id) 0
  if Sys.isErr fd || Sys.isErr ifd then
    return ⟨0, 0, 0, seed, 0, 0, true⟩
  let size ← Sys.fileSize ifd
  let table ← Sys.mapFile ifd size
  Sys.close ifd
  let mut bits := 0
  while (16 : UInt64) <<< bits.toUInt64 < size do
    bits := bits + 1
  let length ← Sys.fileSize fd
  return ⟨table, bits, 0, seed, fd, length, table == 0 || (16 : UInt64) <<< bits.toUInt64 != size⟩

end Shard

end Accounts
