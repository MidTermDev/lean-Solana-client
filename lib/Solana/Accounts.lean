import Fast
import Sys
import Solana.Wire

/-!
# The accounts store

Every account of the chain, on disk, findable by address.

The store is a directory of *shards*; an account belongs to the shard its
address selects, so shards never need to talk to one another and each can
be filled by its own process. A shard is two files:

* `accounts-NN.bin`, a log: accounts appended one after another, each an
  88-byte header and its data, the data's runs of zeros written as counts.
  Nothing is rewritten in place; a newer
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

/-- Bytes at the start of every record in the log: address 32, owner 32,
lamports 8, slot 8, a word holding the data's length (24 bits) and flags
(8 bits), and the length of the data as stored. After them comes the rent
epoch, if the record has one, and then the data. -/
def headerSize : Nat := 88

-- flags: bit 0, the account is executable; bit 1, a rent epoch follows the
-- header (almost every account's is "never", which is not stored); bit 2,
-- the data is stored with its runs of zeros written as counts.

/-- "Not in the store". -/
def none_ : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- The rent epoch of an account that owes no rent, ever: all but a few. -/
def noRent : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- Which of `shards` shards an address belongs to. (The index uses the address's first eight bytes; this uses the next two.) -/
def shardOf (b : ByteArray) (o shards : Nat) : Nat :=
  (b[o + 8]!.toNat + 256 * b[o + 9]!.toNat) % shards

/-- Appends `b[o, o + len)` to `out` with its runs of zeros written as
counts. Account data is mostly zeros (a token account is 165 bytes, more
than half of them zero), so this is most of what makes the store fit a disk.

The coding: a byte below 128 says that many bytes plus one follow as they
are; a byte of 128 or more says that many minus 127 zeros stand here. -/
def packZeros (b : ByteArray) (o len : Nat) (out0 : ByteArray) : ByteArray := Id.run do
  let stop := o + len
  let mut out := out0
  let mut i := o
  -- bytes from `kept` to `i` are waiting to be written as they are
  let mut kept := o
  while i < stop do
    if b[i]! != 0 then
      -- (eight bytes with no zero among them are passed over at once: a word minus 0x0101..., and not
      -- the word, has a top bit set exactly where a byte was zero, or was reached by a borrow from one)
      let word := Fast.le64 b i
      if i + 8 <= stop && (word - 0x0101010101010101) &&& (~~~word) &&& 0x8080808080808080 == 0 then
        i := i + 8
      else
        i := i + 1
    else
      let mut j := i + 1
      -- (and eight zero bytes at once)
      while j + 8 <= stop && Fast.le64 b j == 0 do
        j := j + 8
      while j < stop && b[j]! == 0 do
        j := j + 1
      -- a run of one or two zeros costs less left among its neighbours
      if j - i >= 3 then
        while kept < i do
          let n := if i - kept > 128 then 128 else i - kept
          out := out.push (n - 1).toUInt8
          out := b.copySlice kept out out.size n
          kept := kept + n
        let mut zeros := j - i
        while zeros > 0 do
          let n := if zeros > 128 then 128 else zeros
          out := out.push (127 + n).toUInt8
          zeros := zeros - n
        kept := j
      i := j
  while kept < stop do
    let n := if stop - kept > 128 then 128 else stop - kept
    out := out.push (n - 1).toUInt8
    out := b.copySlice kept out out.size n
    kept := kept + n
  return out

/-- Undoes `packZeros` on `b[o, o + len)`. The result has `size` bytes if the input was well formed (and not otherwise). -/
def zeroRun : ByteArray := Id.run do
  let mut z := ByteArray.emptyWithCapacity 128
  for _ in [0:128] do
    z := z.push 0
  return z

def unpackZeros (b : ByteArray) (o len size : Nat) : ByteArray := Id.run do
  let stop := o + len
  let mut out := ByteArray.emptyWithCapacity (size + 8)
  let mut i := o
  while i < stop do
    let c := b[i]!.toNat
    if c < 128 then
      if i + 2 + c > stop || out.size + c + 1 > size then
        return ByteArray.empty
      out := b.copySlice (i + 1) out out.size (c + 1)
      i := i + 2 + c
    else
      if out.size + (c - 127) > size then
        return ByteArray.empty
      out := zeroRun.copySlice 0 out out.size (c - 127)
      i := i + 1
  return out

/-- An account as the log holds it. `pubkey`, `owner` and `data` are offsets into `b`. -/
def record (b : ByteArray) (pubkey owner : Nat) (lamports rentEpoch slot : UInt64) (executable : Bool) (data dataLen : Nat) : ByteArray := Id.run do
  let mut r := ByteArray.emptyWithCapacity (headerSize + 16 + dataLen + dataLen / 64)
  r := b.copySlice pubkey r 0 32
  r := b.copySlice owner r 32 32
  r := Wire.putU64 (Wire.putU64 r lamports) slot
  -- the two words that depend on how the data packs are filled in afterwards
  r := Wire.putU64 r 0
  if rentEpoch != noRent then
    r := Wire.putU64 r rentEpoch
  let body := r.size
  r := packZeros b data dataLen r
  let mut flags := (if executable then 1 else 0) + (if rentEpoch != noRent then 2 else 0) + 4
  if r.size - body >= dataLen then
    -- nothing gained: the data as it is
    r := r.extract 0 body
    r := b.copySlice data r body dataLen
    flags := flags - 4
  let stored := r.size - body
  r := r.set! 80 dataLen.toUInt8
  r := r.set! 81 (dataLen >>> 8).toUInt8
  r := r.set! 82 (dataLen >>> 16).toUInt8
  r := r.set! 83 flags.toUInt8
  r := r.set! 84 stored.toUInt8
  r := r.set! 85 (stored >>> 8).toUInt8
  r := r.set! 86 (stored >>> 16).toUInt8
  r := r.set! 87 (stored >>> 24).toUInt8
  return r

def recLamports (r : ByteArray) : UInt64 := Wire.u64 r 64
def recSlot (r : ByteArray) : UInt64 := Wire.u64 r 72
def recDataLen (r : ByteArray) : Nat := (Wire.u32 r 80 &&& 0xFFFFFF).toNat
def recFlags (r : ByteArray) : UInt64 := Wire.u8 r 83
def recExecutable (r : ByteArray) : Bool := recFlags r &&& 1 == 1
/-- Bytes of a record after its 88-byte header: the rent epoch if present, and the data as stored. -/
def recRest (r : ByteArray) : Nat := (if recFlags r &&& 2 != 0 then 8 else 0) + (Wire.u32 r 84).toNat
def recRentEpoch (r : ByteArray) : UInt64 := if recFlags r &&& 2 != 0 then Wire.u64 r headerSize else noRent
/-- The account's data. Shorter than `recDataLen` only if the record is damaged. -/
def recData (r : ByteArray) : ByteArray :=
  let body := headerSize + (if recFlags r &&& 2 != 0 then 8 else 0)
  let stored := (Wire.u32 r 84).toNat
  if recFlags r &&& 4 != 0 then unpackZeros r body stored (recDataLen r) else r.extract body (body + stored)

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
  deriving Inhabited

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

/-- The whole record at `loc`; empty if the log cannot be read. -/
def recordAt (s : Shard) (pending : ByteArray) (loc : UInt64) : IO ByteArray := do
  let head ← s.bytesAt pending loc headerSize
  if head.size < headerSize then
    return ByteArray.empty
  let rest := recRest head
  if rest == 0 then
    return head
  let tail ← s.bytesAt pending (loc + headerSize.toUInt64) rest
  if tail.size != rest then
    return ByteArray.empty
  return head ++ tail

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
