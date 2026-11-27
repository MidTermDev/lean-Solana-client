import Fast

/-!
# Bounds-checked wire reading and writing

Everything a gossip node parses arrives from strangers on the internet, so
nothing here may index out of bounds or overflow. Readers take a buffer and
an offset and never fail loudly: reads past the end yield zero, and every
"advance" goes through `adv`, which returns the sentinel `bad` once a
message turns out to be truncated. A parse is valid iff its final offset is
`ok`. Lengths taken from the wire are compared against the buffer size
*before* any arithmetic is done with them.
-/

namespace Wire

/-- The "this parse failed" offset. Sticky: advancing from `bad` stays `bad`. -/
def bad : Nat := 0x4000000000000000

def ok (o : Nat) : Bool := o < bad

/-- Advances `o` by `n` bytes if the buffer has them. -/
def adv (b : ByteArray) (o n : Nat) : Nat :=
  if o >= bad || n > b.size then bad
  else if o + n <= b.size then o + n
  else bad

@[inline] def u8 (b : ByteArray) (o : Nat) : UInt64 :=
  if o < b.size then b[o]!.toUInt64 else 0

-- Little-endian numbers; bytes past the end read as zero. (`Fast`: one instruction each when compiled.)
@[inline] def u16 (b : ByteArray) (o : Nat) : UInt64 := Fast.le16 b o

@[inline] def u32 (b : ByteArray) (o : Nat) : UInt64 := Fast.le32 b o

@[inline] def u64 (b : ByteArray) (o : Nat) : UInt64 := Fast.le64 b o

/-- Length in bytes of the LEB128 varint at `o`, or 0 if it is truncated or too long. -/
def varintLen (b : ByteArray) (o : Nat) : Nat := Id.run do
  if o >= bad then
    return 0
  for i in [0:10] do
    if o + i >= b.size then
      return 0
    if b[o + i]! &&& 0x80 == 0 then
      return i + 1
  return 0

/-- Value of the LEB128 varint at `o` (also Solana's "short vec" length prefix). -/
def varint (b : ByteArray) (o : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  if o >= bad then
    return 0
  for i in [0:10] do
    if o + i >= b.size then
      return v
    let x := b[o + i]!
    v := v ||| ((x &&& 0x7f).toUInt64 <<< (7 * i).toUInt64)
    if x &&& 0x80 == 0 then
      return v
  return v

def skipVarint (b : ByteArray) (o : Nat) : Nat :=
  let n := varintLen b o
  if n == 0 then bad else adv b o n

/-- Skips `count` elements of `elemSize` bytes; `count` comes from the wire. -/
def skipN (b : ByteArray) (o : Nat) (count : UInt64) (elemSize : Nat) : Nat :=
  if o >= bad || count > b.size.toUInt64 then bad
  else adv b o (count.toNat * elemSize)

/-- Skips a bincode `Vec<T>` of fixed-size elements: u64 count, then the elements. -/
def skipVec (b : ByteArray) (o : Nat) (elemSize : Nat) : Nat :=
  skipN b (adv b o 8) (u64 b o) elemSize

/-- Skips a "short vec" of fixed-size elements: varint count, then the elements. -/
def skipShortVec (b : ByteArray) (o : Nat) (elemSize : Nat) : Nat :=
  skipN b (skipVarint b o) (varint b o) elemSize

-- ------------------------------------------------------------------ writers

@[inline] def putU16 (b : ByteArray) (v : UInt64) : ByteArray := Fast.push16 b v

@[inline] def putU32 (b : ByteArray) (v : UInt64) : ByteArray := Fast.push32 b v

@[inline] def putU64 (b : ByteArray) (v : UInt64) : ByteArray := Fast.push64 b v

def putVarint (b : ByteArray) (v : UInt64) : ByteArray := Id.run do
  let mut out := b
  let mut x := v
  while x >= 0x80 do
    out := out.push (x.toUInt8 ||| 0x80)
    x := x >>> 7
  return out.push x.toUInt8

/-- True when `b[o .. o + n)` equals `c[p .. p + n)`. -/
def eqAt (b : ByteArray) (o : Nat) (c : ByteArray) (p n : Nat) : Bool := Id.run do
  if o + n > b.size || p + n > c.size then
    return false
  for i in [0:n] do
    if b[o + i]! != c[p + i]! then
      return false
  return true

end Wire
