import Solana.Wire

/-!
# Tar archives

An archive is a sequence of 512-byte blocks: for each file a header block,
then the file's bytes padded to a whole number of blocks; two blocks of
zeros end it. This reads headers; the caller walks the stream.

A snapshot's account files can exceed the 8 GiB that eleven octal digits can
express, so the size is also read in GNU's binary form.
-/

namespace Tar

structure Header where
  /-- 0 = not a valid header, 1 = a file, 2 = something to skip (a directory, a link, an extension record), 3 = the end of the archive -/
  kind : Nat
  name : String
  size : Nat
  deriving Inhabited

def invalid : Header := ⟨0, "", 0⟩

/-- An octal number in a field of `n` bytes, ended by a space or a zero byte. -/
def octal (b : ByteArray) (o n : Nat) : Nat := Id.run do
  let mut v := 0
  for i in [0:n] do
    let c := b[o + i]!
    if c >= 48 && c <= 55 then
      v := v * 8 + (c.toNat - 48)
    else if c != 32 || v != 0 then
      return v
  return v

/-- A size field: octal, or, if its first byte has the top bit set, a big-endian binary number. -/
def number (b : ByteArray) (o n : Nat) : Nat := Id.run do
  if b[o]! &&& 0x80 == 0 then
    return octal b o n
  let mut v := (b[o]! &&& 0x7F).toNat
  for i in [1:n] do
    v := v * 256 + b[o + i]!.toNat
  return v

/-- The text in a field of at most `n` bytes, up to the first zero byte. -/
def text (b : ByteArray) (o n : Nat) : String := Id.run do
  let mut stop := o
  while stop < o + n && b[stop]! != 0 do
    stop := stop + 1
  return String.fromUTF8! (b.extract o stop)

/-- Reads the header block at `o`; the block must be there (`o + 512 ≤ b.size`). -/
def header (b : ByteArray) (o : Nat) : Header := Id.run do
  if o + 512 > b.size then
    return invalid
  -- the checksum is the sum of the block's bytes with the checksum field itself read as spaces
  let mut sum := 0
  let mut zero := true
  for i in [0:512] do
    let c := b[o + i]!
    if c != 0 then
      zero := false
    sum := sum + (if i >= 148 && i < 156 then 32 else c.toNat)
  if zero then
    return ⟨3, "", 0⟩
  if octal b (o + 148) 8 != sum then
    return invalid
  let size := number b (o + 124) 12
  let kind := b[o + 156]!
  let short := text b o 100
  -- the "ustar" format keeps the front of a long path in a second field
  let front := if Wire.eqAt b (o + 257) "ustar".toUTF8 0 5 && b[o + 345]! != 0 && b[o + 263]! == 48 then text b (o + 345) 155 ++ "/" else ""
  if kind == 48 || kind == 0 then
    return ⟨1, front ++ short, size⟩
  -- directories and links carry no bytes; everything else (long names, extended attributes) is skipped with its content
  return ⟨2, front ++ short, if kind >= 49 && kind <= 54 then 0 else size⟩

/-- How many bytes a file of `size` bytes takes in the archive after its header. -/
def padded (size : Nat) : Nat := (size + 511) / 512 * 512

end Tar
