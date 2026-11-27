/-! # What the compiler does in one instruction

Everything in this file is defined in plain Lean, and that definition is
what each function *means*: it is what the official toolchain runs, and
what the tests hold `leanc` to. `leanc` does not compile these bodies. It
knows the functions by name and puts a few machine instructions in the
place of each call:

* reading and writing numbers of 2, 4 and 8 bytes in a byte array (one
  `mov`, where the Lean reads or writes a byte at a time);
* the high half of a 64 × 64-bit product (one `mul`);
* **vector instructions** (AVX-512): a byte array is treated as a file of
  64-byte registers, and `add32 f 3 1 2` adds registers 1 and 2 into
  register 3, sixteen 32-bit numbers at once, in place. The register
  numbers must be written out as literals (after inlining), because they
  become the instruction's addresses.

Not every processor has the vector instructions. `wide` says whether this
one does; code asks it once and takes a portable path otherwise. Under the
official toolchain `wide` is simply true: the definitions below can do
everything. For the same reason each vector operation has a twin under
`Fast.Ref` that `leanc` compiles as ordinary Lean, so that a test can print
the same thing on any machine. -/

namespace Fast

@[inline] def byte (b : ByteArray) (o : Nat) : UInt64 := if o < b.size then b[o]!.toUInt64 else 0

/-- Two bytes at `o`, least significant first; bytes past the end count as zero. -/
def le16 (b : ByteArray) (o : Nat) : UInt64 := byte b o ||| (byte b (o + 1) <<< 8)

/-- Four bytes at `o`, least significant first; bytes past the end count as zero. -/
def le32 (b : ByteArray) (o : Nat) : UInt64 :=
  byte b o ||| (byte b (o + 1) <<< 8) ||| (byte b (o + 2) <<< 16) ||| (byte b (o + 3) <<< 24)

/-- Eight bytes at `o`, least significant first; bytes past the end count as zero. -/
def le64 (b : ByteArray) (o : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for i in [0:8] do
    v := v ||| (byte b (o + i) <<< (8 * i).toUInt64)
  return v

/-- Writes the low two bytes of `v` at `o` (which must be inside the array). -/
def put16 (b : ByteArray) (o : Nat) (v : UInt64) : ByteArray :=
  (b.set! o v.toUInt8).set! (o + 1) (v >>> 8).toUInt8

/-- Writes the low four bytes of `v` at `o`. -/
def put32 (b : ByteArray) (o : Nat) (v : UInt64) : ByteArray := Id.run do
  let mut out := b
  for i in [0:4] do
    out := out.set! (o + i) (v >>> (8 * i).toUInt64).toUInt8
  return out

/-- Writes `v` at `o`, eight bytes. -/
def put64 (b : ByteArray) (o : Nat) (v : UInt64) : ByteArray := Id.run do
  let mut out := b
  for i in [0:8] do
    out := out.set! (o + i) (v >>> (8 * i).toUInt64).toUInt8
  return out

/-- 1 for true, 0 for false, without a branch: a comparison leaves its answer in a register, and this is
that register. (Sums of many words carry or do not at the whim of the data; a branch on each carry is
guessed wrong half the time.) -/
def bit (b : Bool) : UInt64 := if b then 1 else 0

/-- The high 64 bits of the 128-bit product `a × b`. -/
def mulHi (a b : UInt64) : UInt64 :=
  let al := a &&& 0xFFFFFFFF
  let ah := a >>> 32
  let bl := b &&& 0xFFFFFFFF
  let bh := b >>> 32
  let mid := ((al * bl) >>> 32) + ((al * bh) &&& 0xFFFFFFFF) + ((ah * bl) &&& 0xFFFFFFFF)
  ah * bh + ((al * bh) >>> 32) + ((ah * bl) >>> 32) + (mid >>> 32)

/-- What the processor can do, as it reports it (CPUID leaf 7: `ebx` in the low half, `ecx` in the high
half), with the AVX-512 bits cleared if the operating system does not keep the wide registers. -/
def cpuBits : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- AVX-512 with its byte, word, doubleword and quadword instructions at every width. -/
def wide : Bool := cpuBits &&& 0xC0030000 == 0xC0030000

/-- 52-bit multiply-and-add on eight lanes (AVX-512 IFMA). -/
def ifma : Bool := wide && cpuBits &&& 0x200000 != 0

/-- Is this machine code made by `leanc`? Code that has a vector form and a portable form takes the vector
one only when it is (`quick`): interpreted, the definitions below are far slower than the portable form. -/
def compiled : Bool := false

def quick : Bool := compiled && wide

/-- Its argument. Written where a local is defined (`let mut pc := Fast.hotNat 0`), it tells `leanc` that
this is one of the few values an inner loop turns on, to be kept in a processor register rather than in
memory; `leanc` otherwise picks by counting uses, which says little about a loop with a hundred branches. -/
def hot (x : UInt64) : UInt64 := x
def hotNat (x : Nat) : Nat := x

-- ------------------------------------------------------------ the vector operations, as Lean

namespace Ref

def add32 (f : ByteArray) (d a b : Nat) : ByteArray := Id.run do
  let mut out := f
  for i in [0:16] do
    out := put32 out (64 * d + 4 * i) (le32 out (64 * a + 4 * i) + le32 out (64 * b + 4 * i))
  return out

def xor (f : ByteArray) (d a b : Nat) : ByteArray := Id.run do
  let mut out := f
  for i in [0:8] do
    out := put64 out (64 * d + 8 * i) (le64 out (64 * a + 8 * i) ^^^ le64 out (64 * b + 8 * i))
  return out

def and (f : ByteArray) (d a b : Nat) : ByteArray := Id.run do
  let mut out := f
  for i in [0:8] do
    out := put64 out (64 * d + 8 * i) (le64 out (64 * a + 8 * i) &&& le64 out (64 * b + 8 * i))
  return out

/-- Each of sixteen 32-bit numbers rotated right by `n` bits (0 to 31). -/
def ror32 (f : ByteArray) (d a n : Nat) : ByteArray := Id.run do
  let mut out := f
  for i in [0:16] do
    let x := le32 out (64 * a + 4 * i)
    out := put32 out (64 * d + 4 * i) (if n % 32 == 0 then x else (x >>> (n % 32).toUInt64) ||| (x <<< (32 - n % 32).toUInt64))
  return out

def add16 (f : ByteArray) (d a b : Nat) : ByteArray := Id.run do
  let mut out := f
  for i in [0:32] do
    out := put16 out (64 * d + 2 * i) (le16 out (64 * a + 2 * i) + le16 out (64 * b + 2 * i))
  return out

def sub16 (f : ByteArray) (d a b : Nat) : ByteArray := Id.run do
  let mut out := f
  for i in [0:32] do
    out := put16 out (64 * d + 2 * i) (le16 out (64 * a + 2 * i) + 0x10000 - le16 out (64 * b + 2 * i))
  return out

def add64 (f : ByteArray) (d a b : Nat) : ByteArray := Id.run do
  let mut out := f
  for i in [0:8] do
    out := put64 out (64 * d + 8 * i) (le64 out (64 * a + 8 * i) + le64 out (64 * b + 8 * i))
  return out

/-- Each of eight 64-bit numbers shifted right by `n` bits (0 to 63). -/
def srl64 (f : ByteArray) (d a n : Nat) : ByteArray := Id.run do
  let mut out := f
  for i in [0:8] do
    out := put64 out (64 * d + 8 * i) (le64 out (64 * a + 8 * i) >>> n.toUInt64)
  return out

def sll64 (f : ByteArray) (d a n : Nat) : ByteArray := Id.run do
  let mut out := f
  for i in [0:8] do
    out := put64 out (64 * d + 8 * i) (le64 out (64 * a + 8 * i) <<< n.toUInt64)
  return out

def low52 : UInt64 := 0xFFFFFFFFFFFFF

/-- On each of eight lanes: `acc` plus the low 52 bits of the product of the low 52 bits of `a` and of `b`. -/
def madd52lo (f : ByteArray) (d acc a b : Nat) : ByteArray := Id.run do
  let mut out := f
  for i in [0:8] do
    let x := le64 out (64 * a + 8 * i) &&& low52
    let y := le64 out (64 * b + 8 * i) &&& low52
    out := put64 out (64 * d + 8 * i) (le64 out (64 * acc + 8 * i) + ((x * y) &&& low52))
  return out

/-- The same with the next 52 bits of the product (bits 52 to 103). -/
def madd52hi (f : ByteArray) (d acc a b : Nat) : ByteArray := Id.run do
  let mut out := f
  for i in [0:8] do
    let x := le64 out (64 * a + 8 * i) &&& low52
    let y := le64 out (64 * b + 8 * i) &&& low52
    out := put64 out (64 * d + 8 * i) (le64 out (64 * acc + 8 * i) + ((((mulHi x y) <<< 12) ||| ((x * y) >>> 52)) &&& low52))
  return out

def move (f : ByteArray) (d a : Nat) : ByteArray := f.copySlice (64 * a) f (64 * d) 64

/-- Sixteen copies of the low 32 bits of `x`. -/
def set32 (f : ByteArray) (d : Nat) (x : UInt64) : ByteArray := Id.run do
  let mut out := f
  for i in [0:16] do
    out := put32 out (64 * d + 4 * i) x
  return out

def add32x3 (f : ByteArray) (d a b c : Nat) : ByteArray := Id.run do
  let mut out := f
  for i in [0:16] do
    out := put32 out (64 * d + 4 * i) (le32 out (64 * a + 4 * i) + le32 out (64 * b + 4 * i) + le32 out (64 * c + 4 * i))
  return out

def xorRor32 (f : ByteArray) (d a b n : Nat) : ByteArray := Id.run do
  let mut out := f
  for i in [0:16] do
    let x := le32 out (64 * a + 4 * i) ^^^ le32 out (64 * b + 4 * i)
    out := put32 out (64 * d + 4 * i) (if n % 32 == 0 then x else (x >>> (n % 32).toUInt64) ||| (x <<< (32 - n % 32).toUInt64))
  return out

/-- In each quarter of the register (four 32-bit numbers): the first two of `a` and of `b`, alternating. -/
def unpackLow32 (f : ByteArray) (d a b : Nat) : ByteArray := Id.run do
  let x := f.extract (64 * a) (64 * a + 64)
  let y := f.extract (64 * b) (64 * b + 64)
  let mut out := f
  for q in [0:4] do
    out := put32 out (64 * d + 16 * q) (le32 x (16 * q))
    out := put32 out (64 * d + 16 * q + 4) (le32 y (16 * q))
    out := put32 out (64 * d + 16 * q + 8) (le32 x (16 * q + 4))
    out := put32 out (64 * d + 16 * q + 12) (le32 y (16 * q + 4))
  return out

/-- The same with the last two of each quarter. -/
def unpackHigh32 (f : ByteArray) (d a b : Nat) : ByteArray := Id.run do
  let x := f.extract (64 * a) (64 * a + 64)
  let y := f.extract (64 * b) (64 * b + 64)
  let mut out := f
  for q in [0:4] do
    out := put32 out (64 * d + 16 * q) (le32 x (16 * q + 8))
    out := put32 out (64 * d + 16 * q + 4) (le32 y (16 * q + 8))
    out := put32 out (64 * d + 16 * q + 8) (le32 x (16 * q + 12))
    out := put32 out (64 * d + 16 * q + 12) (le32 y (16 * q + 12))
  return out

/-- In each quarter (two 64-bit numbers): the first of `a`, then the first of `b`. -/
def unpackLow64 (f : ByteArray) (d a b : Nat) : ByteArray := Id.run do
  let x := f.extract (64 * a) (64 * a + 64)
  let y := f.extract (64 * b) (64 * b + 64)
  let mut out := f
  for q in [0:4] do
    out := put64 out (64 * d + 16 * q) (le64 x (16 * q))
    out := put64 out (64 * d + 16 * q + 8) (le64 y (16 * q))
  return out

def unpackHigh64 (f : ByteArray) (d a b : Nat) : ByteArray := Id.run do
  let x := f.extract (64 * a) (64 * a + 64)
  let y := f.extract (64 * b) (64 * b + 64)
  let mut out := f
  for q in [0:4] do
    out := put64 out (64 * d + 16 * q) (le64 x (16 * q + 8))
    out := put64 out (64 * d + 16 * q + 8) (le64 y (16 * q + 8))
  return out

/-- Four quarters picked by `sel`, two bits each: the first two from `a`, the last two from `b`. -/
def shuffle128 (f : ByteArray) (d a b sel : Nat) : ByteArray := Id.run do
  let x := f.extract (64 * a) (64 * a + 64)
  let y := f.extract (64 * b) (64 * b + 64)
  let mut out := f
  out := x.copySlice (16 * (sel % 4)) out (64 * d) 16
  out := x.copySlice (16 * (sel / 4 % 4)) out (64 * d + 16) 16
  out := y.copySlice (16 * (sel / 16 % 4)) out (64 * d + 32) 16
  out := y.copySlice (16 * (sel / 64 % 4)) out (64 * d + 48) 16
  return out

end Ref

-- ---------------------------------------- the vector operations, as `leanc` compiles them

/-- Register `d` := register `a` + register `b`, as sixteen 32-bit numbers. -/
def add32 (f : ByteArray) (d a b : Nat) : ByteArray := Ref.add32 f d a b
def xor (f : ByteArray) (d a b : Nat) : ByteArray := Ref.xor f d a b
def and (f : ByteArray) (d a b : Nat) : ByteArray := Ref.and f d a b
def ror32 (f : ByteArray) (d a n : Nat) : ByteArray := Ref.ror32 f d a n
/-- As thirty-two 16-bit numbers. -/
def add16 (f : ByteArray) (d a b : Nat) : ByteArray := Ref.add16 f d a b
def sub16 (f : ByteArray) (d a b : Nat) : ByteArray := Ref.sub16 f d a b
/-- As eight 64-bit numbers. -/
def add64 (f : ByteArray) (d a b : Nat) : ByteArray := Ref.add64 f d a b
def srl64 (f : ByteArray) (d a n : Nat) : ByteArray := Ref.srl64 f d a n
def sll64 (f : ByteArray) (d a n : Nat) : ByteArray := Ref.sll64 f d a n
def madd52lo (f : ByteArray) (d acc a b : Nat) : ByteArray := Ref.madd52lo f d acc a b
def madd52hi (f : ByteArray) (d acc a b : Nat) : ByteArray := Ref.madd52hi f d acc a b
def move (f : ByteArray) (d a : Nat) : ByteArray := Ref.move f d a
def set32 (f : ByteArray) (d : Nat) (x : UInt64) : ByteArray := Ref.set32 f d x
def add32x3 (f : ByteArray) (d a b c : Nat) : ByteArray := Ref.add32x3 f d a b c
def xorRor32 (f : ByteArray) (d a b n : Nat) : ByteArray := Ref.xorRor32 f d a b n
def unpackLow32 (f : ByteArray) (d a b : Nat) : ByteArray := Ref.unpackLow32 f d a b
def unpackHigh32 (f : ByteArray) (d a b : Nat) : ByteArray := Ref.unpackHigh32 f d a b
def unpackLow64 (f : ByteArray) (d a b : Nat) : ByteArray := Ref.unpackLow64 f d a b
def unpackHigh64 (f : ByteArray) (d a b : Nat) : ByteArray := Ref.unpackHigh64 f d a b
def shuffle128 (f : ByteArray) (d a b sel : Nat) : ByteArray := Ref.shuffle128 f d a b sel

end Fast
