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

/-- Appends the low two bytes of `v`, least significant first. -/
def push16 (b : ByteArray) (v : UInt64) : ByteArray := (b.push v.toUInt8).push (v >>> 8).toUInt8

/-- Appends the low four bytes of `v`. -/
def push32 (b : ByteArray) (v : UInt64) : ByteArray := push16 (push16 b v) (v >>> 16)

/-- Appends `v`, eight bytes. -/
def push64 (b : ByteArray) (v : UInt64) : ByteArray := push32 (push32 b v) (v >>> 32)

/-- Appends `n` zero bytes. -/
def pushZeros (b : ByteArray) (n : Nat) : ByteArray := Id.run do
  let mut out := b
  for _ in [0:n] do
    out := out.push 0
  return out

/-- `n` zero bytes, in an array with room for `capacity` bytes. -/
def zeroed (n capacity : Nat) : ByteArray := pushZeros (ByteArray.emptyWithCapacity (if capacity > n then capacity else n)) n

/-- Whether the `n` bytes of `b` from `o` and the `n` bytes of `c` from `p` are the same; false if either
range leaves its array. (Compared where they lie, eight at a time.) -/
def sameAt (b : ByteArray) (o : Nat) (c : ByteArray) (p n : Nat) : Bool := Id.run do
  if o + n > b.size || p + n > c.size then
    return false
  for i in [0:n] do
    if b[o + i]! != c[p + i]! then
      return false
  return true

/-- How many bytes of `b` from `i` on are zero, looking no further than `stop` (or the end). -/
def zeroRun (b : ByteArray) (i stop : Nat) : Nat := Id.run do
  let mut n := 0
  while i + n < stop && i + n < b.size && b[i + n]! == 0 do
    n := n + 1
  return n

/-- How many bytes of `b` from `i` on are not zero, looking no further than `stop` (or the end). -/
def plainRun (b : ByteArray) (i stop : Nat) : Nat := Id.run do
  let mut n := 0
  while i + n < stop && i + n < b.size && b[i + n]! != 0 do
    n := n + 1
  return n

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

/-- The SHA-256 instructions (with AVX2, which every processor that is given them for speed also has). -/
def sha : Bool := cpuBits &&& 0x20000020 == 0x20000020

/-- The shifts whose count is in any register (`shlx`, `shrx`, `sarx`: BMI2). -/
def anyShift : Bool := cpuBits &&& 0x100 != 0

-- ------------------------------------------------------- machine code made while the program runs
--
-- A program can write machine code into a byte array and have the processor run it. These two functions
-- are the whole of that door. Plain Lean has no such door, and here they do nothing: `codeLoad` answers
-- 0 ("this machine will not run it") and whoever asked carries on the way it would on such a machine.

/-- Makes `code`'s bytes executable: the address of a copy of them that the processor may run, or 0 if it
may not. -/
def codeLoad (code : ByteArray) : UInt64 := if code.size == 0 then 0 else 0

/-- Calls the code at `entry` (an address inside something `codeLoad` returned) with the addresses of the
words of `cpu` and of the bytes of `mem` and `ro`, and returns `cpu` and `mem` as that code left them.
What the code does is up to whoever wrote its bytes; all this promises is that nothing but `cpu` and
`mem` is changed. -/
def run (entry : UInt64) (cpu : Array UInt64) (mem : ByteArray) (ro : ByteArray) : Array UInt64 × ByteArray :=
  if entry == 0 || ro.size == 0 then (cpu, mem) else (cpu, mem)

-- ------------------------------------------------------- a memory outside the language
--
-- Some answers are expensive, a function of 32 bytes alone, and asked for again and again (is this hash
-- a point on the curve?). `leanc` keeps a table of them for as long as the program runs. A pure function
-- cannot have such a table, so in plain Lean these remember nothing: `remembered` answers 0 and the
-- caller works the answer out, every time. The rule that keeps the two the same: only ever `remember`
-- under a key a value that the key alone determines.

/-- What was last noted under `key` (32 bytes that are already well mixed: a hash, an address), or 0. -/
def remembered (key : ByteArray) : UInt64 := if key.size == 32 then 0 else 0

/-- Notes `value` (not 0) under `key`, and returns it. -/
def remember (key : ByteArray) (value : UInt64) : UInt64 := if key.size == 32 then value else value

/-- Its argument. Written where a local is defined (`let mut pc := Fast.hotNat 0`), it tells `leanc` that
this is one of the few values an inner loop turns on, to be kept in a processor register rather than in
memory; `leanc` otherwise picks by counting uses, which says little about a loop with a hundred branches. -/
def hot (x : UInt64) : UInt64 := x
def hotNat (x : Nat) : Nat := x

-- ------------------------------------------------------------ the vector operations, as Lean

namespace Ref

/-- SHA-256's round constants: the first 32 bits of the fractional parts of the cube roots of the first
64 primes. -/
def sha256K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

@[inline] def rotr32 (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- SHA-256's compression function (FIPS 180-4), over `blocks` 64-byte blocks of `data` from `off`.
`state` is the eight working words h0 to h7, four bytes each, least significant byte first. -/
def sha256Blocks (state0 : ByteArray) (data : ByteArray) (off blocks : Nat) : ByteArray := Id.run do
  let mut state := state0
  for block in [0:blocks] do
    let at_ := off + 64 * block
    let mut w : Array UInt32 := Array.replicate 64 0
    for i in [0:16] do
      let j := at_ + 4 * i
      w := w.set! i ((data[j]!.toUInt32 <<< 24) ||| (data[j + 1]!.toUInt32 <<< 16) |||
        (data[j + 2]!.toUInt32 <<< 8) ||| data[j + 3]!.toUInt32)
    for i in [16:64] do
      let w15 := w[i - 15]!
      let w2 := w[i - 2]!
      let s0 := rotr32 w15 7 ^^^ rotr32 w15 18 ^^^ (w15 >>> 3)
      let s1 := rotr32 w2 17 ^^^ rotr32 w2 19 ^^^ (w2 >>> 10)
      w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
    let mut a := (le32 state 0).toUInt32
    let mut b := (le32 state 4).toUInt32
    let mut c := (le32 state 8).toUInt32
    let mut d := (le32 state 12).toUInt32
    let mut e := (le32 state 16).toUInt32
    let mut f := (le32 state 20).toUInt32
    let mut g := (le32 state 24).toUInt32
    let mut h := (le32 state 28).toUInt32
    for i in [0:64] do
      let s1 := rotr32 e 6 ^^^ rotr32 e 11 ^^^ rotr32 e 25
      let ch := (e &&& f) ^^^ (~~~e &&& g)
      let t1 := h + s1 + ch + sha256K[i]! + w[i]!
      let s0 := rotr32 a 2 ^^^ rotr32 a 13 ^^^ rotr32 a 22
      let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
      let t2 := s0 + maj
      h := g
      g := f
      f := e
      e := d + t1
      d := c
      c := b
      b := a
      a := t1 + t2
    state := put32 state 0 ((le32 state 0).toUInt32 + a).toUInt64
    state := put32 state 4 ((le32 state 4).toUInt32 + b).toUInt64
    state := put32 state 8 ((le32 state 8).toUInt32 + c).toUInt64
    state := put32 state 12 ((le32 state 12).toUInt32 + d).toUInt64
    state := put32 state 16 ((le32 state 16).toUInt32 + e).toUInt64
    state := put32 state 20 ((le32 state 20).toUInt32 + f).toUInt64
    state := put32 state 24 ((le32 state 24).toUInt32 + g).toUInt64
    state := put32 state 28 ((le32 state 28).toUInt32 + h).toUInt64
  return state

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

/-- The quarter-round of BLAKE2s and BLAKE3 on registers `a`, `b`, `c`, `d`, with the message registers
`mx` and `my`: eight steps of add, exclusive-or and rotate. -/
def quarter32 (f : ByteArray) (a b c d mx my : Nat) : ByteArray :=
  let f := add32x3 f a a b mx
  let f := xorRor32 f d d a 16
  let f := add32 f c c d
  let f := xorRor32 f b b c 12
  let f := add32x3 f a a b my
  let f := xorRor32 f d d a 8
  let f := add32 f c c d
  xorRor32 f b b c 7

end Ref

/-- SHA-256's compression function over whole blocks (see `Ref.sha256Blocks`); with `sha`, the
processor's own instructions for it. -/
def sha256Blocks (state : ByteArray) (data : ByteArray) (off blocks : Nat) : ByteArray :=
  Ref.sha256Blocks state data off blocks

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
/-- (The four registers must be different ones.) -/
def quarter32 (f : ByteArray) (a b c d mx my : Nat) : ByteArray := Ref.quarter32 f a b c d mx my

end Fast
