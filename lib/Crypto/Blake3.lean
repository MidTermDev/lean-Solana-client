import Fast

/-!
# BLAKE3

Solana hashes every account with BLAKE3, and not to 32 bytes: to 2048, which
it reads as 1024 sixteen-bit numbers (see `Solana.LtHash`). So this module
gives both the ordinary hash and the *extendable output*.

The design, briefly. Input is cut into chunks of 1024 bytes; each chunk is
hashed block by block (64 bytes) with one compression function; the chunks'
values are then combined pairwise into a binary tree. The last compression,
at the root, can be repeated with a counter to give as much output as is
wanted.
-/

namespace Blake3

def iv : Array UInt32 := #[
  0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

def chunkStart : UInt32 := 1
def chunkEnd : UInt32 := 2
def parent : UInt32 := 4
def root : UInt32 := 8

/-- Which message word each step of each of the seven rounds uses: the
identity for the first round, then the same permutation applied again and
again. -/
def schedule : ByteArray := Id.run do
  let permutation : Array Nat := #[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]
  let mut out := ByteArray.emptyWithCapacity 112
  for i in [0:16] do
    out := out.push i.toUInt8
  for r in [1:7] do
    for i in [0:16] do
      out := out.push out[(r - 1) * 16 + permutation[i]!]!
  return out

@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The compression function. `cv` is the chaining value (8 words), `m` the
block (16 words), `counter` the chunk number or the output block number.
Returns all 16 words of output; the first 8 are the new chaining value. -/
def compress (cv : Array UInt32) (m : Array UInt32) (counter : UInt64) (blockLen flags : UInt32) : Array UInt32 := Id.run do
  let s := schedule
  let mut v0 := cv[0]!
  let mut v1 := cv[1]!
  let mut v2 := cv[2]!
  let mut v3 := cv[3]!
  let mut v4 := cv[4]!
  let mut v5 := cv[5]!
  let mut v6 := cv[6]!
  let mut v7 := cv[7]!
  let mut v8 := iv[0]!
  let mut v9 := iv[1]!
  let mut v10 := iv[2]!
  let mut v11 := iv[3]!
  let mut v12 := counter.toUInt32
  let mut v13 := (counter >>> 32).toUInt32
  let mut v14 := blockLen
  let mut v15 := flags
  for r in [0:7] do
    let at_ := r * 16
    v0 := v0 + v4 + m[s[at_ + 0]!.toNat]!
    v12 := rotr (v12 ^^^ v0) 16
    v8 := v8 + v12
    v4 := rotr (v4 ^^^ v8) 12
    v0 := v0 + v4 + m[s[at_ + 1]!.toNat]!
    v12 := rotr (v12 ^^^ v0) 8
    v8 := v8 + v12
    v4 := rotr (v4 ^^^ v8) 7
    v1 := v1 + v5 + m[s[at_ + 2]!.toNat]!
    v13 := rotr (v13 ^^^ v1) 16
    v9 := v9 + v13
    v5 := rotr (v5 ^^^ v9) 12
    v1 := v1 + v5 + m[s[at_ + 3]!.toNat]!
    v13 := rotr (v13 ^^^ v1) 8
    v9 := v9 + v13
    v5 := rotr (v5 ^^^ v9) 7
    v2 := v2 + v6 + m[s[at_ + 4]!.toNat]!
    v14 := rotr (v14 ^^^ v2) 16
    v10 := v10 + v14
    v6 := rotr (v6 ^^^ v10) 12
    v2 := v2 + v6 + m[s[at_ + 5]!.toNat]!
    v14 := rotr (v14 ^^^ v2) 8
    v10 := v10 + v14
    v6 := rotr (v6 ^^^ v10) 7
    v3 := v3 + v7 + m[s[at_ + 6]!.toNat]!
    v15 := rotr (v15 ^^^ v3) 16
    v11 := v11 + v15
    v7 := rotr (v7 ^^^ v11) 12
    v3 := v3 + v7 + m[s[at_ + 7]!.toNat]!
    v15 := rotr (v15 ^^^ v3) 8
    v11 := v11 + v15
    v7 := rotr (v7 ^^^ v11) 7
    v0 := v0 + v5 + m[s[at_ + 8]!.toNat]!
    v15 := rotr (v15 ^^^ v0) 16
    v10 := v10 + v15
    v5 := rotr (v5 ^^^ v10) 12
    v0 := v0 + v5 + m[s[at_ + 9]!.toNat]!
    v15 := rotr (v15 ^^^ v0) 8
    v10 := v10 + v15
    v5 := rotr (v5 ^^^ v10) 7
    v1 := v1 + v6 + m[s[at_ + 10]!.toNat]!
    v12 := rotr (v12 ^^^ v1) 16
    v11 := v11 + v12
    v6 := rotr (v6 ^^^ v11) 12
    v1 := v1 + v6 + m[s[at_ + 11]!.toNat]!
    v12 := rotr (v12 ^^^ v1) 8
    v11 := v11 + v12
    v6 := rotr (v6 ^^^ v11) 7
    v2 := v2 + v7 + m[s[at_ + 12]!.toNat]!
    v13 := rotr (v13 ^^^ v2) 16
    v8 := v8 + v13
    v7 := rotr (v7 ^^^ v8) 12
    v2 := v2 + v7 + m[s[at_ + 13]!.toNat]!
    v13 := rotr (v13 ^^^ v2) 8
    v8 := v8 + v13
    v7 := rotr (v7 ^^^ v8) 7
    v3 := v3 + v4 + m[s[at_ + 14]!.toNat]!
    v14 := rotr (v14 ^^^ v3) 16
    v9 := v9 + v14
    v4 := rotr (v4 ^^^ v9) 12
    v3 := v3 + v4 + m[s[at_ + 15]!.toNat]!
    v14 := rotr (v14 ^^^ v3) 8
    v9 := v9 + v14
    v4 := rotr (v4 ^^^ v9) 7
  return #[v0 ^^^ v8, v1 ^^^ v9, v2 ^^^ v10, v3 ^^^ v11, v4 ^^^ v12, v5 ^^^ v13, v6 ^^^ v14, v7 ^^^ v15,
    v8 ^^^ cv[0]!, v9 ^^^ cv[1]!, v10 ^^^ cv[2]!, v11 ^^^ cv[3]!, v12 ^^^ cv[4]!, v13 ^^^ cv[5]!, v14 ^^^ cv[6]!, v15 ^^^ cv[7]!]

/-- The 64 bytes at `off` as 16 little-endian words. -/
def block (b : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut m : Array UInt32 := Array.emptyWithCapacity 16
  for i in [0:16] do
    let j := off + 4 * i
    m := m.push (b[j]!.toUInt32 ||| (b[j + 1]!.toUInt32 <<< 8) ||| (b[j + 2]!.toUInt32 <<< 16) ||| (b[j + 3]!.toUInt32 <<< 24))
  return m

/-- Up to 64 bytes `b[off, stop)` as 16 words, padded with zeros. -/
def lastBlock (b : ByteArray) (off stop : Nat) : Array UInt32 := Id.run do
  if stop == off + 64 then
    return block b off
  let mut padded := b.extract off stop
  while padded.size < 64 do
    padded := padded.push 0
  return block padded 0

def first8 (v : Array UInt32) : Array UInt32 :=
  #[v[0]!, v[1]!, v[2]!, v[3]!, v[4]!, v[5]!, v[6]!, v[7]!]

/-- A compression that has not been done yet: the root's can be repeated for more output. -/
structure Node where
  cv : Array UInt32
  block : Array UInt32
  counter : UInt64
  blockLen : UInt32
  flags : UInt32
  deriving Inhabited

def Node.value (n : Node) : Array UInt32 :=
  first8 (compress n.cv n.block n.counter n.blockLen n.flags)

/-- One chunk: `b[start, stop)`, at most 1024 bytes, chunk number `counter`. -/
def chunk (b : ByteArray) (start stop : Nat) (counter : UInt64) : Node := Id.run do
  let mut cv := iv
  let mut o := start
  let mut flags := chunkStart
  -- every block but the last (the last may be full, partial, or empty)
  while o + 64 < stop do
    cv := first8 (compress cv (block b o) counter 64 flags)
    flags := 0
    o := o + 64
  return ⟨cv, lastBlock b o stop, counter, (stop - o).toUInt32, flags ||| chunkEnd⟩

def join (left right : Array UInt32) : Node :=
  ⟨iv, #[left[0]!, left[1]!, left[2]!, left[3]!, left[4]!, left[5]!, left[6]!, left[7]!,
    right[0]!, right[1]!, right[2]!, right[3]!, right[4]!, right[5]!, right[6]!, right[7]!], 0, 64, parent⟩

-- ---------------------------------------------------------------- sixteen at once
--
-- With AVX-512 the compression function can be run on sixteen inputs at the price of one: each of its
-- sixteen state words becomes a register holding that word for all sixteen (see `Fast`). Two things
-- here have sixteen independent inputs: the chunks of a long input, and the output blocks of a root.
--
-- The registers of the file: 0-15 the state, 16-31 the message words, 32-39 the chaining value,
-- 40-55 sixteen blocks as they lie in memory (one per register), 56-71 scratch, 72 the numbers 0 to 15.

namespace Wide

def template : ByteArray := Id.run do
  let mut f := ByteArray.emptyWithCapacity 5120
  for _ in [0:5120] do
    f := f.push 0
  for i in [0:16] do
    f := Fast.put32 f (64 * 72 + 4 * i) i.toUInt64
  return f

/-- The quarter-round, on registers: the same eight steps as in `compress`. -/
@[inline] def g (f : ByteArray) (a b c d mx my : Nat) : ByteArray := Fast.quarter32 f a b c d mx my

/-- The seven rounds, on the state in registers 0-15 with the message in 16-31. (Written out: the
registers an instruction uses are part of the instruction.) -/
def rounds (f0 : ByteArray) : ByteArray :=
  let f := g f0 0 4 8 12 16 17
  let f := g f 1 5 9 13 18 19
  let f := g f 2 6 10 14 20 21
  let f := g f 3 7 11 15 22 23
  let f := g f 0 5 10 15 24 25
  let f := g f 1 6 11 12 26 27
  let f := g f 2 7 8 13 28 29
  let f := g f 3 4 9 14 30 31
  let f := g f 0 4 8 12 18 22
  let f := g f 1 5 9 13 19 26
  let f := g f 2 6 10 14 23 16
  let f := g f 3 7 11 15 20 29
  let f := g f 0 5 10 15 17 27
  let f := g f 1 6 11 12 28 21
  let f := g f 2 7 8 13 25 30
  let f := g f 3 4 9 14 31 24
  let f := g f 0 4 8 12 19 20
  let f := g f 1 5 9 13 26 28
  let f := g f 2 6 10 14 29 18
  let f := g f 3 7 11 15 23 30
  let f := g f 0 5 10 15 22 21
  let f := g f 1 6 11 12 25 16
  let f := g f 2 7 8 13 27 31
  let f := g f 3 4 9 14 24 17
  let f := g f 0 4 8 12 26 23
  let f := g f 1 5 9 13 28 25
  let f := g f 2 6 10 14 30 19
  let f := g f 3 7 11 15 29 31
  let f := g f 0 5 10 15 20 16
  let f := g f 1 6 11 12 27 18
  let f := g f 2 7 8 13 21 24
  let f := g f 3 4 9 14 17 22
  let f := g f 0 4 8 12 28 29
  let f := g f 1 5 9 13 25 27
  let f := g f 2 6 10 14 31 26
  let f := g f 3 7 11 15 30 24
  let f := g f 0 5 10 15 23 18
  let f := g f 1 6 11 12 21 19
  let f := g f 2 7 8 13 16 17
  let f := g f 3 4 9 14 22 20
  let f := g f 0 4 8 12 25 30
  let f := g f 1 5 9 13 27 21
  let f := g f 2 6 10 14 24 28
  let f := g f 3 7 11 15 31 17
  let f := g f 0 5 10 15 29 19
  let f := g f 1 6 11 12 16 26
  let f := g f 2 7 8 13 18 22
  let f := g f 3 4 9 14 20 23
  let f := g f 0 4 8 12 27 31
  let f := g f 1 5 9 13 21 16
  let f := g f 2 6 10 14 17 25
  let f := g f 3 7 11 15 24 22
  let f := g f 0 5 10 15 30 26
  let f := g f 1 6 11 12 18 28
  let f := g f 2 7 8 13 19 20
  let f := g f 3 4 9 14 23 29
  f

/-- Sixteen registers of sixteen numbers, turned: what was number `j` of register `s + i` becomes number
`i` of register `d + j`. Registers `s` to `s + 15` and `t` to `t + 15` are used up. -/
@[inline] def transpose (f0 : ByteArray) (s d t : Nat) : ByteArray :=
  let f := Fast.unpackLow32 f0 (t + 0) (s + 0) (s + 1)
  let f := Fast.unpackHigh32 f (t + 1) (s + 0) (s + 1)
  let f := Fast.unpackLow32 f (t + 2) (s + 2) (s + 3)
  let f := Fast.unpackHigh32 f (t + 3) (s + 2) (s + 3)
  let f := Fast.unpackLow32 f (t + 4) (s + 4) (s + 5)
  let f := Fast.unpackHigh32 f (t + 5) (s + 4) (s + 5)
  let f := Fast.unpackLow32 f (t + 6) (s + 6) (s + 7)
  let f := Fast.unpackHigh32 f (t + 7) (s + 6) (s + 7)
  let f := Fast.unpackLow32 f (t + 8) (s + 8) (s + 9)
  let f := Fast.unpackHigh32 f (t + 9) (s + 8) (s + 9)
  let f := Fast.unpackLow32 f (t + 10) (s + 10) (s + 11)
  let f := Fast.unpackHigh32 f (t + 11) (s + 10) (s + 11)
  let f := Fast.unpackLow32 f (t + 12) (s + 12) (s + 13)
  let f := Fast.unpackHigh32 f (t + 13) (s + 12) (s + 13)
  let f := Fast.unpackLow32 f (t + 14) (s + 14) (s + 15)
  let f := Fast.unpackHigh32 f (t + 15) (s + 14) (s + 15)
  let f := Fast.unpackLow64 f (s + 0) (t + 0) (t + 2)
  let f := Fast.unpackHigh64 f (s + 1) (t + 0) (t + 2)
  let f := Fast.unpackLow64 f (s + 2) (t + 1) (t + 3)
  let f := Fast.unpackHigh64 f (s + 3) (t + 1) (t + 3)
  let f := Fast.unpackLow64 f (s + 4) (t + 4) (t + 6)
  let f := Fast.unpackHigh64 f (s + 5) (t + 4) (t + 6)
  let f := Fast.unpackLow64 f (s + 6) (t + 5) (t + 7)
  let f := Fast.unpackHigh64 f (s + 7) (t + 5) (t + 7)
  let f := Fast.unpackLow64 f (s + 8) (t + 8) (t + 10)
  let f := Fast.unpackHigh64 f (s + 9) (t + 8) (t + 10)
  let f := Fast.unpackLow64 f (s + 10) (t + 9) (t + 11)
  let f := Fast.unpackHigh64 f (s + 11) (t + 9) (t + 11)
  let f := Fast.unpackLow64 f (s + 12) (t + 12) (t + 14)
  let f := Fast.unpackHigh64 f (s + 13) (t + 12) (t + 14)
  let f := Fast.unpackLow64 f (s + 14) (t + 13) (t + 15)
  let f := Fast.unpackHigh64 f (s + 15) (t + 13) (t + 15)
  let f := Fast.shuffle128 f (t + 0) (s + 0) (s + 4) 0x88
  let f := Fast.shuffle128 f (t + 4) (s + 0) (s + 4) 0xDD
  let f := Fast.shuffle128 f (t + 1) (s + 1) (s + 5) 0x88
  let f := Fast.shuffle128 f (t + 5) (s + 1) (s + 5) 0xDD
  let f := Fast.shuffle128 f (t + 2) (s + 2) (s + 6) 0x88
  let f := Fast.shuffle128 f (t + 6) (s + 2) (s + 6) 0xDD
  let f := Fast.shuffle128 f (t + 3) (s + 3) (s + 7) 0x88
  let f := Fast.shuffle128 f (t + 7) (s + 3) (s + 7) 0xDD
  let f := Fast.shuffle128 f (t + 8) (s + 8) (s + 12) 0x88
  let f := Fast.shuffle128 f (t + 12) (s + 8) (s + 12) 0xDD
  let f := Fast.shuffle128 f (t + 9) (s + 9) (s + 13) 0x88
  let f := Fast.shuffle128 f (t + 13) (s + 9) (s + 13) 0xDD
  let f := Fast.shuffle128 f (t + 10) (s + 10) (s + 14) 0x88
  let f := Fast.shuffle128 f (t + 14) (s + 10) (s + 14) 0xDD
  let f := Fast.shuffle128 f (t + 11) (s + 11) (s + 15) 0x88
  let f := Fast.shuffle128 f (t + 15) (s + 11) (s + 15) 0xDD
  let f := Fast.shuffle128 f (d + 0) (t + 0) (t + 8) 0x88
  let f := Fast.shuffle128 f (d + 8) (t + 0) (t + 8) 0xDD
  let f := Fast.shuffle128 f (d + 1) (t + 1) (t + 9) 0x88
  let f := Fast.shuffle128 f (d + 9) (t + 1) (t + 9) 0xDD
  let f := Fast.shuffle128 f (d + 2) (t + 2) (t + 10) 0x88
  let f := Fast.shuffle128 f (d + 10) (t + 2) (t + 10) 0xDD
  let f := Fast.shuffle128 f (d + 3) (t + 3) (t + 11) 0x88
  let f := Fast.shuffle128 f (d + 11) (t + 3) (t + 11) 0xDD
  let f := Fast.shuffle128 f (d + 4) (t + 4) (t + 12) 0x88
  let f := Fast.shuffle128 f (d + 12) (t + 4) (t + 12) 0xDD
  let f := Fast.shuffle128 f (d + 5) (t + 5) (t + 13) 0x88
  let f := Fast.shuffle128 f (d + 13) (t + 5) (t + 13) 0xDD
  let f := Fast.shuffle128 f (d + 6) (t + 6) (t + 14) 0x88
  let f := Fast.shuffle128 f (d + 14) (t + 6) (t + 14) 0xDD
  let f := Fast.shuffle128 f (d + 7) (t + 7) (t + 15) 0x88
  let f := Fast.shuffle128 f (d + 15) (t + 7) (t + 15) 0xDD
  f

/-- Output blocks `base` to `base + 15` of a root node: afterwards registers 40-55 hold them, 64 bytes
each, in order (bytes 2560 to 3583 of the file). -/
def output (f0 : ByteArray) (n : Node) (base : UInt64) : ByteArray := Id.run do
  let mut f := f0
  f := Fast.set32 f 0 n.cv[0]!.toUInt64
  f := Fast.set32 f 1 n.cv[1]!.toUInt64
  f := Fast.set32 f 2 n.cv[2]!.toUInt64
  f := Fast.set32 f 3 n.cv[3]!.toUInt64
  f := Fast.set32 f 4 n.cv[4]!.toUInt64
  f := Fast.set32 f 5 n.cv[5]!.toUInt64
  f := Fast.set32 f 6 n.cv[6]!.toUInt64
  f := Fast.set32 f 7 n.cv[7]!.toUInt64
  f := Fast.move f 32 0
  f := Fast.move f 33 1
  f := Fast.move f 34 2
  f := Fast.move f 35 3
  f := Fast.move f 36 4
  f := Fast.move f 37 5
  f := Fast.move f 38 6
  f := Fast.move f 39 7
  f := Fast.set32 f 8 iv[0]!.toUInt64
  f := Fast.set32 f 9 iv[1]!.toUInt64
  f := Fast.set32 f 10 iv[2]!.toUInt64
  f := Fast.set32 f 11 iv[3]!.toUInt64
  -- the block number: `base` plus 0 to 15
  f := Fast.set32 f 12 base
  f := Fast.add32 f 12 12 72
  f := Fast.set32 f 13 (base >>> 32)
  f := Fast.set32 f 14 n.blockLen.toUInt64
  f := Fast.set32 f 15 (n.flags ||| root).toUInt64
  f := Fast.set32 f 16 n.block[0]!.toUInt64
  f := Fast.set32 f 17 n.block[1]!.toUInt64
  f := Fast.set32 f 18 n.block[2]!.toUInt64
  f := Fast.set32 f 19 n.block[3]!.toUInt64
  f := Fast.set32 f 20 n.block[4]!.toUInt64
  f := Fast.set32 f 21 n.block[5]!.toUInt64
  f := Fast.set32 f 22 n.block[6]!.toUInt64
  f := Fast.set32 f 23 n.block[7]!.toUInt64
  f := Fast.set32 f 24 n.block[8]!.toUInt64
  f := Fast.set32 f 25 n.block[9]!.toUInt64
  f := Fast.set32 f 26 n.block[10]!.toUInt64
  f := Fast.set32 f 27 n.block[11]!.toUInt64
  f := Fast.set32 f 28 n.block[12]!.toUInt64
  f := Fast.set32 f 29 n.block[13]!.toUInt64
  f := Fast.set32 f 30 n.block[14]!.toUInt64
  f := Fast.set32 f 31 n.block[15]!.toUInt64
  f := rounds f
  f := Fast.xor f 0 0 8
  f := Fast.xor f 1 1 9
  f := Fast.xor f 2 2 10
  f := Fast.xor f 3 3 11
  f := Fast.xor f 4 4 12
  f := Fast.xor f 5 5 13
  f := Fast.xor f 6 6 14
  f := Fast.xor f 7 7 15
  f := Fast.xor f 8 8 32
  f := Fast.xor f 9 9 33
  f := Fast.xor f 10 10 34
  f := Fast.xor f 11 11 35
  f := Fast.xor f 12 12 36
  f := Fast.xor f 13 13 37
  f := Fast.xor f 14 14 38
  f := Fast.xor f 15 15 39
  return transpose f 0 40 56

/-- The first `blocks` blocks (1 to 16) of up to sixteen chunks, hashed side by side. Chunk `j` is the
1024 bytes (or fewer blocks' worth) of `inputs[which[first + j]]` at `offs[first + j]`, and is chunk
number `counters[first + j]` of its input. With sixteen blocks the chunks are whole, and afterwards word
`i` of chunk `j`'s value is number `j` of register `32 + i`; with fewer, what is left there is the
chaining value before the blocks that were not done (the chunk's last). -/
def chunksOf (f0 : ByteArray) (inputs : Array ByteArray) (which offs : Array Nat) (counters : Array UInt64)
    (first count blocks : Nat) : ByteArray := Id.run do
  let mut f := f0
  f := Fast.set32 f 32 iv[0]!.toUInt64
  f := Fast.set32 f 33 iv[1]!.toUInt64
  f := Fast.set32 f 34 iv[2]!.toUInt64
  f := Fast.set32 f 35 iv[3]!.toUInt64
  f := Fast.set32 f 36 iv[4]!.toUInt64
  f := Fast.set32 f 37 iv[5]!.toUInt64
  f := Fast.set32 f 38 iv[6]!.toUInt64
  f := Fast.set32 f 39 iv[7]!.toUInt64
  for k in [0:blocks] do
    -- block `k` of every chunk, one to a register, then turned into sixteen registers of message words
    for j in [0:count] do
      f := inputs[which[first + j]!]!.copySlice (offs[first + j]! + 64 * k) f (64 * (40 + j)) 64
    f := transpose f 40 16 56
    f := Fast.move f 0 32
    f := Fast.move f 1 33
    f := Fast.move f 2 34
    f := Fast.move f 3 35
    f := Fast.move f 4 36
    f := Fast.move f 5 37
    f := Fast.move f 6 38
    f := Fast.move f 7 39
    f := Fast.set32 f 8 iv[0]!.toUInt64
    f := Fast.set32 f 9 iv[1]!.toUInt64
    f := Fast.set32 f 10 iv[2]!.toUInt64
    f := Fast.set32 f 11 iv[3]!.toUInt64
    for j in [0:count] do
      f := Fast.put32 f (64 * 12 + 4 * j) counters[first + j]!
      f := Fast.put32 f (64 * 13 + 4 * j) (counters[first + j]! >>> 32)
    f := Fast.set32 f 14 64
    f := Fast.set32 f 15 ((if k == 0 then chunkStart else 0) ||| (if k == 15 then chunkEnd else 0)).toUInt64
    f := rounds f
    f := Fast.xor f 32 0 8
    f := Fast.xor f 33 1 9
    f := Fast.xor f 34 2 10
    f := Fast.xor f 35 3 11
    f := Fast.xor f 36 4 12
    f := Fast.xor f 37 5 13
    f := Fast.xor f 38 6 14
    f := Fast.xor f 39 7 15
  return f

/-- The value of chunk number `j` of those `chunks` hashed. -/
def value (f : ByteArray) (j : Nat) : Array UInt32 := Id.run do
  let mut v : Array UInt32 := Array.emptyWithCapacity 8
  for i in [0:8] do
    v := v.push (Fast.le32 f (64 * (32 + i) + 4 * j)).toUInt32
  return v

end Wide

/-- Hashes `b` down to the root of its tree. With `wide`, whole chunks are hashed sixteen at a time by
vector instructions; the result is the same either way. -/
def rootNodeBy (b : ByteArray) (wide : Bool) : Node := Id.run do
  let chunks := if b.size == 0 then 1 else (b.size + 1023) / 1024
  -- values of finished subtrees, largest first: one for each set bit of the number of chunks done
  let mut stack : Array (Array UInt32) := Array.emptyWithCapacity 54
  let mut f := if wide && chunks > 2 then Wide.template else ByteArray.empty
  let mut i := 0
  while i < chunks - 1 do
    -- every chunk but the last is whole; two or more of them are done together
    let together := if wide && chunks - 1 - i >= 2 && chunks < 0xFFFFFFF0 then min 16 (chunks - 1 - i) else 1
    if together != 1 then
      let mut which : Array Nat := Array.emptyWithCapacity 16
      let mut offs : Array Nat := Array.emptyWithCapacity 16
      let mut counters : Array UInt64 := Array.emptyWithCapacity 16
      for j in [0:together] do
        which := which.push 0
        offs := offs.push ((i + j) * 1024)
        counters := counters.push (i + j).toUInt64
      f := Wide.chunksOf f #[b] which offs counters 0 together 16
    for j in [0:together] do
      let mut value := if together != 1 then Wide.value f j
        else (chunk b ((i + j) * 1024) ((i + j) * 1024 + 1024) (i + j).toUInt64).value
      let mut done := i + j + 1
      while done % 2 == 0 do
        value := (join stack[stack.size - 1]! value).value
        stack := stack.pop
        done := done / 2
      stack := stack.push value
    i := i + together
  let mut node := chunk b ((chunks - 1) * 1024) b.size (chunks - 1).toUInt64
  while stack.size > 0 do
    node := join stack[stack.size - 1]! node.value
    stack := stack.pop
  return node

def rootNode (b : ByteArray) : Node := rootNodeBy b Fast.quick

/-- The roots of several inputs, with the vector instructions: the chunks of all of them are hashed
sixteen at a time, whichever input each belongs to, and so are the leading blocks of their last chunks
(those of the same length together). The same roots as `rootNodeBy` gives one by one. -/
def rootNodesWide (inputs : Array ByteArray) : Array Node := Id.run do
  let mut f := Wide.template
  -- 1. every whole chunk (all of an input's chunks but its last) of every input
  let mut which : Array Nat := Array.emptyWithCapacity 64
  let mut offs : Array Nat := Array.emptyWithCapacity 64
  let mut counters : Array UInt64 := Array.emptyWithCapacity 64
  for n in [0:inputs.size] do
    let size := inputs[n]!.size
    let chunks := if size == 0 then 1 else (size + 1023) / 1024
    for c in [0:chunks - 1] do
      which := which.push n
      offs := offs.push (c * 1024)
      counters := counters.push c.toUInt64
  let mut values : Array (Array UInt32) := Array.emptyWithCapacity which.size
  let mut done := 0
  while done < which.size do
    let together := min 16 (which.size - done)
    f := Wide.chunksOf f inputs which offs counters done together 16
    for j in [0:together] do
      values := values.push (Wide.value f j)
    done := done + together
  -- 2. the last chunk of every input: its blocks but the last, those with the same number of them together
  let mut before : Array (Array UInt32) := Array.replicate inputs.size iv
  for blocks in [1:16] do
    let mut lastWhich : Array Nat := Array.emptyWithCapacity 16
    let mut lastOffs : Array Nat := Array.emptyWithCapacity 16
    let mut lastCounters : Array UInt64 := Array.emptyWithCapacity 16
    for n in [0:inputs.size] do
      let size := inputs[n]!.size
      let chunks := if size == 0 then 1 else (size + 1023) / 1024
      let tail := size - (chunks - 1) * 1024
      if tail != 0 && (tail + 63) / 64 - 1 == blocks then
        lastWhich := lastWhich.push n
        lastOffs := lastOffs.push ((chunks - 1) * 1024)
        lastCounters := lastCounters.push (chunks - 1).toUInt64
    let mut at_ := 0
    while at_ < lastWhich.size do
      let together := min 16 (lastWhich.size - at_)
      f := Wide.chunksOf f inputs lastWhich lastOffs lastCounters at_ together blocks
      for j in [0:together] do
        before := before.set! lastWhich[at_ + j]! (Wide.value f j)
      at_ := at_ + together
  -- 3. each input's tree, from its chunks' values
  let mut roots : Array Node := Array.emptyWithCapacity inputs.size
  let mut next := 0
  for n in [0:inputs.size] do
    let b := inputs[n]!
    let chunks := if b.size == 0 then 1 else (b.size + 1023) / 1024
    let mut stack : Array (Array UInt32) := Array.emptyWithCapacity 54
    for c in [0:chunks - 1] do
      let mut value := values[next + c]!
      let mut finished := c + 1
      while finished % 2 == 0 do
        value := (join stack[stack.size - 1]! value).value
        stack := stack.pop
        finished := finished / 2
      stack := stack.push value
    next := next + (chunks - 1)
    let start := (chunks - 1) * 1024
    let tail := b.size - start
    let led := if tail == 0 then 0 else (tail + 63) / 64 - 1
    let mut node : Node := ⟨before[n]!, lastBlock b (start + 64 * led) b.size, (chunks - 1).toUInt64,
      (b.size - (start + 64 * led)).toUInt32, (if led == 0 then chunkStart else 0) ||| chunkEnd⟩
    while stack.size > 0 do
      node := join stack[stack.size - 1]! node.value
      stack := stack.pop
    roots := roots.push node
  return roots

/-- The roots of several inputs. -/
def rootNodes (inputs : Array ByteArray) (wide : Bool) : Array Node := Id.run do
  if wide then
    return rootNodesWide inputs
  let mut roots : Array Node := Array.emptyWithCapacity inputs.size
  for b in inputs do
    roots := roots.push (rootNodeBy b false)
  return roots

/-- The 16 words of output block number `k` of a root node. -/
@[inline] def Node.output (n : Node) (k : UInt64) : Array UInt32 :=
  compress n.cv n.block k n.blockLen (n.flags ||| root)

/-- `length` bytes of output. -/
def Node.bytes (n : Node) (length : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (length + 64)
  let mut k : UInt64 := 0
  while out.size < length do
    let words := n.output k
    for w in words do
      out := out.push w.toUInt8
      out := out.push (w >>> 8).toUInt8
      out := out.push (w >>> 16).toUInt8
      out := out.push (w >>> 24).toUInt8
    k := k + 1
  return out.extract 0 length

/-- `length` bytes of output; with `wide`, sixteen blocks at a time. -/
def Node.bytesBy (n : Node) (length : Nat) (wide : Bool) : ByteArray := Id.run do
  if !wide || length <= 64 then
    return n.bytes length
  let mut out := ByteArray.emptyWithCapacity (length + 1024)
  let mut f := Wide.template
  let mut k : UInt64 := 0
  while out.size < length do
    f := Wide.output f n k
    out := f.copySlice 2560 out out.size 1024
    k := k + 16
  return out.extract 0 length

/-- BLAKE3 of `b`: 32 bytes. -/
def hash (b : ByteArray) : ByteArray := (rootNode b).bytes 32

/-- BLAKE3 of `b`, extended to `length` bytes. -/
def xof (b : ByteArray) (length : Nat) : ByteArray := (rootNode b).bytesBy length Fast.quick

end Blake3
