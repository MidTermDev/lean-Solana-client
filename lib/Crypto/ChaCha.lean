/-!
# ChaCha20, as a random number generator

Solana draws its leader schedule from a generator every validator must
reproduce exactly: ChaCha20 keyed with a 32-byte seed, its output read as
64-bit numbers. This is that generator (the one Rust's `rand_chacha` calls
`ChaChaRng`), no more: the block function, and the stream of numbers.
-/

namespace ChaCha

@[inline] def rotl (x : UInt32) (n : UInt32) : UInt32 := (x <<< n) ||| (x >>> (32 - n))

/-- The ChaCha20 block for a key of 8 words and a 64-bit block counter (the nonce is zero): 16 words. -/
def block (key : Array UInt32) (counter : UInt64) : Array UInt32 := Id.run do
  let c0 : UInt32 := 0x61707865
  let c1 : UInt32 := 0x3320646e
  let c2 : UInt32 := 0x79622d32
  let c3 : UInt32 := 0x6b206574
  let n0 := counter.toUInt32
  let n1 := (counter >>> 32).toUInt32
  let mut x0 := c0
  let mut x1 := c1
  let mut x2 := c2
  let mut x3 := c3
  let mut x4 := key[0]!
  let mut x5 := key[1]!
  let mut x6 := key[2]!
  let mut x7 := key[3]!
  let mut x8 := key[4]!
  let mut x9 := key[5]!
  let mut x10 := key[6]!
  let mut x11 := key[7]!
  let mut x12 := n0
  let mut x13 := n1
  let mut x14 : UInt32 := 0
  let mut x15 : UInt32 := 0
  for _ in [0:10] do
    -- four quarter rounds down the columns
    x0 := x0 + x4
    x12 := rotl (x12 ^^^ x0) 16
    x8 := x8 + x12
    x4 := rotl (x4 ^^^ x8) 12
    x0 := x0 + x4
    x12 := rotl (x12 ^^^ x0) 8
    x8 := x8 + x12
    x4 := rotl (x4 ^^^ x8) 7
    x1 := x1 + x5
    x13 := rotl (x13 ^^^ x1) 16
    x9 := x9 + x13
    x5 := rotl (x5 ^^^ x9) 12
    x1 := x1 + x5
    x13 := rotl (x13 ^^^ x1) 8
    x9 := x9 + x13
    x5 := rotl (x5 ^^^ x9) 7
    x2 := x2 + x6
    x14 := rotl (x14 ^^^ x2) 16
    x10 := x10 + x14
    x6 := rotl (x6 ^^^ x10) 12
    x2 := x2 + x6
    x14 := rotl (x14 ^^^ x2) 8
    x10 := x10 + x14
    x6 := rotl (x6 ^^^ x10) 7
    x3 := x3 + x7
    x15 := rotl (x15 ^^^ x3) 16
    x11 := x11 + x15
    x7 := rotl (x7 ^^^ x11) 12
    x3 := x3 + x7
    x15 := rotl (x15 ^^^ x3) 8
    x11 := x11 + x15
    x7 := rotl (x7 ^^^ x11) 7
    -- and four along the diagonals
    x0 := x0 + x5
    x15 := rotl (x15 ^^^ x0) 16
    x10 := x10 + x15
    x5 := rotl (x5 ^^^ x10) 12
    x0 := x0 + x5
    x15 := rotl (x15 ^^^ x0) 8
    x10 := x10 + x15
    x5 := rotl (x5 ^^^ x10) 7
    x1 := x1 + x6
    x12 := rotl (x12 ^^^ x1) 16
    x11 := x11 + x12
    x6 := rotl (x6 ^^^ x11) 12
    x1 := x1 + x6
    x12 := rotl (x12 ^^^ x1) 8
    x11 := x11 + x12
    x6 := rotl (x6 ^^^ x11) 7
    x2 := x2 + x7
    x13 := rotl (x13 ^^^ x2) 16
    x8 := x8 + x13
    x7 := rotl (x7 ^^^ x8) 12
    x2 := x2 + x7
    x13 := rotl (x13 ^^^ x2) 8
    x8 := x8 + x13
    x7 := rotl (x7 ^^^ x8) 7
    x3 := x3 + x4
    x14 := rotl (x14 ^^^ x3) 16
    x9 := x9 + x14
    x4 := rotl (x4 ^^^ x9) 12
    x3 := x3 + x4
    x14 := rotl (x14 ^^^ x3) 8
    x9 := x9 + x14
    x4 := rotl (x4 ^^^ x9) 7
  return #[x0 + c0, x1 + c1, x2 + c2, x3 + c3, x4 + key[0]!, x5 + key[1]!, x6 + key[2]!, x7 + key[3]!,
    x8 + key[4]!, x9 + key[5]!, x10 + key[6]!, x11 + key[7]!, x12 + n0, x13 + n1, x14, x15]

/-- The generator: the key, the block being read, and how far into it. -/
structure Rng where
  key : Array UInt32
  counter : UInt64
  words : Array UInt32
  index : Nat

/-- A generator seeded with 32 bytes. -/
def Rng.seeded (seed : ByteArray) : Rng := Id.run do
  let mut key : Array UInt32 := Array.emptyWithCapacity 8
  for i in [0:8] do
    key := key.push (seed[4 * i]!.toUInt32 ||| (seed[4 * i + 1]!.toUInt32 <<< 8) ||| (seed[4 * i + 2]!.toUInt32 <<< 16) ||| (seed[4 * i + 3]!.toUInt32 <<< 24))
  return ⟨key, 1, block key 0, 0⟩

/-- The next 32 bits of the stream. -/
def Rng.next32 (r : Rng) : UInt32 × Rng :=
  if r.index < 16 then (r.words[r.index]!, { r with index := r.index + 1 })
  else
    let words := block r.key r.counter
    (words[0]!, ⟨r.key, r.counter + 1, words, 1⟩)

/-- The next 64 bits: two words of the stream, the first the low half. -/
def Rng.next64 (r : Rng) : UInt64 × Rng :=
  let (low, r1) := r.next32
  let (high, r2) := r1.next32
  (low.toUInt64 ||| (high.toUInt64 <<< 32), r2)

end ChaCha
