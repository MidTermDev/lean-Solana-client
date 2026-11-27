/-!
# Keccak-256

The hash Ethereum uses (the original Keccak padding, not SHA-3's). Programs
on Solana reach it through a system call, mostly to check Ethereum-style
signatures and Merkle proofs.

The state is 25 words of 64 bits; each round mixes columns (θ), rotates and
moves words (ρ, π), combines rows (χ) and adds a constant (ι). Input is
absorbed 136 bytes at a time.
-/

namespace Keccak

def roundConstants : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000, 0x000000000000808B, 0x0000000080000001,
  0x8000000080008081, 0x8000000000008009, 0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003, 0x8000000000008002, 0x8000000000000080,
  0x000000000000800A, 0x800000008000000A, 0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- How far each word is rotated, and where it goes, in the order the words are visited. -/
def rotations : Array UInt64 := #[1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44]
def places : Array Nat := #[10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1]

@[inline] def rotl (x n : UInt64) : UInt64 := (x <<< n) ||| (x >>> (64 - n))

/-- The permutation: 24 rounds over the 25 words. -/
def permute (state : Array UInt64) : Array UInt64 := Id.run do
  let mut a := state
  for round in [0:24] do
    -- θ: each word takes the parity of two neighbouring columns
    let mut c : Array UInt64 := Array.emptyWithCapacity 5
    for x in [0:5] do
      c := c.push (a[x]! ^^^ a[x + 5]! ^^^ a[x + 10]! ^^^ a[x + 15]! ^^^ a[x + 20]!)
    for x in [0:5] do
      let d := c[(x + 4) % 5]! ^^^ rotl c[(x + 1) % 5]! 1
      for y in [0:5] do
        a := a.set! (x + 5 * y) (a[x + 5 * y]! ^^^ d)
    -- ρ and π: rotate each word and move it
    let mut carried := a[1]!
    for i in [0:24] do
      let to := places[i]!
      let next := a[to]!
      a := a.set! to (rotl carried rotations[i]!)
      carried := next
    -- χ: each word is combined with the next two of its row
    for y in [0:5] do
      let r0 := a[5 * y]!
      let r1 := a[5 * y + 1]!
      let r2 := a[5 * y + 2]!
      let r3 := a[5 * y + 3]!
      let r4 := a[5 * y + 4]!
      a := a.set! (5 * y) (r0 ^^^ (~~~r1 &&& r2))
      a := a.set! (5 * y + 1) (r1 ^^^ (~~~r2 &&& r3))
      a := a.set! (5 * y + 2) (r2 ^^^ (~~~r3 &&& r4))
      a := a.set! (5 * y + 3) (r3 ^^^ (~~~r4 &&& r0))
      a := a.set! (5 * y + 4) (r4 ^^^ (~~~r0 &&& r1))
    -- ι
    a := a.set! 0 (a[0]! ^^^ roundConstants[round]!)
  return a

/-- Keccak-256 of `data`: 32 bytes. -/
def hash (data : ByteArray) : ByteArray := Id.run do
  -- pad to a multiple of 136 bytes: a 1 bit, zeros, a final 1 bit
  let mut padded := data.push 0x01
  while padded.size % 136 != 0 do
    padded := padded.push 0
  padded := padded.set! (padded.size - 1) (padded[padded.size - 1]! ||| 0x80)
  let mut state : Array UInt64 := Array.replicate 25 0
  for block in [0:padded.size / 136] do
    for i in [0:17] do
      let mut word : UInt64 := 0
      for j in [0:8] do
        word := word ||| (padded[136 * block + 8 * i + j]!.toUInt64 <<< (8 * j).toUInt64)
      state := state.set! i (state[i]! ^^^ word)
    state := permute state
  let mut out := ByteArray.emptyWithCapacity 32
  for i in [0:4] do
    for j in [0:8] do
      out := out.push (state[i]! >>> (8 * j).toUInt64).toUInt8
  return out

end Keccak
