/-!
# SHA-512 (FIPS 180-4)

Ed25519 hashes with SHA-512, so every signature check runs through this.
-/

namespace Sha512

/-- Round constants: the first 64 bits of the fractional parts of the cube
roots of the first 80 primes. -/
def k : Array UInt64 := #[
  0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
  0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
  0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
  0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
  0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
  0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
  0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
  0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
  0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
  0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
  0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
  0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
  0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
  0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
  0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
  0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
  0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
  0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
  0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
  0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817]

def init : Array UInt64 := #[
  0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
  0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179]

@[inline] def rotr (x : UInt64) (n : UInt64) : UInt64 := (x >>> n) ||| (x <<< (64 - n))

/-- Reads a big-endian 64-bit word at byte offset `j`. -/
def be64 (data : ByteArray) (j : Nat) : UInt64 :=
  (data[j]!.toUInt64 <<< 56) ||| (data[j + 1]!.toUInt64 <<< 48) |||
    (data[j + 2]!.toUInt64 <<< 40) ||| (data[j + 3]!.toUInt64 <<< 32) |||
    (data[j + 4]!.toUInt64 <<< 24) ||| (data[j + 5]!.toUInt64 <<< 16) |||
    (data[j + 6]!.toUInt64 <<< 8) ||| data[j + 7]!.toUInt64

/-- The compression function: folds the 128-byte block at `off` into state `h`. -/
def compress (h : Array UInt64) (data : ByteArray) (off : Nat) : Array UInt64 := Id.run do
  let mut w : Array UInt64 := Array.replicate 80 0
  for i in [0:16] do
    w := w.set! i (be64 data (off + i * 8))
  for i in [16:80] do
    let w15 := w[i - 15]!
    let w2 := w[i - 2]!
    let s0 := rotr w15 1 ^^^ rotr w15 8 ^^^ (w15 >>> 7)
    let s1 := rotr w2 19 ^^^ rotr w2 61 ^^^ (w2 >>> 6)
    w := w.set! i (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for i in [0:80] do
    let s1 := rotr e 14 ^^^ rotr e 18 ^^^ rotr e 41
    let ch := (e &&& f) ^^^ (~~~e &&& g)
    let t1 := hh + s1 + ch + k[i]! + w[i]!
    let s0 := rotr a 28 ^^^ rotr a 34 ^^^ rotr a 39
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := s0 + maj
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

/-- SHA-512 of `data`: 64 bytes. -/
def hash (data : ByteArray) : ByteArray := Id.run do
  let n := data.size
  let full := n / 128
  let mut h := init
  for b in [0:full] do
    h := compress h data (b * 128)
  -- final block(s): remaining bytes, 0x80, zero padding, 128-bit big-endian bit length
  let mut tail := data.extract (full * 128) n
  tail := tail.push 0x80
  while tail.size % 128 != 112 do
    tail := tail.push 0
  -- the length field is 128 bits wide; its upper half is always zero here
  for _ in [0:8] do
    tail := tail.push 0
  let bits : UInt64 := n.toUInt64 * 8
  for i in [0:8] do
    tail := tail.push (bits >>> ((7 - i).toUInt64 * 8)).toUInt8
  for b in [0:tail.size / 128] do
    h := compress h tail (b * 128)
  let mut out := ByteArray.emptyWithCapacity 64
  for i in [0:8] do
    let v := h[i]!
    for j in [0:8] do
      out := out.push (v >>> ((7 - j).toUInt64 * 8)).toUInt8
  return out

end Sha512
