import Fast

/-!
# SHA-256 (FIPS 180-4)

Used by Solana for the gossip ping/pong token hash and for CRDS value hashes.
-/

namespace Sha256

/-- Initial hash value: fractional parts of the square roots of the first 8 primes, as the eight words
of state `Fast.sha256Blocks` works on. -/
def init : ByteArray :=
  let b := ByteArray.emptyWithCapacity 32
  let b := Fast.push32 (Fast.push32 b 0x6a09e667) 0xbb67ae85
  let b := Fast.push32 (Fast.push32 b 0x3c6ef372) 0xa54ff53a
  let b := Fast.push32 (Fast.push32 b 0x510e527f) 0x9b05688c
  Fast.push32 (Fast.push32 b 0x1f83d9ab) 0x5be0cd19

/-- The compression function over `count` 64-byte blocks of `data` from `off`: by the processor's SHA
instructions where it has them, by the same function in plain Lean otherwise. -/
def blocks (state : ByteArray) (data : ByteArray) (off count : Nat) : ByteArray :=
  if Fast.sha then Fast.sha256Blocks state data off count else Fast.Ref.sha256Blocks state data off count

/-- SHA-256 of `data`: 32 bytes. -/
def hash (data : ByteArray) : ByteArray := Id.run do
  let n := data.size
  let full := n / 64
  let mut h := blocks init data 0 full
  -- final block(s): remaining bytes, 0x80, zero padding, 64-bit big-endian bit length
  let mut tail := data.extract (full * 64) n
  tail := tail.push 0x80
  while tail.size % 64 != 56 do
    tail := tail.push 0
  let bits : UInt64 := n.toUInt64 * 8
  for i in [0:8] do
    tail := tail.push (bits >>> ((7 - i).toUInt64 * 8)).toUInt8
  h := blocks h tail 0 (tail.size / 64)
  let mut out := ByteArray.emptyWithCapacity 32
  for i in [0:8] do
    let v := Fast.le32 h (4 * i)
    out := out.push (v >>> 24).toUInt8
    out := out.push (v >>> 16).toUInt8
    out := out.push (v >>> 8).toUInt8
    out := out.push v.toUInt8
  return out

end Sha256
