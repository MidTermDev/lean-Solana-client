import Crypto.Ed25519

/-!
# X25519: agreeing on a secret (RFC 7748)

Each side picks a secret number and sends that many times the curve's base
point, as one coordinate, 32 bytes. Either side's number times the other's
point is the same point: the shared secret. Only that coordinate is ever
computed, by the Montgomery ladder, on the field Ed25519 already works in.
-/

namespace X25519
open Ed25519

def a24 : Fe := Fe.fromBytes (Hex.decode "41db010000000000000000000000000000000000000000000000000000000000")

/-- `secret` (32 bytes, clamped as the RFC says) times the point whose coordinate is `point`. -/
def multiply (secret point : ByteArray) : ByteArray := Id.run do
  let k := (secret.set! 0 (secret[0]! &&& 248)).set! 31 ((secret[31]! &&& 127) ||| 64)
  let x1 := Fe.fromBytes point
  let mut x2 := Fe.one
  let mut z2 := Fe.zero
  let mut x3 := x1
  let mut z3 := Fe.one
  let mut swapped := false
  for i in [0:255] do
    let t := 254 - i
    let bit := (k[t / 8]! >>> (t % 8).toUInt8) &&& 1 == 1
    if bit != swapped then
      let x := x2
      x2 := x3
      x3 := x
      let z := z2
      z2 := z3
      z3 := z
    swapped := bit
    let a := Fe.add x2 z2
    let aa := Fe.sq a
    let b := Fe.sub x2 z2
    let bb := Fe.sq b
    let e := Fe.sub aa bb
    let da := Fe.mul (Fe.sub x3 z3) a
    let cb := Fe.mul (Fe.add x3 z3) b
    x3 := Fe.sq (Fe.add da cb)
    z3 := Fe.mul x1 (Fe.sq (Fe.sub da cb))
    x2 := Fe.mul aa bb
    z2 := Fe.mul e (Fe.add aa (Fe.mul a24 e))
  if swapped then
    x2 := x3
    z2 := z3
  return Fe.toBytes (Fe.mul x2 (Fe.invert z2))

/-- What is sent to the other side: `secret` times the base point, whose coordinate is 9. -/
def public_ (secret : ByteArray) : ByteArray :=
  multiply secret (Hex.decode "0900000000000000000000000000000000000000000000000000000000000000")

end X25519
