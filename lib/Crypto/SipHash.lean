import Solana.Wire

/-!
# SipHash-1-3

A keyed hash of 64 bits: one round per eight bytes of input, three at the
end. The chain uses it, with a key of zero, to spread an epoch's stake
rewards over blocks (`Solana.Epoch`).
-/

namespace SipHash

def rotl (x b : UInt64) : UInt64 := (x <<< b) ||| (x >>> (64 - b))

/-- One round on the four words of state. -/
def round (v : Array UInt64) : Array UInt64 :=
  let a := v[0]! + v[1]!
  let b := rotl v[1]! 13 ^^^ a
  let c := v[2]! + v[3]!
  let d := rotl v[3]! 16 ^^^ c
  let e := rotl a 32 + d
  let f := c + b
  #[e, rotl b 17 ^^^ f, rotl f 32, rotl d 21 ^^^ e]

def hash13 (k0 k1 : UInt64) (data : ByteArray) : UInt64 := Id.run do
  let mut v : Array UInt64 := #[k0 ^^^ 0x736f6d6570736575, k1 ^^^ 0x646f72616e646f6d, k0 ^^^ 0x6c7967656e657261, k1 ^^^ 0x7465646279746573]
  let whole := data.size / 8
  -- the last word: the bytes left over, and the length in its top byte
  let mut last := data.size.toUInt64 <<< 56
  for i in [8 * whole:data.size] do
    last := last ||| (data[i]!.toUInt64 <<< (8 * (i - 8 * whole)).toUInt64)
  for i in [0:whole + 1] do
    let m := if i == whole then last else Wire.u64 data (8 * i)
    v := round (v.set! 3 (v[3]! ^^^ m))
    v := v.set! 0 (v[0]! ^^^ m)
  v := round (round (round (v.set! 2 (v[2]! ^^^ 0xff))))
  return v[0]! ^^^ v[1]! ^^^ v[2]! ^^^ v[3]!

end SipHash
