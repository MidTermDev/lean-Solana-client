import Fast
import Crypto.Sha512
import Encoding.Hex

/-!
# Ed25519 (RFC 8032), strict verification

Solana signs everything with Ed25519: transactions, gossip records, pings.
This file implements the curve from scratch: field arithmetic modulo
p = 2^255 - 19, the twisted Edwards group law in extended coordinates,
point (de)compression, scalar reduction modulo the group order, signing and
verification.

Verification follows the *strict* rules Solana validators apply
(`ed25519-dalek`'s `verify_strict`): the scalar `S` must be canonical and
neither the public key nor `R` may be a small-order point.

Field elements are ten limbs in radix 2^26. Using 26-bit limbs keeps every
intermediate product inside a `UInt64`, so the code needs no 128-bit
arithmetic and runs unchanged under the official Lean toolchain and leanc.
Since ten limbs hold 260 bits, the wrap-around constant is
2^260 mod p = 2^5 * 19 = 608.
-/

namespace Ed25519

/-- An element of GF(2^255 - 19): `l0 + l1*2^26 + ... + l9*2^234`.
Invariant maintained by every operation: each limb is below `2^26 + 2^14`. -/
structure Fe where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64
  l4 : UInt64
  l5 : UInt64
  l6 : UInt64
  l7 : UInt64
  l8 : UInt64
  l9 : UInt64
  deriving Inhabited

namespace Fe

def mask26 : UInt64 := 0x3ffffff

def zero : Fe := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
def one : Fe := ⟨1, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

/-- Propagates carries and folds the overflow above 2^260 back in (times 608).
Accepts limbs up to about 2^62 and restores the limb invariant. -/
def carry (r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : UInt64) : Fe :=
  let r1 := r1 + (r0 >>> 26)
  let r2 := r2 + (r1 >>> 26)
  let r3 := r3 + (r2 >>> 26)
  let r4 := r4 + (r3 >>> 26)
  let r5 := r5 + (r4 >>> 26)
  let r6 := r6 + (r5 >>> 26)
  let r7 := r7 + (r6 >>> 26)
  let r8 := r8 + (r7 >>> 26)
  let r9 := r9 + (r8 >>> 26)
  let top := r9 >>> 26
  let t0 := (r0 &&& mask26) + 608 * top
  let t1 := (r1 &&& mask26) + (t0 >>> 26)
  ⟨t0 &&& mask26, t1, r2 &&& mask26, r3 &&& mask26, r4 &&& mask26, r5 &&& mask26, r6 &&& mask26, r7 &&& mask26, r8 &&& mask26, r9 &&& mask26⟩

def add (a b : Fe) : Fe :=
  carry (a.l0 + b.l0) (a.l1 + b.l1) (a.l2 + b.l2) (a.l3 + b.l3) (a.l4 + b.l4) (a.l5 + b.l5) (a.l6 + b.l6) (a.l7 + b.l7) (a.l8 + b.l8) (a.l9 + b.l9)

/-- `a - b`. Adds a multiple of p whose limbs all exceed 2^27 first, so no
limb can underflow. -/
def sub (a b : Fe) : Fe :=
  carry (a.l0 + 0xbfffb2d - b.l0) (a.l1 + 0xbfffffd - b.l1) (a.l2 + 0xbfffffd - b.l2) (a.l3 + 0xbfffffd - b.l3) (a.l4 + 0xbfffffd - b.l4)
    (a.l5 + 0xbfffffd - b.l5) (a.l6 + 0xbfffffd - b.l6) (a.l7 + 0xbfffffd - b.l7) (a.l8 + 0xbfffffd - b.l8) (a.l9 + 0x81ffffd - b.l9)

def neg (a : Fe) : Fe := sub zero a

/-- Schoolbook 10x10 multiplication. Each of the 19 column sums stays below
2^56; the upper nine are carried and folded into the lower ten. -/
def mul (a b : Fe) : Fe :=
  let a0 := a.l0
  let a1 := a.l1
  let a2 := a.l2
  let a3 := a.l3
  let a4 := a.l4
  let a5 := a.l5
  let a6 := a.l6
  let a7 := a.l7
  let a8 := a.l8
  let a9 := a.l9
  let b0 := b.l0
  let b1 := b.l1
  let b2 := b.l2
  let b3 := b.l3
  let b4 := b.l4
  let b5 := b.l5
  let b6 := b.l6
  let b7 := b.l7
  let b8 := b.l8
  let b9 := b.l9
  let c0 := a0 * b0
  let c1 := a0 * b1 + a1 * b0
  let c2 := a0 * b2 + a1 * b1 + a2 * b0
  let c3 := a0 * b3 + a1 * b2 + a2 * b1 + a3 * b0
  let c4 := a0 * b4 + a1 * b3 + a2 * b2 + a3 * b1 + a4 * b0
  let c5 := a0 * b5 + a1 * b4 + a2 * b3 + a3 * b2 + a4 * b1 + a5 * b0
  let c6 := a0 * b6 + a1 * b5 + a2 * b4 + a3 * b3 + a4 * b2 + a5 * b1 + a6 * b0
  let c7 := a0 * b7 + a1 * b6 + a2 * b5 + a3 * b4 + a4 * b3 + a5 * b2 + a6 * b1 + a7 * b0
  let c8 := a0 * b8 + a1 * b7 + a2 * b6 + a3 * b5 + a4 * b4 + a5 * b3 + a6 * b2 + a7 * b1 + a8 * b0
  let c9 := a0 * b9 + a1 * b8 + a2 * b7 + a3 * b6 + a4 * b5 + a5 * b4 + a6 * b3 + a7 * b2 + a8 * b1 + a9 * b0
  let c10 := a1 * b9 + a2 * b8 + a3 * b7 + a4 * b6 + a5 * b5 + a6 * b4 + a7 * b3 + a8 * b2 + a9 * b1
  let c11 := a2 * b9 + a3 * b8 + a4 * b7 + a5 * b6 + a6 * b5 + a7 * b4 + a8 * b3 + a9 * b2
  let c12 := a3 * b9 + a4 * b8 + a5 * b7 + a6 * b6 + a7 * b5 + a8 * b4 + a9 * b3
  let c13 := a4 * b9 + a5 * b8 + a6 * b7 + a7 * b6 + a8 * b5 + a9 * b4
  let c14 := a5 * b9 + a6 * b8 + a7 * b7 + a8 * b6 + a9 * b5
  let c15 := a6 * b9 + a7 * b8 + a8 * b7 + a9 * b6
  let c16 := a7 * b9 + a8 * b8 + a9 * b7
  let c17 := a8 * b9 + a9 * b8
  let c18 := a9 * b9
  let c11 := c11 + (c10 >>> 26)
  let c12 := c12 + (c11 >>> 26)
  let c13 := c13 + (c12 >>> 26)
  let c14 := c14 + (c13 >>> 26)
  let c15 := c15 + (c14 >>> 26)
  let c16 := c16 + (c15 >>> 26)
  let c17 := c17 + (c16 >>> 26)
  let c18 := c18 + (c17 >>> 26)
  let c19 := c18 >>> 26
  carry (c0 + 608 * (c10 &&& mask26)) (c1 + 608 * (c11 &&& mask26)) (c2 + 608 * (c12 &&& mask26))
    (c3 + 608 * (c13 &&& mask26)) (c4 + 608 * (c14 &&& mask26)) (c5 + 608 * (c15 &&& mask26))
    (c6 + 608 * (c16 &&& mask26)) (c7 + 608 * (c17 &&& mask26)) (c8 + 608 * (c18 &&& mask26)) (c9 + 608 * c19)

/-- Squaring: the same column sums with the symmetric products doubled. -/
def sq (a : Fe) : Fe :=
  let a0 := a.l0
  let a1 := a.l1
  let a2 := a.l2
  let a3 := a.l3
  let a4 := a.l4
  let a5 := a.l5
  let a6 := a.l6
  let a7 := a.l7
  let a8 := a.l8
  let a9 := a.l9
  let d0 := a0 * 2
  let d1 := a1 * 2
  let d2 := a2 * 2
  let d3 := a3 * 2
  let d4 := a4 * 2
  let d5 := a5 * 2
  let d6 := a6 * 2
  let d7 := a7 * 2
  let d8 := a8 * 2
  let c0 := a0 * a0
  let c1 := d0 * a1
  let c2 := d0 * a2 + a1 * a1
  let c3 := d0 * a3 + d1 * a2
  let c4 := d0 * a4 + d1 * a3 + a2 * a2
  let c5 := d0 * a5 + d1 * a4 + d2 * a3
  let c6 := d0 * a6 + d1 * a5 + d2 * a4 + a3 * a3
  let c7 := d0 * a7 + d1 * a6 + d2 * a5 + d3 * a4
  let c8 := d0 * a8 + d1 * a7 + d2 * a6 + d3 * a5 + a4 * a4
  let c9 := d0 * a9 + d1 * a8 + d2 * a7 + d3 * a6 + d4 * a5
  let c10 := d1 * a9 + d2 * a8 + d3 * a7 + d4 * a6 + a5 * a5
  let c11 := d2 * a9 + d3 * a8 + d4 * a7 + d5 * a6
  let c12 := d3 * a9 + d4 * a8 + d5 * a7 + a6 * a6
  let c13 := d4 * a9 + d5 * a8 + d6 * a7
  let c14 := d5 * a9 + d6 * a8 + a7 * a7
  let c15 := d6 * a9 + d7 * a8
  let c16 := d7 * a9 + a8 * a8
  let c17 := d8 * a9
  let c18 := a9 * a9
  let c11 := c11 + (c10 >>> 26)
  let c12 := c12 + (c11 >>> 26)
  let c13 := c13 + (c12 >>> 26)
  let c14 := c14 + (c13 >>> 26)
  let c15 := c15 + (c14 >>> 26)
  let c16 := c16 + (c15 >>> 26)
  let c17 := c17 + (c16 >>> 26)
  let c18 := c18 + (c17 >>> 26)
  let c19 := c18 >>> 26
  carry (c0 + 608 * (c10 &&& mask26)) (c1 + 608 * (c11 &&& mask26)) (c2 + 608 * (c12 &&& mask26))
    (c3 + 608 * (c13 &&& mask26)) (c4 + 608 * (c14 &&& mask26)) (c5 + 608 * (c15 &&& mask26))
    (c6 + 608 * (c16 &&& mask26)) (c7 + 608 * (c17 &&& mask26)) (c8 + 608 * (c18 &&& mask26)) (c9 + 608 * c19)

/-- `a^(2^n)`. -/
def sqn (a : Fe) (n : Nat) : Fe := Id.run do
  let mut r := a
  for _ in [0:n] do
    r := sq r
  return r

/-- `a^(2^250 - 1)`, the shared prefix of the inversion and square-root chains. -/
def pow250 (a : Fe) : Fe :=
  let a2 := sq a
  let a9 := mul a (sqn a2 2)
  let a11 := mul a2 a9
  let x5 := mul a9 (sq a11)
  let x10 := mul (sqn x5 5) x5
  let x20 := mul (sqn x10 10) x10
  let x40 := mul (sqn x20 20) x20
  let x50 := mul (sqn x40 10) x10
  let x100 := mul (sqn x50 50) x50
  let x200 := mul (sqn x100 100) x100
  mul (sqn x200 50) x50

/-- `a^(p - 2) = a^(2^255 - 21)`: the inverse, by Fermat. -/
def invert (a : Fe) : Fe :=
  let a2 := sq a
  let a9 := mul a (sqn a2 2)
  let a11 := mul a2 a9
  mul (sqn (pow250 a) 5) a11

/-- `a^((p - 5) / 8) = a^(2^252 - 3)`, used to take square roots. -/
def pow22523 (a : Fe) : Fe := mul (sqn (pow250 a) 2) a

def le64 (b : ByteArray) (o : Nat) : UInt64 :=
  b[o]!.toUInt64 ||| (b[o + 1]!.toUInt64 <<< 8) ||| (b[o + 2]!.toUInt64 <<< 16) |||
    (b[o + 3]!.toUInt64 <<< 24) ||| (b[o + 4]!.toUInt64 <<< 32) ||| (b[o + 5]!.toUInt64 <<< 40) |||
    (b[o + 6]!.toUInt64 <<< 48) ||| (b[o + 7]!.toUInt64 <<< 56)

/-- Decodes 32 little-endian bytes, ignoring the top bit (bit 255). -/
def fromBytes (b : ByteArray) : Fe :=
  let w0 := le64 b 0
  let w1 := le64 b 8
  let w2 := le64 b 16
  let w3 := le64 b 24 &&& 0x7fffffffffffffff
  ⟨w0 &&& mask26,
   (w0 >>> 26) &&& mask26,
   ((w0 >>> 52) ||| (w1 <<< 12)) &&& mask26,
   (w1 >>> 14) &&& mask26,
   ((w1 >>> 40) ||| (w2 <<< 24)) &&& mask26,
   (w2 >>> 2) &&& mask26,
   (w2 >>> 28) &&& mask26,
   ((w2 >>> 54) ||| (w3 <<< 10)) &&& mask26,
   (w3 >>> 16) &&& mask26,
   (w3 >>> 42) &&& mask26⟩

/-- The canonical 32-byte little-endian encoding (fully reduced modulo p). -/
def toBytes (a : Fe) : ByteArray := Id.run do
  -- strict carry chain: every limb below 2^26
  let mut l : Array UInt64 := #[a.l0, a.l1, a.l2, a.l3, a.l4, a.l5, a.l6, a.l7, a.l8, a.l9]
  for i in [0:9] do
    l := l.set! (i + 1) (l[i + 1]! + (l[i]! >>> 26))
    l := l.set! i (l[i]! &&& mask26)
  -- bits 255 and up wrap around times 19
  let top := l[9]! >>> 21
  l := l.set! 0 (l[0]! + 19 * top)
  l := l.set! 9 (l[9]! &&& 0x1fffff)
  for i in [0:9] do
    l := l.set! (i + 1) (l[i + 1]! + (l[i]! >>> 26))
    l := l.set! i (l[i]! &&& mask26)
  -- now the value is below 2p; q = 1 exactly when it is at least p
  let mut q := (l[0]! + 19) >>> 26
  for i in [1:9] do
    q := (l[i]! + q) >>> 26
  q := (l[9]! + q) >>> 21
  l := l.set! 0 (l[0]! + 19 * q)
  for i in [0:9] do
    l := l.set! (i + 1) (l[i + 1]! + (l[i]! >>> 26))
    l := l.set! i (l[i]! &&& mask26)
  l := l.set! 9 (l[9]! &&& 0x1fffff)
  -- pack 10 x 26 bits into bytes
  let mut out := ByteArray.emptyWithCapacity 32
  let mut acc : UInt64 := 0
  let mut nbits : UInt64 := 0
  for i in [0:10] do
    acc := acc ||| (l[i]! <<< nbits)
    nbits := nbits + 26
    while nbits >= 8 && out.size < 32 do
      out := out.push acc.toUInt8
      acc := acc >>> 8
      nbits := nbits - 8
  return out

def isZero (a : Fe) : Bool := Id.run do
  let b := toBytes a
  let mut acc : UInt8 := 0
  for x in b do
    acc := acc ||| x
  return acc == 0

def eq (a b : Fe) : Bool := isZero (sub a b)

/-- "Negative" means the canonical encoding is odd (RFC 8032, section 5.1.2). -/
def isNegative (a : Fe) : Bool := (toBytes a)[0]! &&& 1 == 1

end Fe

/-- The curve constant d = -121665/121666. -/
def d : Fe := Fe.fromBytes (Hex.decode "a3785913ca4deb75abd841414d0a700098e879777940c78c73fe6f2bee6c0352")
def d2 : Fe := Fe.add d d
/-- A square root of -1 modulo p. -/
def sqrtM1 : Fe := Fe.fromBytes (Hex.decode "b0a00e4a271beec478e42fad0618432fa7d7fb3d99004d2b0bdfc14f8024832b")

/-- A curve point in extended coordinates: x = X/Z, y = Y/Z, T = XY/Z. -/
structure Point where
  x : Fe
  y : Fe
  z : Fe
  t : Fe
  deriving Inhabited

namespace Point

def identity : Point := ⟨Fe.zero, Fe.one, Fe.one, Fe.zero⟩

/-- Unified addition (RFC 8032, section 5.1.4). -/
def add (p q : Point) : Point :=
  let a := Fe.mul (Fe.sub p.y p.x) (Fe.sub q.y q.x)
  let b := Fe.mul (Fe.add p.y p.x) (Fe.add q.y q.x)
  let c := Fe.mul (Fe.mul p.t d2) q.t
  let zz := Fe.mul p.z q.z
  let dd := Fe.add zz zz
  let e := Fe.sub b a
  let f := Fe.sub dd c
  let g := Fe.add dd c
  let h := Fe.add b a
  ⟨Fe.mul e f, Fe.mul g h, Fe.mul f g, Fe.mul e h⟩

/-- Doubling (RFC 8032, section 5.1.4). -/
def dbl (p : Point) : Point :=
  let a := Fe.sq p.x
  let b := Fe.sq p.y
  let zz := Fe.sq p.z
  let c := Fe.add zz zz
  let h := Fe.add a b
  let xy := Fe.add p.x p.y
  let e := Fe.sub h (Fe.sq xy)
  let g := Fe.sub a b
  let f := Fe.add c g
  ⟨Fe.mul e f, Fe.mul g h, Fe.mul f g, Fe.mul e h⟩

def neg (p : Point) : Point := ⟨Fe.neg p.x, p.y, p.z, Fe.neg p.t⟩

/-- The 32-byte compressed encoding: y with the sign of x in the top bit. -/
def encode (p : Point) : ByteArray :=
  let zi := Fe.invert p.z
  let x := Fe.mul p.x zi
  let y := Fe.mul p.y zi
  let out := Fe.toBytes y
  let sign : UInt8 := if Fe.isNegative x then 0x80 else 0
  out.set! 31 (out[31]! ||| sign)

/-- Decompression: recovers x from y by solving x^2 = (y^2 - 1) / (d y^2 + 1).
Returns `none` when the bytes are not a point on the curve. -/
def decode (b : ByteArray) : Option Point :=
  if b.size != 32 then none
  else
    let y := Fe.fromBytes b
    let yy := Fe.sq y
    let u := Fe.sub yy Fe.one
    let v := Fe.add (Fe.mul d yy) Fe.one
    let v3 := Fe.mul (Fe.sq v) v
    let v7 := Fe.mul (Fe.sq v3) v
    let x := Fe.mul (Fe.mul u v3) (Fe.pow22523 (Fe.mul u v7))
    let vxx := Fe.mul v (Fe.sq x)
    let wantNeg := b[31]! >>> 7 == 1
    if Fe.eq vxx u then
      let x := if Fe.isNegative x != wantNeg then Fe.neg x else x
      some ⟨x, y, Fe.one, Fe.mul x y⟩
    else if Fe.eq vxx (Fe.neg u) then
      let x := Fe.mul x sqrtM1
      let x := if Fe.isNegative x != wantNeg then Fe.neg x else x
      some ⟨x, y, Fe.one, Fe.mul x y⟩
    else none

/-- Is the number `a` (below p = 2²⁵⁵ − 19, as four 64-bit words, least significant first) a square of
something other than zero? By the Jacobi symbol, which needs only halvings, subtractions and a look at
the low bits: far cheaper than raising `a` to a power, which is the other way to tell. -/
def isSquare (w0 w1 w2 w3 : UInt64) : Bool := Id.run do
  let mut a0 := Fast.hot w0
  let mut a1 := w1
  let mut a2 := w2
  let mut a3 := w3
  let mut n0 : UInt64 := Fast.hot 0xFFFFFFFFFFFFFFED
  let mut n1 : UInt64 := 0xFFFFFFFFFFFFFFFF
  let mut n2 : UInt64 := 0xFFFFFFFFFFFFFFFF
  let mut n3 : UInt64 := 0x7FFFFFFFFFFFFFFF
  -- the symbol so far: true for +1
  let mut plus := true
  for _ in [0:1200] do
    if a0 ||| a1 ||| a2 ||| a3 == 0 then
      break
    if a0 &&& 1 == 0 then
      -- (2/n) is −1 when n is 3 or 5 modulo 8
      a0 := (a0 >>> 1) ||| (a1 <<< 63)
      a1 := (a1 >>> 1) ||| (a2 <<< 63)
      a2 := (a2 >>> 1) ||| (a3 <<< 63)
      a3 := a3 >>> 1
      let r := n0 &&& 7
      if r == 3 || r == 5 then
        plus := !plus
    else
      -- both odd: the larger first (swapping flips the sign when both are 3 modulo 4), then subtract
      let less := if a3 != n3 then a3 < n3 else if a2 != n2 then a2 < n2 else if a1 != n1 then a1 < n1 else a0 < n0
      if less then
        if a0 &&& 3 == 3 && n0 &&& 3 == 3 then
          plus := !plus
        let t0 := a0
        let t1 := a1
        let t2 := a2
        let t3 := a3
        a0 := n0
        a1 := n1
        a2 := n2
        a3 := n3
        n0 := t0
        n1 := t1
        n2 := t2
        n3 := t3
      let b0 : UInt64 := if a0 < n0 then 1 else 0
      let b1 : UInt64 := if a1 < n1 || (a1 == n1 && b0 == 1) then 1 else 0
      let b2 : UInt64 := if a2 < n2 || (a2 == n2 && b1 == 1) then 1 else 0
      a0 := a0 - n0
      a1 := a1 - n1 - b0
      a2 := a2 - n2 - b1
      a3 := a3 - n3 - b2
  return plus && n0 == 1 && n1 ||| n2 ||| n3 == 0

/-- Are these 32 bytes a point of the curve? The same answer as `(decode b).isSome`, without finding the
point: there is an `x` exactly when (y² − 1)/(d·y² + 1) is zero or a square, and a quotient is a square
when the product is. -/
def isOnCurve (b : ByteArray) : Bool :=
  if b.size != 32 then false
  else
    let y := Fe.fromBytes b
    let yy := Fe.sq y
    let u := Fe.sub yy Fe.one
    let v := Fe.add (Fe.mul d yy) Fe.one
    let product := Fe.toBytes (Fe.mul u v)
    let w0 := Fast.le64 product 0
    let w1 := Fast.le64 product 8
    let w2 := Fast.le64 product 16
    let w3 := Fast.le64 product 24
    w0 ||| w1 ||| w2 ||| w3 == 0 || isSquare w0 w1 w2 w3

/-- True when 8P is the identity, i.e. P lies in the small torsion subgroup. -/
def isSmallOrder (p : Point) : Bool :=
  let q := dbl (dbl (dbl p))
  Fe.isZero q.x && Fe.eq q.y q.z

/-- Multiples 0P .. 15P, for 4-bit windowed scalar multiplication. -/
def table (p : Point) : Array Point := Id.run do
  let mut t : Array Point := Array.emptyWithCapacity 16
  t := t.push identity
  for i in [1:16] do
    t := t.push (add t[i - 1]! p)
  return t

end Point

/-! Ristretto: the same curve with its cofactor divided out, so that every 32-byte encoding names
exactly one element of a group of prime order (RFC 9496). The elements are points as above; only how
they are written down differs. -/
namespace Ristretto

def invSqrtAMinusD : Fe := Fe.fromBytes (Hex.decode "ea405d80aafdc899be72415a17162f9d40d801fe917bc216a2fcafcf05896c78")

/-- The square root of `u / v` if it has one (then `true`), else of `i · u / v`; never the negative one. -/
def sqrtRatio (u v : Fe) : Bool × Fe :=
  let v3 := Fe.mul (Fe.sq v) v
  let r := Fe.mul (Fe.mul u v3) (Fe.pow22523 (Fe.mul u (Fe.mul (Fe.sq v3) v)))
  let check := Fe.mul v (Fe.sq r)
  let flipped := Fe.eq check (Fe.neg u)
  let root := if flipped || Fe.eq check (Fe.neg (Fe.mul u sqrtM1)) then Fe.mul sqrtM1 r else r
  (Fe.eq check u || flipped, if Fe.isNegative root then Fe.neg root else root)

def decode (b : ByteArray) : Option Point :=
  let s := Fe.fromBytes b
  if b.size != 32 || Fe.toBytes s != b || Fe.isNegative s then none
  else
    let u1 := Fe.sub Fe.one (Fe.sq s)
    let u2 := Fe.add Fe.one (Fe.sq s)
    let v := Fe.sub (Fe.neg (Fe.mul d (Fe.sq u1))) (Fe.sq u2)
    let (square, inverse) := sqrtRatio Fe.one (Fe.mul v (Fe.sq u2))
    let twice := Fe.mul (Fe.add s s) (Fe.mul inverse u2)
    let x := if Fe.isNegative twice then Fe.neg twice else twice
    let y := Fe.mul u1 (Fe.mul (Fe.mul inverse (Fe.mul inverse u2)) v)
    if !square || Fe.isNegative (Fe.mul x y) || Fe.isZero y then none else some ⟨x, y, Fe.one, Fe.mul x y⟩

def encode (p : Point) : ByteArray :=
  let u1 := Fe.mul (Fe.add p.z p.y) (Fe.sub p.z p.y)
  let u2 := Fe.mul p.x p.y
  let (_, inverse) := sqrtRatio Fe.one (Fe.mul u1 (Fe.sq u2))
  let den1 := Fe.mul inverse u1
  let den2 := Fe.mul inverse u2
  let zInverse := Fe.mul (Fe.mul den1 den2) p.t
  let rotate := Fe.isNegative (Fe.mul p.t zInverse)
  let x := if rotate then Fe.mul p.y sqrtM1 else p.x
  let y := if rotate then Fe.mul p.x sqrtM1 else p.y
  let s := Fe.mul (if rotate then Fe.mul den1 invSqrtAMinusD else den2) (Fe.sub p.z (if Fe.isNegative (Fe.mul x zInverse) then Fe.neg y else y))
  Fe.toBytes (if Fe.isNegative s then Fe.neg s else s)

end Ristretto

/-- The base point B: y = 4/5 with x positive. -/
def basePoint : Point :=
  match Point.decode (Hex.decode "5866666666666666666666666666666666666666666666666666666666666666") with
  | some p => p
  | none => Point.identity

def baseTable : Array Point := Point.table basePoint

/-- The `i`-th 4-bit digit of a little-endian scalar. -/
def nibble (s : ByteArray) (i : Nat) : Nat :=
  let b := s[i / 2]!
  if i % 2 == 0 then (b &&& 15).toNat else (b >>> 4).toNat

/-- `[s]P + [k]Q` with one shared doubling chain (Straus' trick), given the
window tables of P and Q. Scalars are 32 little-endian bytes. -/
def doubleScalarMul (s : ByteArray) (tp : Array Point) (k : ByteArray) (tq : Array Point) : Point := Id.run do
  let mut r := Point.identity
  for i in [0:64] do
    let j := 63 - i
    r := Point.dbl (Point.dbl (Point.dbl (Point.dbl r)))
    let ns := nibble s j
    let nk := nibble k j
    if ns != 0 then
      r := Point.add r tp[ns]!
    if nk != 0 then
      r := Point.add r tq[nk]!
  return r

/-- `[s]B` for the base point. -/
def scalarMulBase (s : ByteArray) : Point := Id.run do
  let mut r := Point.identity
  for i in [0:64] do
    let j := 63 - i
    r := Point.dbl (Point.dbl (Point.dbl (Point.dbl r)))
    let ns := nibble s j
    if ns != 0 then
      r := Point.add r baseTable[ns]!
  return r

-- ------------------------------------------------------------------ scalars
--
-- The group order L = 2^252 + 27742317777372353535851937790883648493,
-- as four little-endian 64-bit words.

def l0 : UInt64 := 0x5812631a5cf5d3ed
def l1 : UInt64 := 0x14def9dea2f79cd6
def l3 : UInt64 := 0x1000000000000000

/-- `r >= L` for a 256-bit value given as four words. -/
def geL (r0 r1 r2 r3 : UInt64) : Bool :=
  if r3 != l3 then r3 > l3
  else if r2 != 0 then true
  else if r1 != l1 then r1 > l1
  else r0 >= l0

def words (r0 r1 r2 r3 : UInt64) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity 32
  for w in #[r0, r1, r2, r3] do
    for i in [0:8] do
      out := out.push (w >>> (i.toUInt64 * 8)).toUInt8
  return out

/-- Reduces a little-endian integer of any length modulo L, one bit at a time. -/
def scReduce (h : ByteArray) : ByteArray := Id.run do
  let mut r0 : UInt64 := 0
  let mut r1 : UInt64 := 0
  let mut r2 : UInt64 := 0
  let mut r3 : UInt64 := 0
  let nbits := h.size * 8
  for i in [0:nbits] do
    let bit := nbits - 1 - i
    let b := ((h[bit / 8]! >>> (bit % 8).toUInt8) &&& 1).toUInt64
    -- r := 2r + b   (r < L < 2^253, so this fits in 256 bits)
    r3 := (r3 <<< 1) ||| (r2 >>> 63)
    r2 := (r2 <<< 1) ||| (r1 >>> 63)
    r1 := (r1 <<< 1) ||| (r0 >>> 63)
    r0 := (r0 <<< 1) ||| b
    if geL r0 r1 r2 r3 then
      -- r := r - L, with borrows
      let b0 : UInt64 := if r0 < l0 then 1 else 0
      let t1 := r1 - l1
      let b1 : UInt64 := if r1 < l1 || t1 < b0 then 1 else 0
      let b2 : UInt64 := if r2 < b1 then 1 else 0
      r0 := r0 - l0
      r1 := t1 - b0
      r2 := r2 - b1
      r3 := r3 - l3 - b2
  return words r0 r1 r2 r3

/-- A canonical scalar is one already reduced modulo L. -/
def scIsCanonical (s : ByteArray) : Bool :=
  !(geL (Fe.le64 s 0) (Fe.le64 s 8) (Fe.le64 s 16) (Fe.le64 s 24))

/-- `(a * b + c) mod L` for 32-byte little-endian scalars. -/
def scMulAdd (a b c : ByteArray) : ByteArray := Id.run do
  -- schoolbook product over bytes: column sums stay far below 2^64
  let mut acc : Array UInt64 := Array.replicate 65 0
  for i in [0:32] do
    for j in [0:32] do
      acc := acc.set! (i + j) (acc[i + j]! + a[i]!.toUInt64 * b[j]!.toUInt64)
  for i in [0:32] do
    acc := acc.set! i (acc[i]! + c[i]!.toUInt64)
  let mut out := ByteArray.emptyWithCapacity 64
  let mut carry : UInt64 := 0
  for i in [0:64] do
    let v := acc[i]! + carry
    out := out.push v.toUInt8
    carry := v >>> 8
  return scReduce out

-- ---------------------------------------------------------------- signatures

/-- Strict Ed25519 verification of `sig` (64 bytes) over `msg` under `pk` (32 bytes). -/
def verify (pk sig msg : ByteArray) : Bool := Id.run do
  if pk.size != 32 || sig.size != 64 then
    return false
  let rBytes := sig.extract 0 32
  let sBytes := sig.extract 32 64
  if !(scIsCanonical sBytes) then
    return false
  match Point.decode pk with
  | none => return false
  | some a =>
    match Point.decode rBytes with
    | none => return false
    | some r =>
      if Point.isSmallOrder a || Point.isSmallOrder r then
        return false
      let k := scReduce (Sha512.hash (rBytes ++ pk ++ msg))
      -- accept iff [S]B - [k]A encodes to R
      let rr := doubleScalarMul sBytes baseTable k (Point.table (Point.neg a))
      return Point.encode rr == rBytes

/-- The secret scalar and nonce prefix derived from a 32-byte seed. -/
def expandSeed (seed : ByteArray) : ByteArray × ByteArray :=
  let h := Sha512.hash seed
  let a := h.extract 0 32
  let a := a.set! 0 (a[0]! &&& 248)
  let a := a.set! 31 ((a[31]! &&& 127) ||| 64)
  (a, h.extract 32 64)

/-- The 32-byte public key for a 32-byte seed. -/
def publicKey (seed : ByteArray) : ByteArray :=
  Point.encode (scalarMulBase (expandSeed seed).1)

/-- Signs `msg`; `pk` must be `publicKey seed`. Returns the 64-byte signature. -/
def sign (seed pk msg : ByteArray) : ByteArray :=
  let (a, pref) := expandSeed seed
  let r := scReduce (Sha512.hash (pref ++ msg))
  let rEnc := Point.encode (scalarMulBase r)
  let k := scReduce (Sha512.hash (rEnc ++ pk ++ msg))
  rEnc ++ scMulAdd k a r

end Ed25519
