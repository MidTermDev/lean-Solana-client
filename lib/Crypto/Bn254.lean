import Crypto.Mont
import Encoding.Hex

/-!
# The alt_bn128 curve and its pairing

BN254, the curve Ethereum's precompiles made the standard for zero-knowledge
proofs: programs on Solana verify Groth16 proofs with it, through a system
call that adds points, multiplies them, and checks a product of pairings.

A pairing takes a point of the curve and a point of its "twist" (the same
curve over a field of pairs of numbers) to a number in a field twelve times
as large, in such a way that multiplying either point multiplies the result's
exponent. A proof is accepted when a product of a few pairings is 1.

This is written to be right rather than fast: the twelve-fold field is
plain polynomials reduced modulo `w¹² − 18w⁶ + 82`, and the final
exponentiation is one long power. A check takes about half a second.
-/

namespace Bn254

abbrev Fq := Mont.Num

/-- The field's modulus, and the order of the group. -/
def p : Mont.Num := #[0xD87CFD47, 0x3C208C16, 0x6871CA8D, 0x97816A91, 0x8181585D, 0xB85045B6, 0xE131A029, 0x30644E72]
def order : Mont.Num := #[0xF0000001, 0x43E1F593, 0x79B97091, 0x2833E848, 0x8181585D, 0xB85045B6, 0xE131A029, 0x30644E72]
def fq : Mont.Field := Mont.Field.make p

def zero : Fq := Mont.zero
def fadd (a b : Fq) : Fq := Mont.addMod p a b
def fsub (a b : Fq) : Fq := Mont.subMod p a b
def fmul (a b : Fq) : Fq := Mont.mul fq a b
def fneg (a : Fq) : Fq := Mont.subMod p zero a
def finv (a : Fq) : Fq := Mont.inv fq a
def small (n : UInt64) : Fq := fq.enter #[n, 0, 0, 0, 0, 0, 0, 0]
def one : Fq := fq.one
def three : Fq := small 3

-- ------------------------------------------------- pairs of numbers: a + b·u, u² = −1

structure Fq2 where
  a : Fq
  b : Fq
  deriving Inhabited

namespace Fq2
def zero : Fq2 := ⟨Mont.zero, Mont.zero⟩
def one : Fq2 := ⟨Bn254.one, Mont.zero⟩
def isZero (x : Fq2) : Bool := Mont.isZero x.a && Mont.isZero x.b
def same (x y : Fq2) : Bool := Mont.same x.a y.a && Mont.same x.b y.b
def add (x y : Fq2) : Fq2 := ⟨fadd x.a y.a, fadd x.b y.b⟩
def sub (x y : Fq2) : Fq2 := ⟨fsub x.a y.a, fsub x.b y.b⟩
def neg (x : Fq2) : Fq2 := ⟨fneg x.a, fneg x.b⟩
def conj (x : Fq2) : Fq2 := ⟨x.a, fneg x.b⟩
def mul (x y : Fq2) : Fq2 := ⟨fsub (fmul x.a y.a) (fmul x.b y.b), fadd (fmul x.a y.b) (fmul x.b y.a)⟩
def scale (x : Fq2) (k : Fq) : Fq2 := ⟨fmul x.a k, fmul x.b k⟩
def inv (x : Fq2) : Fq2 :=
  let norm := finv (fadd (fmul x.a x.a) (fmul x.b x.b))
  ⟨fmul x.a norm, fneg (fmul x.b norm)⟩
def pow (x : Fq2) (e : Mont.Num) : Fq2 := Id.run do
  let mut result := one
  let mut i := 256
  while i > 0 do
    i := i - 1
    result := mul result result
    if (e[i / 32]! >>> (i % 32).toUInt64) &&& 1 == 1 then
      result := mul result x
  return result
end Fq2

/-- `ξ = 9 + u`: the twelve-fold field is built on a sixth root of it. -/
def xi : Fq2 := ⟨small 9, one⟩

-- ---------------------------------------------------------------- the curve: y² = x³ + 3

/-- A point of the curve in Jacobian coordinates (`z = 0`: the point at infinity). -/
structure G1 where
  x : Fq
  y : Fq
  z : Fq
  deriving Inhabited

def g1Infinity : G1 := ⟨one, one, Mont.zero⟩

def g1Double (a : G1) : G1 :=
  if Mont.isZero a.z || Mont.isZero a.y then g1Infinity
  else
    let xx := fmul a.x a.x
    let yy := fmul a.y a.y
    let yyyy := fmul yy yy
    let t := fadd a.x yy
    let d0 := fsub (fsub (fmul t t) xx) yyyy
    let d := fadd d0 d0
    let e := fadd (fadd xx xx) xx
    let x3 := fsub (fmul e e) (fadd d d)
    let c2 := fadd yyyy yyyy
    let c4 := fadd c2 c2
    let y3 := fsub (fmul e (fsub d x3)) (fadd c4 c4)
    let yz := fmul a.y a.z
    ⟨x3, y3, fadd yz yz⟩

def g1Add (a b : G1) : G1 :=
  if Mont.isZero a.z then b
  else if Mont.isZero b.z then a
  else
    let z1z1 := fmul a.z a.z
    let z2z2 := fmul b.z b.z
    let u1 := fmul a.x z2z2
    let u2 := fmul b.x z1z1
    let s1 := fmul a.y (fmul b.z z2z2)
    let s2 := fmul b.y (fmul a.z z1z1)
    if Mont.same u1 u2 then
      if Mont.same s1 s2 then g1Double a else g1Infinity
    else
      let h := fsub u2 u1
      let r := fsub s2 s1
      let hh := fmul h h
      let hhh := fmul h hh
      let v := fmul u1 hh
      let x3 := fsub (fsub (fmul r r) hhh) (fadd v v)
      ⟨x3, fsub (fmul r (fsub v x3)) (fmul s1 hhh), fmul h (fmul a.z b.z)⟩

/-- `k` times a point, `k` an ordinary 256-bit number. -/
def g1Scale (k : Mont.Num) (a : G1) : G1 := Id.run do
  let mut result := g1Infinity
  let mut i := 256
  while i > 0 do
    i := i - 1
    result := g1Double result
    if (k[i / 32]! >>> (i % 32).toUInt64) &&& 1 == 1 then
      result := g1Add result a
  return result

/-- A point from its 64 bytes (x then y, most significant byte first, or the reverse of each with `little`);
all zeros is the point at infinity. `none` if the coordinates are out of range or not on the curve.

The two top bits of `y`, which a number below the modulus never uses, are flags, as in the library Agave
reads points with: 0x40 says "the point at infinity" whatever the rest, 0x80 is ignored, both is an error.
Programs do pass points with these bits set. -/
def g1OfBytes (b : ByteArray) (o : Nat) (big : Bool) : Option G1 :=
  let x := Mont.ofBytes b o big
  let raw := Mont.ofBytes b (o + 32) big
  let flags := raw[7]! >>> 30
  let y := raw.set! 7 (raw[7]! &&& 0x3FFFFFFF)
  if Mont.isZero x && Mont.isZero raw then some g1Infinity
  else if flags == 3 || Mont.atLeast x p || Mont.atLeast y p then none
  else if flags == 1 then some g1Infinity
  else
    let mx := fq.enter x
    let my := fq.enter y
    if Mont.same (fmul my my) (fadd (fmul (fmul mx mx) mx) three) then some ⟨mx, my, one⟩ else none

/-- The affine coordinates of a point, in Montgomery form (zeros for the point at infinity). -/
def g1Affine (a : G1) : Fq × Fq :=
  if Mont.isZero a.z then (Mont.zero, Mont.zero)
  else
    let zi := finv a.z
    let zz := fmul zi zi
    (fmul a.x zz, fmul a.y (fmul zz zi))

def g1ToBytes (a : G1) (big : Bool) : ByteArray :=
  let (x, y) := g1Affine a
  Mont.toBytes (fq.leave x) big ++ Mont.toBytes (fq.leave y) big

-- ------------------------------------------- the twist: y² = x³ + 3/ξ over pairs of numbers

/-- A point of the twist, in ordinary coordinates. -/
structure G2 where
  x : Fq2
  y : Fq2
  infinite : Bool
  deriving Inhabited

def g2Infinity : G2 := ⟨Fq2.zero, Fq2.zero, true⟩

def twistB : Fq2 := Fq2.scale (Fq2.inv xi) three

def g2Double (a : G2) : G2 :=
  if a.infinite || a.y.isZero then g2Infinity
  else
    let xx := Fq2.mul a.x a.x
    let m := Fq2.mul (Fq2.add (Fq2.add xx xx) xx) (Fq2.inv (Fq2.add a.y a.y))
    let x3 := Fq2.sub (Fq2.mul m m) (Fq2.add a.x a.x)
    ⟨x3, Fq2.sub (Fq2.mul m (Fq2.sub a.x x3)) a.y, false⟩

def g2Add (a b : G2) : G2 :=
  if a.infinite then b
  else if b.infinite then a
  else if Fq2.same a.x b.x then
    if Fq2.same a.y b.y then g2Double a else g2Infinity
  else
    let m := Fq2.mul (Fq2.sub b.y a.y) (Fq2.inv (Fq2.sub b.x a.x))
    let x3 := Fq2.sub (Fq2.sub (Fq2.mul m m) a.x) b.x
    ⟨x3, Fq2.sub (Fq2.mul m (Fq2.sub a.x x3)) a.y, false⟩

def g2Scale (k : Mont.Num) (a : G2) : G2 := Id.run do
  let mut result := g2Infinity
  let mut i := 256
  while i > 0 do
    i := i - 1
    result := g2Double result
    if (k[i / 32]! >>> (i % 32).toUInt64) &&& 1 == 1 then
      result := g2Add result a
  return result

/-- A point of the twist from its 128 bytes, in Ethereum's order: for x and then for y, the `u` part first.
`none` if out of range, off the curve, or not in the subgroup the pairing is defined on. -/
def g2OfBytes (b : ByteArray) (o : Nat) (big : Bool) : Option G2 := Id.run do
  let mut parts : Array Mont.Num := Array.emptyWithCapacity 4
  let mut allZero := true
  -- the flags (see `g1OfBytes`) are the top bits of the `u` part of y
  let flagged := if big then 2 else 3
  let mut flags : UInt64 := 0
  for i in [0:4] do
    let mut v := Mont.ofBytes b (o + 32 * i) big
    if !(Mont.isZero v) then
      allZero := false
    if i == flagged then
      flags := v[7]! >>> 30
      v := v.set! 7 (v[7]! &&& 0x3FFFFFFF)
    if Mont.atLeast v p then
      return none
    parts := parts.push (fq.enter v)
  if allZero then
    return some g2Infinity
  if flags == 3 then
    return none
  if flags == 1 then
    return some g2Infinity
  -- most significant first: (x.u, x.1, y.u, y.1); least significant first: (x.1, x.u, y.1, y.u)
  let x : Fq2 := if big then ⟨parts[1]!, parts[0]!⟩ else ⟨parts[0]!, parts[1]!⟩
  let y : Fq2 := if big then ⟨parts[3]!, parts[2]!⟩ else ⟨parts[2]!, parts[3]!⟩
  if !(Fq2.same (Fq2.mul y y) (Fq2.add (Fq2.mul (Fq2.mul x x) x) twistB)) then
    return none
  let q : G2 := ⟨x, y, false⟩
  if !(g2Scale order q).infinite then
    return none
  return some q

-- ---------------------------------- twelve numbers: polynomials in w, with w¹² = 18·w⁶ − 82

abbrev Fq12 := Array Fq

def one12 : Fq12 := Id.run do
  let mut a : Fq12 := Array.replicate 12 Mont.zero
  a := a.set! 0 one
  return a

def eighteen : Fq := small 18
def eightyTwo : Fq := small 82
def nine : Fq := small 9

def mul12 (x y : Fq12) : Fq12 := Id.run do
  let mut c : Array Fq := Array.replicate 23 Mont.zero
  for i in [0:12] do
    if !(Mont.isZero x[i]!) then
      for j in [0:12] do
        if !(Mont.isZero y[j]!) then
          c := c.set! (i + j) (fadd c[i + j]! (fmul x[i]! y[j]!))
  -- w¹² = 18·w⁶ − 82, from the top down
  let mut k := 23
  while k > 12 do
    k := k - 1
    let top := c[k]!
    if !(Mont.isZero top) then
      c := c.set! (k - 6) (fadd c[k - 6]! (fmul top eighteen))
      c := c.set! (k - 12) (fsub c[k - 12]! (fmul top eightyTwo))
  let mut out : Fq12 := Array.emptyWithCapacity 12
  for i in [0:12] do
    out := out.push c[i]!
  return out

def isOne12 (x : Fq12) : Bool := Id.run do
  if !(Mont.same x[0]! one) then
    return false
  for i in [1:12] do
    if !(Mont.isZero x[i]!) then
      return false
  return true

/-- Adds `z·wᵏ` to `x`, for a pair `z = a + b·u`: since `u = w⁶ − 9`, that is `(a − 9b)·wᵏ + b·wᵏ⁺⁶`. -/
def addAt (x : Fq12) (k : Nat) (z : Fq2) : Fq12 :=
  let x1 := x.set! k (fadd x[k]! (fsub z.a (fmul nine z.b)))
  x1.set! (k + 6) (fadd x1[k + 6]! z.b)

/-- The line through two points of the twist (the tangent, if they are the same), evaluated at a point of
the curve `(px, py)`, as a number of the twelve-fold field. A point of the twist `(x, y)` stands for
`(x·w², y·w³)` there, which is where the powers of `w` below come from. -/
def line (a b : G2) (px py : Fq) : Fq12 := Id.run do
  let zero12 : Fq12 := Array.replicate 12 Mont.zero
  let vertical := Fq2.same a.x b.x && !(Fq2.same a.y b.y)
  if vertical then
    -- px − x·w²
    let x := zero12.set! 0 px
    return addAt x 2 (Fq2.neg a.x)
  let m := if Fq2.same a.x b.x then
      let xx := Fq2.mul a.x a.x
      Fq2.mul (Fq2.add (Fq2.add xx xx) xx) (Fq2.inv (Fq2.add a.y a.y))
    else Fq2.mul (Fq2.sub b.y a.y) (Fq2.inv (Fq2.sub b.x a.x))
  -- −py + (m·px)·w + (y − m·x)·w³
  let x := zero12.set! 0 (fneg py)
  return addAt (addAt x 1 (Fq2.scale m px)) 3 (Fq2.sub a.y (Fq2.mul m a.x))

/-- (p − 1)/3 and (p − 1)/2: the powers of `ξ` by which the field's own symmetry moves a point of the twist. -/
def thirdOfPMinus1 : Mont.Num := #[0x4829A9C2, 0x69602EB2, 0xCD7B4384, 0xDD2B2385, 0x808072C9, 0xE81AC1E7, 0xA065E00D, 0x10216F7B]
def halfOfPMinus1 : Mont.Num := #[0x6C3E7EA3, 0x9E10460B, 0xB438E546, 0xCBC0B548, 0x40C0AC2E, 0xDC2822DB, 0x7098D014, 0x18322739]
def twistX : Fq2 := Fq2.pow xi thirdOfPMinus1
def twistY : Fq2 := Fq2.pow xi halfOfPMinus1

/-- The loop of the pairing ("Miller's loop") for one pair of points. -/
def miller (q : G2) (px py : Fq) : Fq12 := Id.run do
  -- 6x + 2 for the curve's parameter x: its top bit is implied, these are the 64 below it
  let count : UInt64 := 0x9D797039BE763BA8
  let mut f := one12
  let mut t := q
  let mut i := 64
  while i > 0 do
    i := i - 1
    f := mul12 (mul12 f f) (line t t px py)
    t := g2Double t
    if (count >>> i.toUInt64) &&& 1 == 1 then
      f := mul12 f (line t q px py)
      t := g2Add t q
  -- two more steps with the point moved by the field's symmetry, once and twice
  let q1 : G2 := ⟨Fq2.mul (Fq2.conj q.x) twistX, Fq2.mul (Fq2.conj q.y) twistY, false⟩
  let q2 : G2 := ⟨Fq2.mul q.x (Fq2.mul twistX (Fq2.conj twistX)), q.y, false⟩
  f := mul12 f (line t q1 px py)
  t := g2Add t q1
  return mul12 f (line t q2 px py)

/-- (p¹² − 1) / order: the power that turns the loop's result into the pairing. -/
def finalExponent : ByteArray := Hex.decode "2f4b6dc97020fddadf107d20bc842d43bf6369b1ff6a1c71015f3f7be2e1e30a73bb94fec0daf15466b2383a5d3ec3d15ad524d8f70c54efee1bd8c3b21377e563a09a1b705887e72eceaddea3790364a61f676baaf977870e88d5c6c8fef0781361e443ae77f5b63a2a2264487f2940a8b1ddb3d15062cd0fb2015dfc6668449aed3cc48a82d0d602d268c7daab6a41294c0cc4ebe5664568dfc50e1648a45a4a1e3a5195846a3ed011a337a02088ec80e0ebae8755cfe107acf3aafb40494e406f804216bb10cf430b0f37856b42db8dc5514724ee93dfb10826f0dd4a0364b9580291d2cd65664814fde37ca80bb4ea44eacc5e641bbadf423f9a2cbf813b8d145da90029baee7ddadda71c7f3811c4105262945bba1668c3be69a3c230974d83561841d766f9c9d570bb7fbe04c7e8a6c3c760c0de81def35692da361102b6b9b2b918837fa97896e84abb40a4efb7e54523a486964b64ca86f120"

def finalPower (x : Fq12) : Fq12 := Id.run do
  let e := finalExponent
  let mut result := one12
  let mut started := false
  for byte in e do
    for k in [0:8] do
      if started then
        result := mul12 result result
      if (byte >>> (7 - k).toUInt8) &&& 1 == 1 then
        result := if started then mul12 result x else x
        started := true
  return result

/-- Is the product of the pairings of these pairs 1? `input` is pairs of a point of the curve (64 bytes)
and a point of the twist (128 bytes). Returns 1 or 0, or 2 if a point is not valid. -/
def pairingCheck (input : ByteArray) (big : Bool) : Nat := Id.run do
  let mut f := one12
  for k in [0:input.size / 192] do
    match g1OfBytes input (192 * k) big, g2OfBytes input (192 * k + 64) big with
    | some g, some q =>
      if !(Mont.isZero g.z) && !q.infinite then
        let (px, py) := g1Affine g
        f := mul12 f (miller q px py)
    | _, _ => return 2
  return if isOne12 (finalPower f) then 1 else 0

-- ------------------------------------------------------- points in half the bytes

/-- A square root in the base field, if there is one (the modulus is 3 modulo 4: it is a power). -/
def fsqrt (a : Fq) : Option Fq :=
  let exponent : Mont.Num := #[0xB61F3F52, 0x4F082305, 0x5A1C72A3, 0x65E05AA4, 0xA0605617, 0x6E14116D, 0xB84C680A, 0x0C19139C]
  let r := Mont.pow fq a exponent
  if Mont.same (fmul r r) a then some r else none

/-- A square root of a pair, if there is one. -/
def sqrt2 (a : Fq2) : Option Fq2 := Id.run do
  if Mont.isZero a.b then
    -- a plain number: its root is plain, or (when it has none) a multiple of u, since u² = −1
    match fsqrt a.a with
    | some r => return some ⟨r, Mont.zero⟩
    | none =>
      match fsqrt (fneg a.a) with
      | some r => return some ⟨Mont.zero, r⟩
      | none => return none
  match fsqrt (fadd (fmul a.a a.a) (fmul a.b a.b)) with
  | none => return none
  | some alpha =>
    let half := finv (small 2)
    let mut real := fsqrt (fmul (fadd a.a alpha) half)
    if real.isNone then
      real := fsqrt (fmul (fsub a.a alpha) half)
    match real with
    | none => return none
    | some r =>
      let root : Fq2 := ⟨r, fmul a.b (finv (fadd r r))⟩
      return if Fq2.same (Fq2.mul root root) a then some root else none

/-- Is a number larger than its negative? (Of a point's two possible `y`, this tells which one it has.) -/
def isLarger (y : Fq) : Bool := !(Mont.atLeast (fq.leave (fneg y)) (fq.leave y))

def isLarger2 (y : Fq2) : Bool :=
  if Mont.isZero y.b then isLarger y.a else isLarger y.b

/-- A number below the modulus from 32 bytes (most significant first) whose top `skip` bits are something
else, in Montgomery form. -/
def fieldOf (b : ByteArray) (o : Nat) (skip : Bool) : Option Fq :=
  let raw := Mont.ofBytes b o true
  let v := if skip then raw.set! 7 (raw[7]! &&& 0x3FFFFFFF) else raw
  if Mont.atLeast v p then none else some (fq.enter v)

def bytesOf (a : Fq) : ByteArray := Mont.toBytes (fq.leave a) true

def allZero (b : ByteArray) : Bool := Id.run do
  for x in b do
    if x != 0 then
      return false
  return true

def zeroBytes (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    out := out.push 0
  return out

/-- The four conversions of `sol_alt_bn128_compression`, most significant byte first: a point of the curve
to 32 bytes (0) and back (1), a point of the twist to 64 bytes (2) and back (3). The short form is `x` with
two flags in its top bits: 0x80 = `y` is the larger of the two candidates, 0x40 = the point at infinity.
Nothing is checked beyond what is needed to convert (a point going in need not be on the curve). Empty if
the input cannot be converted. -/
def convert (op : Nat) (input : ByteArray) : ByteArray := Id.run do
  let wide := op >= 2
  let part := if wide then 64 else 32
  let pack := op == 0 || op == 2
  if input.size != (if pack then 2 * part else part) then
    return ByteArray.empty
  if allZero input then
    return zeroBytes (if pack then part else 2 * part)
  -- the flags sit in the top bits of the last number read: `y` going in whole, `x` going in short
  let flagAt := if pack then part else 0
  let flags := input[flagAt]! >>> 6
  if flags == 3 then
    return ByteArray.empty
  let mut numbers : Array Fq := Array.emptyWithCapacity 4
  for i in [0:input.size / 32] do
    match fieldOf input (32 * i) (32 * i == flagAt) with
    | none => return ByteArray.empty
    | some v => numbers := numbers.push v
  if pack then
    if flags == 1 then
      return (zeroBytes part).set! 0 0x40
    let larger := if wide then isLarger2 ⟨numbers[3]!, numbers[2]!⟩ else isLarger numbers[1]!
    let out := input.extract 0 part
    return out.set! 0 (out[0]! ||| (if larger then 0x80 else 0))
  else
    if flags == 1 then
      return zeroBytes (2 * part)
    if wide then
      let x : Fq2 := ⟨numbers[1]!, numbers[0]!⟩
      match sqrt2 (Fq2.add (Fq2.mul (Fq2.mul x x) x) twistB) with
      | none => return ByteArray.empty
      | some root =>
        let y := if isLarger2 root == (flags == 2) then root else Fq2.neg root
        return bytesOf x.b ++ bytesOf x.a ++ bytesOf y.b ++ bytesOf y.a
    else
      let x := numbers[0]!
      match fsqrt (fadd (fmul (fmul x x) x) three) with
      | none => return ByteArray.empty
      | some root =>
        let y := if isLarger root == (flags == 2) then root else fneg root
        return bytesOf x ++ bytesOf y

end Bn254
