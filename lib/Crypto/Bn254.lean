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

/-- Is `order` times the point the point at infinity? The same multiplication as `g2Scale`, in coordinates
(X/Z², Y/Z³) that need no division: of a point that came off the wire, only this is asked. -/
def g2InSubgroup (a : G2) : Bool := Id.run do
  if a.infinite then
    return true
  let mut x := Fq2.one
  let mut y := Fq2.one
  let mut z := Fq2.zero
  let mut i := 256
  while i > 0 do
    i := i - 1
    -- double
    if !(z.isZero) then
      if y.isZero then
        z := Fq2.zero
      else
        let xx := Fq2.mul x x
        let yy := Fq2.mul y y
        let yyyy := Fq2.mul yy yy
        let t := Fq2.add x yy
        let d0 := Fq2.sub (Fq2.sub (Fq2.mul t t) xx) yyyy
        let d := Fq2.add d0 d0
        let e := Fq2.add (Fq2.add xx xx) xx
        let x3 := Fq2.sub (Fq2.mul e e) (Fq2.add d d)
        let c2 := Fq2.add yyyy yyyy
        let c4 := Fq2.add c2 c2
        let y3 := Fq2.sub (Fq2.mul e (Fq2.sub d x3)) (Fq2.add c4 c4)
        let yz := Fq2.mul y z
        x := x3
        y := y3
        z := Fq2.add yz yz
    if (order[i / 32]! >>> (i % 32).toUInt64) &&& 1 == 1 then
      -- add the point itself (whose Z is 1)
      if z.isZero then
        x := a.x
        y := a.y
        z := Fq2.one
      else
        let zz := Fq2.mul z z
        let u2 := Fq2.mul a.x zz
        let s2 := Fq2.mul a.y (Fq2.mul z zz)
        if Fq2.same x u2 then
          if Fq2.same y s2 then
            -- the same point: this would be a doubling, which the order's bits never ask for of a
            -- point in the subgroup; leave it to the slow, general routine
            return (g2Scale order a).infinite
          z := Fq2.zero
        else
          let h := Fq2.sub u2 x
          let r := Fq2.sub s2 y
          let hh := Fq2.mul h h
          let hhh := Fq2.mul h hh
          let v := Fq2.mul x hh
          let x3 := Fq2.sub (Fq2.sub (Fq2.mul r r) hhh) (Fq2.add v v)
          let y3 := Fq2.sub (Fq2.mul r (Fq2.sub v x3)) (Fq2.mul y hhh)
          z := Fq2.mul h z
          x := x3
          y := y3
  return z.isZero

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
  if !(g2InSubgroup q) then
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

/-- The same power, bit by bit: three thousand squarings. Kept as the plain statement of what `finalPower` computes. -/
def finalPowerSlow (x : Fq12) : Fq12 := Id.run do
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

-- The same power in a few hundred multiplications. (p¹² − 1)/order = (p⁶ − 1)·(p² + 1)·(p⁴ − p² + 1)/order.
-- Raising to a power of p is a symmetry of the field ("Frobenius"), linear in the twelve coefficients, so
-- it costs one multiplication's worth; the first two factors are done that way. What they leave has its
-- inverse for the asking (it is the image under the p⁶ symmetry), and the last factor then unfolds into
-- three powers by the curve's 63-bit parameter and a short chain of products.

/-- `x` to the power `e` (eight 32-bit digits). -/
def pow12 (x : Fq12) (e : Mont.Num) : Fq12 := Id.run do
  let mut result := one12
  let mut started := false
  let mut i := 256
  while i > 0 do
    i := i - 1
    if started then
      result := mul12 result result
    if (e[i / 32]! >>> (i % 32).toUInt64) &&& 1 == 1 then
      result := if started then mul12 result x else x
      started := true
  return result

/-- 1, s, s², ..., s¹¹. -/
def powersOf (s : Fq12) : Array Fq12 := Id.run do
  let mut out : Array Fq12 := Array.emptyWithCapacity 12
  let mut power := one12
  for _ in [0:12] do
    out := out.push power
    power := mul12 power s
  return out

/-- The image of `x` under the symmetry that sends `w` to `s`, given the powers of `s`. -/
def mapBy (powers : Array Fq12) (x : Fq12) : Fq12 := Id.run do
  let mut out : Fq12 := Array.replicate 12 Mont.zero
  for i in [0:12] do
    let c := x[i]!
    if !(Mont.isZero c) then
      let column := powers[i]!
      for j in [0:12] do
        if !(Mont.isZero column[j]!) then
          out := out.set! j (fadd out[j]! (fmul c column[j]!))
  return out

/-- Where `w` goes when everything is raised to the power p, p² and p³ (as the powers of its image). -/
def frobenius1 : Array Fq12 := powersOf (pow12 ((Array.replicate 12 Mont.zero).set! 1 one) p)
def frobenius2 : Array Fq12 := powersOf (mapBy frobenius1 frobenius1[1]!)
def frobenius3 : Array Fq12 := powersOf (mapBy frobenius1 frobenius2[1]!)

/-- Raising to the power p⁶ sends `w` to `−w`: the odd coefficients change sign. -/
def conj12 (x : Fq12) : Fq12 := Id.run do
  let mut out : Fq12 := Array.emptyWithCapacity 12
  for i in [0:12] do
    out := out.push (if i % 2 == 1 then fneg x[i]! else x[i]!)
  return out

/-- `x` times `w`. -/
def timesW (x : Fq12) : Fq12 := Id.run do
  let top := x[11]!
  let mut out : Fq12 := Array.emptyWithCapacity 12
  out := out.push (fneg (fmul top eightyTwo))
  for i in [0:11] do
    out := out.push (if i == 5 then fadd x[i]! (fmul top eighteen) else x[i]!)
  return out

/-- 1/x, by solving `x·y = 1` for the twelve coefficients of `y` (twelve equations, by elimination).
All zeros for `x = 0`. -/
def inv12 (x : Fq12) : Fq12 := Id.run do
  -- 12 rows of 13 numbers: row i holds coefficient i of x, x·w, ..., x·w¹¹, and then of 1
  let mut m : Array Fq := Array.replicate 156 Mont.zero
  let mut column := x
  for j in [0:12] do
    for i in [0:12] do
      m := m.set! (13 * i + j) column[i]!
    column := timesW column
  m := m.set! 12 one
  for c in [0:12] do
    let mut pivot := c
    while pivot < 12 && Mont.isZero m[13 * pivot + c]! do
      pivot := pivot + 1
    if pivot == 12 then
      return Array.replicate 12 Mont.zero
    if pivot != c then
      for k in [0:13] do
        let t := m[13 * c + k]!
        m := m.set! (13 * c + k) m[13 * pivot + k]!
        m := m.set! (13 * pivot + k) t
    let scale := finv m[13 * c + c]!
    for k in [c:13] do
      m := m.set! (13 * c + k) (fmul m[13 * c + k]! scale)
    for r in [0:12] do
      let factor := m[13 * r + c]!
      if r != c && !(Mont.isZero factor) then
        for k in [c:13] do
          m := m.set! (13 * r + k) (fsub m[13 * r + k]! (fmul factor m[13 * c + k]!))
  let mut out : Fq12 := Array.emptyWithCapacity 12
  for i in [0:12] do
    out := out.push m[13 * i + 12]!
  return out

/-- `x` to the power of the curve's parameter, 4965661367192848881. -/
def powParameter (x : Fq12) : Fq12 := pow12 x #[0x4A6909F1, 0x44E992B4, 0, 0, 0, 0, 0, 0]

def finalPower (x : Fq12) : Fq12 :=
  -- to the power (p⁶ − 1)(p² + 1)
  let t := mul12 (conj12 x) (inv12 x)
  let t := mul12 (mapBy frobenius2 t) t
  -- and to (p⁴ − p² + 1)/order
  let fp := mapBy frobenius1 t
  let fp2 := mapBy frobenius2 t
  let fp3 := mapBy frobenius3 t
  let fu := powParameter t
  let fu2 := powParameter fu
  let fu3 := powParameter fu2
  let y0 := mul12 (mul12 fp fp2) fp3
  let y1 := conj12 t
  let y2 := mapBy frobenius2 fu2
  let y3 := conj12 (mapBy frobenius1 fu)
  let y4 := conj12 (mul12 fu (mapBy frobenius1 fu2))
  let y5 := conj12 fu2
  let y6 := conj12 (mul12 fu3 (mapBy frobenius1 fu3))
  let t0 := mul12 (mul12 (mul12 y6 y6) y4) y5
  let t1 := mul12 (mul12 y3 y5) t0
  let t0 := mul12 t0 y2
  let t1 := mul12 (mul12 t1 t1) t0
  let t1 := mul12 t1 t1
  let t0 := mul12 t1 y1
  let t1 := mul12 t1 y0
  mul12 (mul12 t0 t0) t1

/-- The inverses of several pairs with a single division (the product of all is inverted, and each
one's inverse recovered from it). Empty if one of them is zero. -/
def invertAll (xs : Array Fq2) : Array Fq2 := Id.run do
  -- a pair's inverse is its conjugate over its norm, a plain number: those are what gets inverted
  let mut norms : Array Fq := Array.emptyWithCapacity xs.size
  let mut running : Array Fq := Array.emptyWithCapacity xs.size
  let mut product := one
  for x in xs do
    let norm := fadd (fmul x.a x.a) (fmul x.b x.b)
    if Mont.isZero norm then
      return Array.emptyWithCapacity 0
    norms := norms.push norm
    running := running.push product
    product := fmul product norm
  let mut inverse := finv product
  let mut out : Array Fq2 := Array.replicate xs.size Fq2.zero
  let mut k := xs.size
  while k > 0 do
    k := k - 1
    let normInverse := fmul inverse running[k]!
    inverse := fmul inverse norms[k]!
    out := out.set! k ⟨fmul xs[k]!.a normInverse, fneg (fmul xs[k]!.b normInverse)⟩
  return out

/-- The line of slope `m` through the point `(x, y)` of the twist, evaluated at `(px, py)` (see `line`). -/
def lineOfSlope (m x y : Fq2) (px py : Fq) : Fq12 :=
  let zero12 : Fq12 := Array.replicate 12 Mont.zero
  addAt (addAt (zero12.set! 0 (fneg py)) 1 (Fq2.scale m px)) 3 (Fq2.sub y (Fq2.mul m x))

/-- One step of the loop for every pair at once: multiplies `f` by each pair's line through its running
point `ts[k]` and `others[k]` (the tangent, with `tangent`), and moves each running point along its
line. The slopes need a division each; they are all had from one (`invertAll`). Returns nothing new
if some line is vertical, which the caller then does the slow way. -/
def stepAll (f : Fq12) (ts others : Array G2) (pxs pys : Array Fq) (tangent : Bool) : Fq12 × Array G2 := Id.run do
  let mut bottoms : Array Fq2 := Array.emptyWithCapacity ts.size
  for k in [0:ts.size] do
    bottoms := bottoms.push (if tangent then Fq2.add ts[k]!.y ts[k]!.y else Fq2.sub others[k]!.x ts[k]!.x)
  let inverses := invertAll bottoms
  if inverses.size != ts.size then
    return (f, Array.emptyWithCapacity 0)
  let mut g := f
  let mut next : Array G2 := Array.emptyWithCapacity ts.size
  for k in [0:ts.size] do
    let t := ts[k]!
    let o := others[k]!
    let top := if tangent then
        let xx := Fq2.mul t.x t.x
        Fq2.add (Fq2.add xx xx) xx
      else Fq2.sub o.y t.y
    let m := Fq2.mul top inverses[k]!
    g := mul12 g (lineOfSlope m t.x t.y pxs[k]! pys[k]!)
    let x3 := Fq2.sub (Fq2.sub (Fq2.mul m m) t.x) (if tangent then t.x else o.x)
    next := next.push ⟨x3, Fq2.sub (Fq2.mul m (Fq2.sub t.x x3)) t.y, false⟩
  return (g, next)

/-- The loops of all the pairs, run together: `f` is squared once per step for all of them. -/
def millerAll (qs : Array G2) (pxs pys : Array Fq) : Fq12 := Id.run do
  let count : UInt64 := 0x9D797039BE763BA8
  let mut f := one12
  let mut ts := qs
  let mut i := 64
  while i > 0 do
    i := i - 1
    f := mul12 f f
    let (g, doubled) := stepAll f ts ts pxs pys true
    if doubled.size != ts.size then
      -- (a point with y = 0: not one that passed the subgroup check; the pairs one by one, then)
      let mut slow := one12
      for k in [0:qs.size] do
        slow := mul12 slow (miller qs[k]! pxs[k]! pys[k]!)
      return slow
    f := g
    ts := doubled
    if (count >>> i.toUInt64) &&& 1 == 1 then
      let (g, added) := stepAll f ts qs pxs pys false
      if added.size != ts.size then
        let mut slow := one12
        for k in [0:qs.size] do
          slow := mul12 slow (miller qs[k]! pxs[k]! pys[k]!)
        return slow
      f := g
      ts := added
  -- the two closing steps, with each point moved by the field's symmetry once and twice
  for k in [0:qs.size] do
    let q := qs[k]!
    let q1 : G2 := ⟨Fq2.mul (Fq2.conj q.x) twistX, Fq2.mul (Fq2.conj q.y) twistY, false⟩
    let q2 : G2 := ⟨Fq2.mul q.x (Fq2.mul twistX (Fq2.conj twistX)), q.y, false⟩
    f := mul12 f (line ts[k]! q1 pxs[k]! pys[k]!)
    f := mul12 f (line (g2Add ts[k]! q1) q2 pxs[k]! pys[k]!)
  return f

/-- Is the product of the pairings of these pairs 1? `input` is pairs of a point of the curve (64 bytes)
and a point of the twist (128 bytes). Returns 1 or 0, or 2 if a point is not valid. -/
def pairingCheck (input : ByteArray) (big : Bool) : Nat := Id.run do
  let mut qs : Array G2 := Array.emptyWithCapacity 4
  let mut pxs : Array Fq := Array.emptyWithCapacity 4
  let mut pys : Array Fq := Array.emptyWithCapacity 4
  for k in [0:input.size / 192] do
    match g1OfBytes input (192 * k) big, g2OfBytes input (192 * k + 64) big with
    | some g, some q =>
      -- (a pair with a point at infinity pairs to 1)
      if !(Mont.isZero g.z) && !q.infinite then
        let (px, py) := g1Affine g
        qs := qs.push q
        pxs := pxs.push px
        pys := pys.push py
    | _, _ => return 2
  if qs.size == 0 then
    return 1
  return if isOne12 (finalPower (millerAll qs pxs pys)) then 1 else 0

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
