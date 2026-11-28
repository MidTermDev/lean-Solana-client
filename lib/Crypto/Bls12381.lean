import Fast
import Crypto.Sha256
import Encoding.Hex

/-!
# The BLS12-381 curve, its pairing, and signatures that add up

Under Alpenglow validators sign their votes with BLS signatures. A key is a
point of a curve, a signature is a point of the curve's "twist" (the same
curve over pairs of numbers), and both add: the sum of many validators'
signatures of one message is a signature of it by the sum of their keys. So
one check, two pairings, tells whether two thirds of the stake voted.

A pairing takes a point of the curve and a point of the twist to a number in
a field twelve times as large, so that multiplying either point multiplies
the result's exponent. A signature `s` of a message by the key `k` is good
when the pairing of `k` with the message's point equals the pairing of the
curve's generator with `s`.

This is written to be small: one kind of point serves both curves (a point
of the plain curve is a point over pairs whose second halves are zero), and
the twelve-fold field is plain polynomials in `w` over pairs, `w⁶ = 1 + u`.
A check takes a few tens of milliseconds.
-/

namespace Bls12381

-- ------------------------------------------------- numbers modulo p (381 bits)

/-- Six 64-bit words, least significant first. Numbers are kept in Montgomery form: multiplied by 2³⁸⁴. -/
abbrev Fp := Array UInt64

def p : Fp := #[0xb9feffffffffaaab, 0x1eabfffeb153ffff, 0x6730d2a0f6b0f624, 0x64774b84f38512bf, 0x4b1ba7b6434bacd7, 0x1a0111ea397fe69a]

def zero : Fp := Array.replicate 6 0

def isZero (a : Fp) : Bool := a[0]! ||| a[1]! ||| a[2]! ||| a[3]! ||| a[4]! ||| a[5]! == 0

def same (a b : Fp) : Bool := Id.run do
  for i in [0:6] do
    if a[i]! != b[i]! then
      return false
  return true

/-- `a ≥ b`. -/
def atLeast (a b : Fp) : Bool := Id.run do
  let mut i := 6
  while i > 0 do
    i := i - 1
    if a[i]! != b[i]! then
      return a[i]! > b[i]!
  return true

/-- `a − b`, for `a ≥ b`. -/
def subRaw (a b : Fp) : Fp := Id.run do
  let mut out : Fp := Array.emptyWithCapacity 6
  let mut borrow : UInt64 := 0
  for i in [0:6] do
    out := out.push (a[i]! - b[i]! - borrow)
    borrow := Fast.bit (a[i]! < b[i]! || (a[i]! == b[i]! && borrow == 1))
  return out

def fadd (a b : Fp) : Fp := Id.run do
  -- (p has three bits to spare in its top word: the sum cannot overflow)
  let mut out : Fp := Array.emptyWithCapacity 6
  let mut carry : UInt64 := 0
  for i in [0:6] do
    let s := a[i]! + b[i]!
    out := out.push (s + carry)
    carry := Fast.bit (s < a[i]! || s + carry < s)
  return if atLeast out p then subRaw out p else out

def fsub (a b : Fp) : Fp := if atLeast a b then subRaw a b else subRaw p (subRaw b a)
def fneg (a : Fp) : Fp := if isZero a then a else subRaw p a

/-- The Montgomery product: `x × y / 2³⁸⁴` modulo p. One round per word of `y`; a carry out of an
addition is seen by the sum being smaller than what was added. -/
def fmul (x y : Fp) : Fp := Id.run do
  let x0 := x[0]!
  let x1 := x[1]!
  let x2 := x[2]!
  let x3 := x[3]!
  let x4 := x[4]!
  let x5 := x[5]!
  let mut t0 : UInt64 := 0
  let mut t1 : UInt64 := 0
  let mut t2 : UInt64 := 0
  let mut t3 : UInt64 := 0
  let mut t4 : UInt64 := 0
  let mut t5 : UInt64 := 0
  for i in [0:6] do
    let b := y[i]!
    -- add `x` times this word of `y`
    let l0 := x0 * b
    let s0 := t0 + l0
    let c0 := Fast.mulHi x0 b + Fast.bit (s0 < l0)
    let l1 := x1 * b
    let u1 := t1 + l1
    let s1 := u1 + c0
    let c1 := Fast.mulHi x1 b + Fast.bit (u1 < l1) + Fast.bit (s1 < c0)
    let l2 := x2 * b
    let u2 := t2 + l2
    let s2 := u2 + c1
    let c2 := Fast.mulHi x2 b + Fast.bit (u2 < l2) + Fast.bit (s2 < c1)
    let l3 := x3 * b
    let u3 := t3 + l3
    let s3 := u3 + c2
    let c3 := Fast.mulHi x3 b + Fast.bit (u3 < l3) + Fast.bit (s3 < c2)
    let l4 := x4 * b
    let u4 := t4 + l4
    let s4 := u4 + c3
    let c4 := Fast.mulHi x4 b + Fast.bit (u4 < l4) + Fast.bit (s4 < c3)
    let l5 := x5 * b
    let u5 := t5 + l5
    let s5 := u5 + c4
    let c5 := Fast.mulHi x5 b + Fast.bit (u5 < l5) + Fast.bit (s5 < c4)
    -- add the multiple of p that makes the lowest word zero, and drop that word
    let q := s0 * 0x89f3fffcfffcfffd
    let m0 := q * 0xb9feffffffffaaab
    let d0 := Fast.mulHi q 0xb9feffffffffaaab + Fast.bit (s0 + m0 < m0)
    let m1 := q * 0x1eabfffeb153ffff
    let v1 := s1 + m1
    let r1 := v1 + d0
    let d1 := Fast.mulHi q 0x1eabfffeb153ffff + Fast.bit (v1 < m1) + Fast.bit (r1 < d0)
    let m2 := q * 0x6730d2a0f6b0f624
    let v2 := s2 + m2
    let r2 := v2 + d1
    let d2 := Fast.mulHi q 0x6730d2a0f6b0f624 + Fast.bit (v2 < m2) + Fast.bit (r2 < d1)
    let m3 := q * 0x64774b84f38512bf
    let v3 := s3 + m3
    let r3 := v3 + d2
    let d3 := Fast.mulHi q 0x64774b84f38512bf + Fast.bit (v3 < m3) + Fast.bit (r3 < d2)
    let m4 := q * 0x4b1ba7b6434bacd7
    let v4 := s4 + m4
    let r4 := v4 + d3
    let d4 := Fast.mulHi q 0x4b1ba7b6434bacd7 + Fast.bit (v4 < m4) + Fast.bit (r4 < d3)
    let m5 := q * 0x1a0111ea397fe69a
    let v5 := s5 + m5
    let r5 := v5 + d4
    let d5 := Fast.mulHi q 0x1a0111ea397fe69a + Fast.bit (v5 < m5) + Fast.bit (r5 < d4)
    t0 := r1
    t1 := r2
    t2 := r3
    t3 := r4
    t4 := r5
    t5 := c5 + d5
  let r : Fp := #[t0, t1, t2, t3, t4, t5]
  return if atLeast r p then subRaw r p else r

/-- A number below p, into Montgomery form and back. -/
def enter (a : Fp) : Fp :=
  fmul a #[0xf4df1f341c341746, 0x0a76e6a609d104f1, 0x8de5476c4c95b6d5, 0x67eb88a9939d83c0, 0x9a793e85b519952d, 0x11988fe592cae3aa]
def leave (a : Fp) : Fp := fmul a #[1, 0, 0, 0, 0, 0]

def small (n : UInt64) : Fp := enter #[n, 0, 0, 0, 0, 0]
def minus (n : UInt64) : Fp := fneg (small n)
def one : Fp := small 1

/-- `a` to the power `e` (an ordinary number, in words). -/
def fpow (a : Fp) (e : Array UInt64) : Fp := Id.run do
  let mut r := one
  let mut i := 64 * e.size
  while i > 0 do
    i := i - 1
    r := fmul r r
    if (e[i / 64]! >>> (i % 64).toUInt64) &&& 1 == 1 then
      r := fmul r a
  return r

/-- The inverse: the power `p − 2`. -/
def finv (a : Fp) : Fp := fpow a (p.set! 0 (p[0]! - 2))

/-- A square root, if there is one: p is 3 modulo 4, so it is the power `(p + 1)/4`. -/
def fsqrt (a : Fp) : Option Fp :=
  let r := fpow a #[0xee7fbfffffffeaab, 0x07aaffffac54ffff, 0xd9cc34a83dac3d89, 0xd91dd2e13ce144af, 0x92c6e9ed90d2eb35, 0x0680447a8e5ff9a6]
  if same (fmul r r) a then some r else none

/-- The `n` bytes at `o`, most significant first, as a number (not in Montgomery form). -/
def number (b : ByteArray) (o n : Nat) : Fp := Id.run do
  let mut w := zero
  for i in [0:n] do
    let k := n - 1 - i
    w := w.set! (k / 8) (w[k / 8]! ||| (b[o + i]!.toUInt64 <<< (8 * (k % 8)).toUInt64))
  return w

/-- A number below p from 48 bytes whose top three bits are something else. -/
def fieldOf (b : ByteArray) (o : Nat) : Option Fp :=
  let raw := number b o 48
  let v := raw.set! 5 (raw[5]! &&& 0x1FFFFFFFFFFFFFFF)
  if atLeast v p then none else some (enter v)

def bytesOf (a : Fp) : ByteArray := Id.run do
  let v := leave a
  let mut out := ByteArray.emptyWithCapacity 48
  for i in [0:48] do
    out := out.push (v[(47 - i) / 8]! >>> (8 * ((47 - i) % 8)).toUInt64).toUInt8
  return out

-- ------------------------------------------------- pairs of numbers: a + b·u, u² = −1

structure Fp2 where
  a : Fp
  b : Fp
  deriving Inhabited

namespace Fp2
def zero : Fp2 := ⟨Bls12381.zero, Bls12381.zero⟩
def one : Fp2 := ⟨Bls12381.one, Bls12381.zero⟩
def isZero (x : Fp2) : Bool := Bls12381.isZero x.a && Bls12381.isZero x.b
def same (x y : Fp2) : Bool := Bls12381.same x.a y.a && Bls12381.same x.b y.b
def add (x y : Fp2) : Fp2 := ⟨fadd x.a y.a, fadd x.b y.b⟩
def sub (x y : Fp2) : Fp2 := ⟨fsub x.a y.a, fsub x.b y.b⟩
def neg (x : Fp2) : Fp2 := ⟨fneg x.a, fneg x.b⟩
def conj (x : Fp2) : Fp2 := ⟨x.a, fneg x.b⟩
def twice (x : Fp2) : Fp2 := add x x
def thrice (x : Fp2) : Fp2 := add (add x x) x
def scale (x : Fp2) (k : Fp) : Fp2 := ⟨fmul x.a k, fmul x.b k⟩
def mul (x y : Fp2) : Fp2 :=
  let aa := fmul x.a y.a
  let bb := fmul x.b y.b
  ⟨fsub aa bb, fsub (fsub (fmul (fadd x.a x.b) (fadd y.a y.b)) aa) bb⟩
def sqr (x : Fp2) : Fp2 :=
  let ab := fmul x.a x.b
  ⟨fmul (fadd x.a x.b) (fsub x.a x.b), fadd ab ab⟩
/-- Times `1 + u`. -/
def timesXi (x : Fp2) : Fp2 := ⟨fsub x.a x.b, fadd x.a x.b⟩
def inv (x : Fp2) : Fp2 :=
  let norm := finv (fadd (fmul x.a x.a) (fmul x.b x.b))
  ⟨fmul x.a norm, fneg (fmul x.b norm)⟩
def pow (x : Fp2) (e : Array UInt64) : Fp2 := Id.run do
  let mut r := one
  let mut i := 64 * e.size
  while i > 0 do
    i := i - 1
    r := sqr r
    if (e[i / 64]! >>> (i % 64).toUInt64) &&& 1 == 1 then
      r := mul r x
  return r

def half : Fp := finv (small 2)

/-- A square root, if there is one. -/
def sqrt (x : Fp2) : Option Fp2 := Id.run do
  if Bls12381.isZero x.b then
    -- a plain number: its root is plain, or (when it has none) a multiple of u, since u² = −1
    match fsqrt x.a with
    | some r => return some ⟨r, Bls12381.zero⟩
    | none =>
      match fsqrt (fneg x.a) with
      | some r => return some ⟨Bls12381.zero, r⟩
      | none => return none
  match fsqrt (fadd (fmul x.a x.a) (fmul x.b x.b)) with
  | none => return none
  | some alpha =>
    let mut real := fsqrt (fmul (fadd x.a alpha) half)
    if real.isNone then
      real := fsqrt (fmul (fsub x.a alpha) half)
    match real with
    | none => return none
    | some r =>
      let root : Fp2 := ⟨r, fmul x.b (finv (fadd r r))⟩
      return if same (sqr root) x then some root else none

/-- Is a number larger than its negative? (Of a point's two possible `y`, this tells which one it has.) -/
def larger (y : Fp2) : Bool :=
  let v := if Bls12381.isZero y.b then y.a else y.b
  !(atLeast (leave (fneg v)) (leave v))

/-- Is a pair odd, as RFC 9380 counts it: by its first half, or by its second if the first is zero. -/
def odd (v : Fp2) : Bool := (leave v.a)[0]! &&& 1 == 1 || (Bls12381.isZero v.a && (leave v.b)[0]! &&& 1 == 1)
end Fp2

/-- `1 + u`: the twelve-fold field is built on a sixth root of it, `w`. -/
def xi : Fp2 := ⟨one, one⟩

/-- `w` to the power `p` is `w` times this: `(1 + u)` to the power `(p − 1)/6`. Its powers, 0 to 5. -/
def gammas : Array Fp2 := Id.run do
  let g := xi.pow #[0x49aa7ffffffff1c7, 0x051caaaa72e35555, 0xe688231ad3c82906, 0xe613e1eb7deb831f, 0x0c849bf3b5e1f223, 0x045582fc5eeaa66f]
  let mut out : Array Fp2 := #[Fp2.one]
  for i in [0:5] do
    out := out.push (out[i]!.mul g)
  return out

-- ------------------------------------------------- points

/-- A point `(x/z², y/z³)` of a curve `y² = x³ + b`; `z = 0` is the point at infinity. The plain curve
has `b = 4` and the twisted one `b = 4(1 + u)`, but adding points does not involve `b`. -/
structure Point where
  x : Fp2
  y : Fp2
  z : Fp2
  deriving Inhabited

namespace Point
def infinity : Point := ⟨Fp2.one, Fp2.one, Fp2.zero⟩
def isInfinity (a : Point) : Bool := a.z.isZero
def neg (a : Point) : Point := ⟨a.x, a.y.neg, a.z⟩

def double (a : Point) : Point :=
  let xx := a.x.sqr
  let yy := a.y.sqr
  let yyyy := yy.sqr
  let d := ((((a.x.add yy).sqr).sub xx).sub yyyy).twice
  let e := xx.thrice
  let x := (e.sqr.sub d).sub d
  ⟨x, (e.mul (d.sub x)).sub yyyy.twice.twice.twice, (a.y.mul a.z).twice⟩

def add (a b : Point) : Point :=
  if a.isInfinity then b
  else if b.isInfinity then a
  else
    let za := a.z.sqr
    let zb := b.z.sqr
    let ua := a.x.mul zb
    let sa := (a.y.mul b.z).mul zb
    let h := (b.x.mul za).sub ua
    let r := ((b.y.mul a.z).mul za).sub sa
    if h.isZero then
      if r.isZero then a.double else infinity
    else
      let hh := h.sqr
      let hhh := h.mul hh
      let v := ua.mul hh
      let x := ((r.sqr.sub hhh).sub v).sub v
      ⟨x, (r.mul (v.sub x)).sub (sa.mul hhh), (a.z.mul b.z).mul h⟩

/-- `k` times the point (`k` an ordinary number, in words). -/
def scale (a : Point) (k : Array UInt64) : Point := Id.run do
  let mut r := infinity
  let mut i := 64 * k.size
  while i > 0 do
    i := i - 1
    r := r.double
    if (k[i / 64]! >>> (i % 64).toUInt64) &&& 1 == 1 then
      r := r.add a
  return r

/-- The same point with `z = 1`. -/
def affine (a : Point) : Point :=
  if a.isInfinity then a
  else
    let zi := a.z.inv
    ⟨a.x.mul zi.sqr, (a.y.mul zi.sqr).mul zi, Fp2.one⟩

def same (a b : Point) : Bool :=
  if a.isInfinity || b.isInfinity then a.isInfinity && b.isInfinity
  else
    let za := a.z.sqr
    let zb := b.z.sqr
    (a.x.mul zb).same (b.x.mul za) && ((a.y.mul zb).mul b.z).same ((b.y.mul za).mul a.z)

/-- The curve's parameter is minus this; its bits steer the pairing. -/
def parameter : UInt64 := 0xd201000000010000

/-- The point times the curve's parameter. -/
def timesParameter (a : Point) : Point := (a.scale #[parameter]).neg

def psiX : Fp2 := (gammas[2]!).inv
def psiY : Fp2 := (gammas[3]!).inv

/-- A map of the twisted curve to itself that multiplies the points of the group by `p`. -/
def psi (a : Point) : Point := ⟨a.x.conj.mul psiX, a.y.conj.mul psiY, a.z.conj⟩

/-- Is a point of the twisted curve in the group signatures live in (the points of order r)? There
`psi` is multiplication by the parameter, and only there. -/
def inGroup (a : Point) : Bool := a.psi.same a.timesParameter

/-- A point from its compressed form: its `x`, most significant byte first, in 48 bytes for the plain
curve and 96 for the twisted one (second half first), with three flags on top: compressed, infinity,
and which `y`. A point of the twisted curve must be in the group. -/
def ofBytes (b : ByteArray) : Option Point := Id.run do
  let twisted := b.size == 96
  if (b.size != 48 && !twisted) || b[0]! &&& 0x80 == 0 then
    return none
  if b[0]! &&& 0x40 != 0 then
    return some infinity
  match fieldOf b 0 with
  | none => return none
  | some first =>
    match (if twisted then fieldOf b 48 else some Bls12381.zero) with
    | none => return none
    | some second =>
      let x : Fp2 := if twisted then ⟨second, first⟩ else ⟨first, second⟩
      let four := small 4
      match ((x.sqr.mul x).add ⟨four, if twisted then four else Bls12381.zero⟩).sqrt with
      | none => return none
      | some y =>
        let point : Point := ⟨x, if y.larger != (b[0]! &&& 0x20 != 0) then y.neg else y, Fp2.one⟩
        if (twisted && !point.inGroup) || (!twisted && !Bls12381.isZero y.b) then
          return none
        return some point

/-- The compressed form. -/
def toBytes (a : Point) (twisted : Bool) : ByteArray :=
  if a.isInfinity then (Fast.zeroed (if twisted then 96 else 48) 0).set! 0 0xC0
  else
    let q := a.affine
    let b := if twisted then bytesOf q.x.b ++ bytesOf q.x.a else bytesOf q.x.a
    b.set! 0 (b[0]! ||| (if q.y.larger then 0xA0 else 0x80))
end Point

/-- The generator of the plain curve's group. -/
def generator : Point :=
  match Point.ofBytes (Hex.decode "97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb") with
  | some g => g
  | none => Point.infinity

-- ------------------------------------------------- a message's point (RFC 9380)

/-- 256 bytes spun out of a message with SHA-256, for the purpose `domain` names. -/
def expand (message domain : ByteArray) : ByteArray := Id.run do
  let tag := domain.push domain.size.toUInt8
  let first := Sha256.hash ((((Fast.zeroed 64 (128 + message.size) ++ message).push 1).push 0).push 0 ++ tag)
  let mut block := Sha256.hash ((first.push 1) ++ tag)
  let mut out := block
  for i in [2:9] do
    let mut mixed := ByteArray.emptyWithCapacity 80
    for k in [0:32] do
      mixed := mixed.push (first[k]! ^^^ block[k]!)
    block := Sha256.hash ((mixed.push i.toUInt8) ++ tag)
    out := out ++ block
  return out

/-- The 64 bytes at `o` as a number modulo p. -/
def reduced (b : ByteArray) (o : Nat) : Fp :=
  fadd (fmul (enter (number b o 32)) (enter #[0, 0, 0, 0, 1, 0])) (enter (number b (o + 32) 32))

/-- A polynomial at `x`: coefficients from the constant up. -/
def polynomial (coefficients : Array Fp2) (x : Fp2) : Fp2 := Id.run do
  let mut r := Fp2.zero
  let mut i := coefficients.size
  while i > 0 do
    i := i - 1
    r := (r.mul x).add coefficients[i]!
  return r

/-- A point of the twisted curve from a pair of numbers. The simplified SWU map finds a point of
another curve, `y² = x³ + 240u·x + 1012(1 + u)`, and a map of degree three (whose coefficients are small
fractions; the nines and twenty-sevens under them go into `z`) carries it to the twisted curve. -/
def mapToCurve (t : Fp2) : Point := Id.run do
  let a : Fp2 := ⟨zero, small 240⟩
  let b : Fp2 := ⟨small 1012, small 1012⟩
  let z : Fp2 := ⟨minus 2, minus 1⟩
  let zt := z.mul t.sqr
  let v := zt.sqr.add zt
  let mut x := if v.isZero then b.mul (z.mul a).inv else (b.neg.mul a.inv).mul (Fp2.one.add v.inv)
  -- `x` if `x³ + a·x + b` has a root, or else `z·t²·x`, which then has one
  let mut root := Fp2.zero
  match (((x.sqr.add a).mul x).add b).sqrt with
  | some r => root := r
  | none =>
    x := zt.mul x
    match (((x.sqr.add a).mul x).add b).sqrt with
    | some r => root := r
    | none => root := Fp2.zero
  -- of the two roots, the one as odd as `t`
  let y := if root.odd != t.odd then root.neg else root
  let xn := polynomial #[⟨small 304, small 304⟩, ⟨zero, minus 24⟩, ⟨small 12, minus 12⟩, Fp2.one] x
  let xd := polynomial #[⟨zero, minus 72⟩, ⟨small 12, minus 12⟩, Fp2.one] x
  let yn := polynomial #[⟨small 752, small 752⟩, ⟨zero, small 264⟩, ⟨minus 18, small 18⟩, Fp2.one.neg] x
  let yd := polynomial #[⟨minus 432, minus 432⟩, ⟨zero, minus 216⟩, ⟨small 18, minus 18⟩, Fp2.one] x
  return ⟨(xn.mul xd).mul yd.sqr, ((y.mul yn).mul (xd.sqr.mul xd)).mul yd.sqr, (xd.mul yd).scale (small 3)⟩

/-- The point of the group that stands for a message, for the purpose `domain` names. -/
def hashToCurve (message domain : ByteArray) : Point :=
  let bytes := expand message domain
  let q := (mapToCurve ⟨reduced bytes 0, reduced bytes 64⟩).add (mapToCurve ⟨reduced bytes 128, reduced bytes 192⟩)
  -- into the group: (x² − x − 1)·q + (x − 1)·psi(q) + psi(psi(2q)), x the parameter
  let a := q.timesParameter
  let b := q.psi
  let c := (a.add b).timesParameter
  ((((q.double.psi.psi.add b.neg).add c).add a.neg).add q.neg)

-- ------------------------------------------------- twelve numbers: polynomials in w over pairs, w⁶ = 1 + u

abbrev Fp12 := Array Fp2

def one12 : Fp12 := (Array.replicate 6 Fp2.zero).set! 0 Fp2.one

/-- Eleven coefficients brought down to six. -/
def reduce (r : Array Fp2) : Fp12 := Id.run do
  let mut out : Fp12 := Array.emptyWithCapacity 6
  for i in [0:5] do
    out := out.push (r[i]!.add r[i + 6]!.timesXi)
  return out.push r[5]!

def mul12 (x y : Fp12) : Fp12 := Id.run do
  let mut r : Array Fp2 := Array.replicate 11 Fp2.zero
  for i in [0:6] do
    for j in [0:6] do
      if !y[j]!.isZero then
        r := r.set! (i + j) (r[i + j]!.add (x[i]!.mul y[j]!))
  return reduce r

def sqr12 (x : Fp12) : Fp12 := Id.run do
  let mut r : Array Fp2 := Array.replicate 11 Fp2.zero
  for i in [0:6] do
    r := r.set! (2 * i) (r[2 * i]!.add x[i]!.sqr)
    for j in [i + 1:6] do
      r := r.set! (i + j) (r[i + j]!.add (x[i]!.mul x[j]!).twice)
  return reduce r

/-- The power `p⁶`, which for the numbers a pairing ends in is the inverse. -/
def conj12 (x : Fp12) : Fp12 := #[x[0]!, x[1]!.neg, x[2]!, x[3]!.neg, x[4]!, x[5]!.neg]

/-- The power `p`. -/
def frobenius (x : Fp12) : Fp12 := Id.run do
  let mut out : Fp12 := Array.emptyWithCapacity 6
  for i in [0:6] do
    out := out.push (x[i]!.conj.mul gammas[i]!)
  return out

/-- The inverse: `x` times its conjugate has only even powers of `w`, and such a number times its
powers `p²` and `p⁴` is a pair. -/
def inv12 (x : Fp12) : Fp12 := Id.run do
  let n := mul12 x (conj12 x)
  let n2 := frobenius (frobenius n)
  let rest := mul12 n2 (frobenius (frobenius n2))
  let norm := ((mul12 n rest)[0]!).inv
  let mut out : Fp12 := Array.emptyWithCapacity 6
  for c in mul12 (conj12 x) rest do
    out := out.push (c.mul norm)
  return out

def isOne12 (x : Fp12) : Bool := Id.run do
  for i in [1:6] do
    if !x[i]!.isZero then
      return false
  return x[0]!.same Fp2.one

-- ------------------------------------------------- the pairing

-- A point (x', y') of the twisted curve stands for the point (x'/w², y'/w³) of the plain curve over
-- the twelve-fold field. A line through two such points, taken at a plain point (x, y) and multiplied
-- by w³, is `(slope·x' − y') − slope·x·w² + y·w³`: three coefficients. Factors that lie in a smaller
-- field (w³ here, denominators below) do not matter: the final power sends them to one.

def line (c0 c2 c3 : Fp2) : Fp12 := #[c0, Fp2.zero, c2, c3, Fp2.zero, Fp2.zero]

/-- The tangent at `t`, taken at `(x, y)`. -/
def tangent (t : Point) (x y : Fp) : Fp12 :=
  let e := t.x.sqr.thrice
  let zz := t.z.sqr
  line ((t.x.mul e).sub t.y.sqr.twice) ((e.mul zz).scale x).neg ((((t.y.mul t.z).twice).mul zz).scale y)

/-- The line through `t` and `q` (which has `z = 1`), taken at `(x, y)`. -/
def chord (t q : Point) (x y : Fp) : Fp12 :=
  let zz := t.z.sqr
  let r := ((q.y.mul zz).mul t.z).sub t.y
  let zh := t.z.mul ((q.x.mul zz).sub t.x)
  line ((r.mul q.x).sub (zh.mul q.y)) (r.scale x).neg (zh.scale y)

/-- Miller's loop for several pairs at once: plain points and twisted points, all with `z = 1`. -/
def miller (plain twisted : Array Point) : Fp12 := Id.run do
  let mut f := one12
  let mut ts := twisted
  let mut i := 63
  while i > 0 do
    i := i - 1
    f := sqr12 f
    for k in [0:plain.size] do
      f := mul12 f (tangent ts[k]! plain[k]!.x.a plain[k]!.y.a)
      ts := ts.set! k ts[k]!.double
    if (Point.parameter >>> i.toUInt64) &&& 1 == 1 then
      for k in [0:plain.size] do
        f := mul12 f (chord ts[k]! twisted[k]! plain[k]!.x.a plain[k]!.y.a)
        ts := ts.set! k (ts[k]!.add twisted[k]!)
  return f

/-- The square of `a + b·s`, where `s = w³` (so `s²` is `1 + u`): its two halves. -/
def sqr4 (a b : Fp2) : Fp2 × Fp2 :=
  let aa := a.sqr
  let bb := b.sqr
  (aa.add bb.timesXi, (((a.add b).sqr).sub aa).sub bb)

/-- The square of a number whose conjugate is its inverse, as the numbers a pairing ends in are
(Granger and Scott): written `a + b·w + c·w²` with `a`, `b`, `c` of the form above, it is
`(3a² − 2ā) + (3s·c² + 2b̄)·w + (3b² − 2c̄)·w²`, the bar changing the sign of `s`. -/
def sqrUnitary (x : Fp12) : Fp12 :=
  let (a0, a1) := sqr4 x[0]! x[3]!
  let (b0, b1) := sqr4 x[1]! x[4]!
  let (c0, c1) := sqr4 x[2]! x[5]!
  #[a0.thrice.sub x[0]!.twice, c1.timesXi.thrice.add x[1]!.twice, b0.thrice.sub x[2]!.twice,
    a1.thrice.add x[3]!.twice, c0.thrice.sub x[4]!.twice, b1.thrice.add x[5]!.twice]

/-- The power minus the parameter, of a number whose conjugate is its inverse. -/
def powParameter (x : Fp12) : Fp12 := Id.run do
  let mut r := x
  let mut i := 63
  while i > 0 do
    i := i - 1
    r := sqrUnitary r
    if (Point.parameter >>> i.toUInt64) &&& 1 == 1 then
      r := mul12 r x
  return conj12 r

/-- The power `3(p¹² − 1)/r`, which is one exactly when the power `(p¹² − 1)/r` is. With x the
parameter, `3(p⁴ − p² + 1)/r = (x − 1)²(x + p)(x² + p² − 1) + 3`. -/
def finalPower (f : Fp12) : Fp12 :=
  let g0 := mul12 (conj12 f) (inv12 f)
  let g := mul12 (frobenius (frobenius g0)) g0
  let t := mul12 (powParameter g) (conj12 g)
  let a := mul12 (powParameter t) (conj12 t)
  let b := mul12 (powParameter a) (frobenius a)
  let c := mul12 (mul12 (powParameter (powParameter b)) (frobenius (frobenius b))) (conj12 b)
  mul12 c (mul12 (sqrUnitary g) g)

/-- Do the pairings of each plain point with its twisted point multiply to one? None may be the point at infinity. -/
def pairingsCancel (plain twisted : Array Point) : Bool := Id.run do
  let mut ps : Array Point := Array.emptyWithCapacity plain.size
  let mut qs : Array Point := Array.emptyWithCapacity plain.size
  for k in [0:plain.size] do
    if plain[k]!.isInfinity || twisted[k]!.isInfinity then
      return false
    ps := ps.push plain[k]!.affine
    qs := qs.push twisted[k]!.affine
  return isOne12 (finalPower (miller ps qs))

/-- Is `signature` the signature of `message` by `key` (or the sum of signatures by the keys that sum to `key`)? -/
def verify (key : Point) (message domain : ByteArray) (signature : Point) : Bool :=
  pairingsCancel #[key, generator.neg] #[hashToCurve message domain, signature]

end Bls12381
