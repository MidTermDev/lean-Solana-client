import Crypto.Mont
import Crypto.Sha256

/-! # ECDSA over P-256 (secp256r1)

The curve of passkeys and of the secure chips in phones: `y² = x³ − 3x + b`
over a prime just below 2²⁵⁶. Solana has a program that checks such
signatures before a transaction runs, so that a wallet can be controlled by
a passkey; this is its arithmetic.

Points are kept as (X, Y, Z) standing for (X/Z², Y/Z³), numbers in
Montgomery form. Checking a signature is not secret work, so nothing here
tries to take the same time whatever the input. -/

namespace P256

abbrev Fp := Mont.Num

def p : Mont.Num := #[0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0x00000000, 0x00000000, 0x00000000, 0x00000001, 0xFFFFFFFF]
def n : Mont.Num := #[0xFC632551, 0xF3B9CAC2, 0xA7179E84, 0xBCE6FAAD, 0xFFFFFFFF, 0xFFFFFFFF, 0x00000000, 0xFFFFFFFF]
/-- Half the order, rounded down: `s` may not be above it (of the two forms of a signature, only the lower). -/
def halfN : Mont.Num := #[0x7E3192A8, 0x79DCE561, 0xD38BCF42, 0xDE737D56, 0xFFFFFFFF, 0x7FFFFFFF, 0x80000000, 0x7FFFFFFF]
def fp : Mont.Field := Mont.Field.make p
def fn : Mont.Field := Mont.Field.make n

def fadd (a b : Fp) : Fp := Mont.addMod p a b
def fsub (a b : Fp) : Fp := Mont.subMod p a b
def fmul (a b : Fp) : Fp := Mont.mul fp a b

def curveB : Fp := fp.enter #[0x27D2604B, 0x3BCE3C3E, 0xCC53B0F6, 0x651D06B0, 0x769886BC, 0xB3EBBD55, 0xAA3A93E7, 0x5AC635D8]
def three : Fp := fp.enter #[3, 0, 0, 0, 0, 0, 0, 0]

structure Point where
  x : Fp
  y : Fp
  z : Fp
  deriving Inhabited

def infinity : Point := ⟨fp.one, fp.one, Mont.zero⟩

def generator : Point :=
  ⟨fp.enter #[0xD898C296, 0xF4A13945, 0x2DEB33A0, 0x77037D81, 0x63A440F2, 0xF8BCE6E5, 0xE12C4247, 0x6B17D1F2],
   fp.enter #[0x37BF51F5, 0xCBB64068, 0x6B315ECE, 0x2BCE3357, 0x7C0F9E16, 0x8EE7EB4A, 0xFE1A7F9B, 0x4FE342E2], fp.one⟩

def double (a : Point) : Point :=
  if Mont.isZero a.z || Mont.isZero a.y then infinity
  else
    let zz := fmul a.z a.z
    -- the slope's numerator, 3x² − 3z⁴, as 3(x − z²)(x + z²)
    let m := fmul three (fmul (fsub a.x zz) (fadd a.x zz))
    let yy := fmul a.y a.y
    let xyy := fmul a.x yy
    let s := fadd (fadd xyy xyy) (fadd xyy xyy)
    let x := fsub (fmul m m) (fadd s s)
    let y4 := fmul yy yy
    let y8 := fadd (fadd y4 y4) (fadd y4 y4)
    let y := fsub (fmul m (fsub s x)) (fadd y8 y8)
    let yz := fmul a.y a.z
    ⟨x, y, fadd yz yz⟩

def add (a b : Point) : Point :=
  if Mont.isZero a.z then b
  else if Mont.isZero b.z then a
  else
    let z1z1 := fmul a.z a.z
    let z2z2 := fmul b.z b.z
    let u1 := fmul a.x z2z2
    let u2 := fmul b.x z1z1
    let s1 := fmul a.y (fmul z2z2 b.z)
    let s2 := fmul b.y (fmul z1z1 a.z)
    let h := fsub u2 u1
    let r := fsub s2 s1
    if Mont.isZero h then
      if Mont.isZero r then double a else infinity
    else
      let hh := fmul h h
      let hhh := fmul hh h
      let v := fmul u1 hh
      let x := fsub (fsub (fmul r r) hhh) (fadd v v)
      let y := fsub (fmul r (fsub v x)) (fmul s1 hhh)
      ⟨x, y, fmul h (fmul a.z b.z)⟩

/-- `j·a + k·b`, for ordinary numbers `j` and `k`: one pass over their bits, adding `a`, `b` or their sum. -/
def combine (j : Mont.Num) (a : Point) (k : Mont.Num) (b : Point) : Point := Id.run do
  let both := add a b
  let mut result := infinity
  let mut i := 256
  while i > 0 do
    i := i - 1
    result := double result
    let bitJ := (j[i / 32]! >>> (i % 32).toUInt64) &&& 1 == 1
    let bitK := (k[i / 32]! >>> (i % 32).toUInt64) &&& 1 == 1
    if bitJ && bitK then
      result := add result both
    else if bitJ then
      result := add result a
    else if bitK then
      result := add result b
  return result

/-- A public key from its 33 bytes: 2 or 3 (which of the two `y`: the even or the odd), then `x`. -/
def decode (key : ByteArray) : Option Point :=
  if key.size != 33 || (key[0]! != 2 && key[0]! != 3) then none
  else
    let raw := Mont.ofBytes key 1 true
    if Mont.atLeast raw p then none
    else
      let x := fp.enter raw
      let rhs := fadd (fsub (fmul (fmul x x) x) (fmul three x)) curveB
      -- the prime is 3 modulo 4: a square root, if there is one, is the (p + 1)/4-th power
      let root := Mont.pow fp rhs #[0x00000000, 0x00000000, 0x40000000, 0x00000000, 0x00000000, 0x40000000, 0xC0000000, 0x3FFFFFFF]
      if !(Mont.same (fmul root root) rhs) then none
      else
        let odd := (fp.leave root)[0]! &&& 1 == 1
        some ⟨x, if odd == (key[0]! == 3) then root else Mont.subMod p Mont.zero root, fp.one⟩

/-- Is `(r, s)` in the range the program accepts: `r` from 1 to below the order, `s` from 1 to half the order? -/
def inRange (signature : ByteArray) : Bool :=
  let r := Mont.ofBytes signature 0 true
  let s := Mont.ofBytes signature 32 true
  !(Mont.isZero r) && !(Mont.atLeast r n) && !(Mont.isZero s) && Mont.atLeast halfN s

/-- Did the holder of `key` sign the SHA-256 hash of `message` with `signature` (`r` then `s`, 32 bytes each)? -/
def verify (key : Point) (signature message : ByteArray) : Bool :=
  let r := Mont.ofBytes signature 0 true
  let s := Mont.ofBytes signature 32 true
  if Mont.isZero r || Mont.atLeast r n || Mont.isZero s || Mont.atLeast s n then false
  else
    let hash := Mont.ofBytes (Sha256.hash message) 0 true
    let z := if Mont.atLeast hash n then Mont.subRaw hash n else hash
    let w := Mont.inv fn (fn.enter s)
    let u1 := fn.leave (Mont.mul fn (fn.enter z) w)
    let u2 := fn.leave (Mont.mul fn (fn.enter r) w)
    let point := combine u1 generator u2 key
    if Mont.isZero point.z then false
    else
      let zi := Mont.inv fp point.z
      let x := fp.leave (fmul point.x (fmul zi zi))
      Mont.same (if Mont.atLeast x n then Mont.subRaw x n else x) r

end P256
