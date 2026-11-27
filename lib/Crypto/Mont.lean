/-!
# Arithmetic modulo a 256-bit number

Several things the chain's programs can ask for (the Poseidon hash, the
alt_bn128 curve) are arithmetic modulo a prime of about 254 bits that is
not close to a power of two, so there is no shortcut to reducing a product.
Montgomery's method avoids the division: numbers are kept multiplied by
2²⁵⁶, and a product is brought back into range with multiplications only.

A number is eight 32-bit digits, least significant first, each in a 64-bit
word. A `Field` holds what the method needs to know about a modulus.
-/

namespace Mont

abbrev Num := Array UInt64

structure Field where
  /-- the modulus (odd) -/
  m : Num
  /-- minus the inverse of the modulus, modulo 2³² -/
  inverse : UInt64
  /-- 2²⁵⁶ and 2⁵¹² modulo the modulus: the number one, and what turns a number into its Montgomery form -/
  one : Num
  square : Num
  deriving Inhabited

def zero : Num := Array.replicate 8 0

def isZero (a : Num) : Bool := Id.run do
  for d in a do
    if d != 0 then
      return false
  return true

def same (a b : Num) : Bool := Id.run do
  for i in [0:8] do
    if a[i]! != b[i]! then
      return false
  return true

/-- `a ≥ b`. -/
def atLeast (a b : Num) : Bool := Id.run do
  let mut i := 8
  while i > 0 do
    i := i - 1
    if a[i]! != b[i]! then
      return a[i]! > b[i]!
  return true

/-- `a − b` for `a ≥ b`. -/
def subRaw (a b : Num) : Num := Id.run do
  let mut out : Num := Array.emptyWithCapacity 8
  let mut borrow : UInt64 := 0
  for i in [0:8] do
    let d := a[i]! + 0x100000000 - b[i]! - borrow
    out := out.push (d &&& 0xFFFFFFFF)
    borrow := if d < 0x100000000 then 1 else 0
  return out

/-- `a + b` modulo `m`, for `a` and `b` below `m`. -/
def addMod (m a b : Num) : Num := Id.run do
  let mut out : Num := Array.emptyWithCapacity 8
  let mut carry : UInt64 := 0
  for i in [0:8] do
    let t := a[i]! + b[i]! + carry
    out := out.push (t &&& 0xFFFFFFFF)
    carry := t >>> 32
  if carry != 0 || atLeast out m then
    -- (with a carry out of the top, the subtraction's borrow cancels it)
    let mut fixed : Num := Array.emptyWithCapacity 8
    let mut borrow : UInt64 := 0
    for i in [0:8] do
      let d := out[i]! + 0x100000000 - m[i]! - borrow
      fixed := fixed.push (d &&& 0xFFFFFFFF)
      borrow := if d < 0x100000000 then 1 else 0
    return fixed
  return out

def subMod (m a b : Num) : Num :=
  if atLeast a b then subRaw a b else subRaw m (subRaw b a)

/-- What a modulus needs: the inverse of its lowest digit, and powers of two reduced by it. -/
def Field.make (m : Num) : Field := Id.run do
  -- Newton's iteration doubles the number of correct bits of an inverse modulo a power of two
  let m0 := m[0]!
  let mut x : UInt64 := 1
  for _ in [0:5] do
    x := (x * (2 - m0 * x)) &&& 0xFFFFFFFF
  let inverse := (0x100000000 - x) &&& 0xFFFFFFFF
  -- 2^256 and 2^512 modulo m, by doubling
  let mut v : Num := #[1, 0, 0, 0, 0, 0, 0, 0]
  let mut one := v
  for i in [0:512] do
    v := addMod m v v
    if i == 255 then
      one := v
  return ⟨m, inverse, one, v⟩

/-- The Montgomery product: `a × b / 2²⁵⁶` modulo the modulus. -/
def mul (f : Field) (a b : Num) : Num := Id.run do
  let m := f.m
  let mut t : Num := Array.replicate 10 0
  for i in [0:8] do
    let bi := b[i]!
    let mut c : UInt64 := 0
    for j in [0:8] do
      let v := t[j]! + a[j]! * bi + c
      t := t.set! j (v &&& 0xFFFFFFFF)
      c := v >>> 32
    let top := t[8]! + c
    t := t.set! 8 (top &&& 0xFFFFFFFF)
    t := t.set! 9 (top >>> 32)
    -- add the multiple of the modulus that makes the lowest digit zero, and drop that digit
    let q := (t[0]! * f.inverse) &&& 0xFFFFFFFF
    let mut c2 := (t[0]! + q * m[0]!) >>> 32
    for j in [1:8] do
      let v := t[j]! + q * m[j]! + c2
      t := t.set! (j - 1) (v &&& 0xFFFFFFFF)
      c2 := v >>> 32
    let top2 := t[8]! + c2
    t := t.set! 7 (top2 &&& 0xFFFFFFFF)
    t := t.set! 8 (t[9]! + (top2 >>> 32))
  let mut out : Num := Array.emptyWithCapacity 8
  for i in [0:8] do
    out := out.push t[i]!
  if t[8]! != 0 || atLeast out m then
    let mut fixed : Num := Array.emptyWithCapacity 8
    let mut borrow : UInt64 := 0
    for i in [0:8] do
      let d := out[i]! + 0x100000000 - m[i]! - borrow
      fixed := fixed.push (d &&& 0xFFFFFFFF)
      borrow := if d < 0x100000000 then 1 else 0
    return fixed
  return out

/-- A number below the modulus, into Montgomery form and back. -/
def Field.enter (f : Field) (a : Num) : Num := mul f a f.square
def Field.leave (f : Field) (a : Num) : Num := mul f a #[1, 0, 0, 0, 0, 0, 0, 0]

/-- `a` (in Montgomery form) to the power `e` (an ordinary number of eight digits). -/
def pow (f : Field) (a e : Num) : Num := Id.run do
  let mut result := f.one
  let mut i := 256
  while i > 0 do
    i := i - 1
    result := mul f result result
    if (e[i / 32]! >>> (i % 32).toUInt64) &&& 1 == 1 then
      result := mul f result a
  return result

/-- The inverse modulo a prime: the power `m − 2`. -/
def inv (f : Field) (a : Num) : Num :=
  pow f a (subRaw f.m #[2, 0, 0, 0, 0, 0, 0, 0])

/-- Thirty-two bytes at `o` as a number, most significant byte first (or last). -/
def ofBytes (b : ByteArray) (o : Nat) (bigEndian : Bool) : Num := Id.run do
  let mut out : Num := Array.emptyWithCapacity 8
  for i in [0:8] do
    let mut d : UInt64 := 0
    for k in [0:4] do
      let at_ := if bigEndian then o + 31 - (4 * i + k) else o + 4 * i + k
      d := d ||| (b[at_]!.toUInt64 <<< (8 * k).toUInt64)
    out := out.push d
  return out

def toBytes (a : Num) (bigEndian : Bool) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity 32
  for i in [0:32] do
    let at_ := if bigEndian then 31 - i else i
    out := out.push (a[at_ / 4]! >>> (8 * (at_ % 4)).toUInt64).toUInt8
  return out

end Mont
