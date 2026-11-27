/-!
# secp256k1: recovering a public key from a signature

The curve of Bitcoin and Ethereum, `y² = x³ + 7` over the integers modulo
`p = 2²⁵⁶ − 2³² − 977`. Programs on Solana use one operation on it, through
a system call: given a message hash and a signature, find the public key
that made it (which is how an Ethereum address is checked).

Numbers are eight 32-bit digits, least significant first, each in a 64-bit
word. Nothing here is fast, and nothing needs to be secret: every input is
public.
-/

namespace Secp256k1

abbrev Num := Array UInt64

def ofDigits (digits : Array UInt64) : Num := digits

/-- The field's modulus `p`, and `2²⁵⁶ − p`. -/
def p : Num := #[0xFFFFFC2F, 0xFFFFFFFE, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF]
def pGap : Num := #[0x3D1, 1]
/-- The number of points `n`, and `2²⁵⁶ − n`. -/
def n : Num := #[0xD0364141, 0xBFD25E8C, 0xAF48A03B, 0xBAAEDCE6, 0xFFFFFFFE, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF]
def nGap : Num := #[0x2FC9BEBF, 0x402DA173, 0x50B75FC4, 0x45512319, 1]

def zero : Num := Array.replicate 8 0
def one : Num := #[1, 0, 0, 0, 0, 0, 0, 0]

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

/-- `a ≥ b`, both of the same length. -/
def atLeast (a b : Num) : Bool := Id.run do
  let mut i := a.size
  while i > 0 do
    i := i - 1
    if a[i]! != b[i]! then
      return a[i]! > b[i]!
  return true

/-- `a − b` for `a ≥ b`, both of 8 digits. -/
def subRaw (a b : Num) : Num := Id.run do
  let mut out : Num := Array.emptyWithCapacity 8
  let mut borrow : UInt64 := 0
  for i in [0:8] do
    let d := a[i]! + 0x100000000 - b[i]! - borrow
    out := out.push (d &&& 0xFFFFFFFF)
    borrow := if d < 0x100000000 then 1 else 0
  return out

/-- The product of two numbers, digit by digit: as many digits as both together. -/
def mulRaw (a b : Num) : Num := Id.run do
  let mut out : Num := Array.replicate (a.size + b.size) 0
  for i in [0:a.size] do
    let mut carry : UInt64 := 0
    for j in [0:b.size] do
      let t := out[i + j]! + a[i]! * b[j]! + carry
      out := out.set! (i + j) (t &&& 0xFFFFFFFF)
      carry := t >>> 32
    out := out.set! (i + b.size) carry
  return out

/-- Reduces a number of any length modulo `m = 2²⁵⁶ − gap`: what lies above
256 bits is worth `gap` times as much below, so it is multiplied by `gap`
and added in, until nothing is above; then `m` is subtracted while it fits. -/
def reduce (x : Num) (m gap : Num) : Num := Id.run do
  let mut v := x
  while v.size > 8 do
    -- low eight digits, plus the rest times the gap
    let mut high : Num := Array.emptyWithCapacity (v.size - 8)
    for i in [8:v.size] do
      high := high.push v[i]!
    let mut any := false
    for d in high do
      if d != 0 then
        any := true
    let mut sum : Num := Array.emptyWithCapacity (high.size + gap.size + 1)
    if any then
      let folded := mulRaw high gap
      let mut carry : UInt64 := 0
      for i in [0:(if folded.size > 8 then folded.size else 8)] do
        let t := (if i < 8 then v[i]! else 0) + (if i < folded.size then folded[i]! else 0) + carry
        sum := sum.push (t &&& 0xFFFFFFFF)
        carry := t >>> 32
      sum := sum.push carry
      -- drop leading zeros beyond eight digits
      while sum.size > 8 && sum[sum.size - 1]! == 0 do
        sum := sum.pop
    else
      for i in [0:8] do
        sum := sum.push v[i]!
    v := sum
  while v.size < 8 do
    v := v.push 0
  while atLeast v m do
    v := subRaw v m
  return v

def mulMod (a b m gap : Num) : Num := reduce (mulRaw a b) m gap

def addMod (a b m gap : Num) : Num := Id.run do
  let mut out : Num := Array.emptyWithCapacity 9
  let mut carry : UInt64 := 0
  for i in [0:8] do
    let t := a[i]! + b[i]! + carry
    out := out.push (t &&& 0xFFFFFFFF)
    carry := t >>> 32
  out := out.push carry
  return reduce out m gap

/-- `a − b` modulo `m`, for `a` and `b` below `m`. -/
def subMod (a b m : Num) : Num :=
  if atLeast a b then subRaw a b else subRaw m (subRaw b a)

/-- `a` to the power `e` (eight digits) modulo `m`. -/
def powMod (a e m gap : Num) : Num := Id.run do
  let mut result := one
  let mut started := false
  let mut i := 256
  while i > 0 do
    i := i - 1
    if started then
      result := mulMod result result m gap
    if (e[i / 32]! >>> (i % 32).toUInt64) &&& 1 == 1 then
      result := if started then mulMod result a m gap else a
      started := true
  return result

-- field arithmetic
def fmul (a b : Num) : Num := mulMod a b p pGap
def fadd (a b : Num) : Num := addMod a b p pGap
def fsub (a b : Num) : Num := subMod a b p

/-- A point in Jacobian coordinates: `(X/Z², Y/Z³)`, with `Z = 0` for the point at infinity. -/
structure Point where
  x : Num
  y : Num
  z : Num
  deriving Inhabited

def infinity : Point := ⟨one, one, zero⟩

def generator : Point :=
  ⟨#[0x16F81798, 0x59F2815B, 0x2DCE28D9, 0x029BFCDB, 0xCE870B07, 0x55A06295, 0xF9DCBBAC, 0x79BE667E],
   #[0xFB10D4B8, 0x9C47D08F, 0xA6855419, 0xFD17B448, 0x0E1108A8, 0x5DA4FBFC, 0x26A3C465, 0x483ADA77], one⟩

def double (a : Point) : Point :=
  if isZero a.z || isZero a.y then infinity
  else
    let xx := fmul a.x a.x
    let yy := fmul a.y a.y
    let yyyy := fmul yy yy
    let t := fadd a.x yy
    let d0 := fsub (fsub (fmul t t) xx) yyyy
    let d := fadd d0 d0
    let e := fadd (fadd xx xx) xx
    let f := fmul e e
    let x3 := fsub f (fadd d d)
    let c8 := fadd (fadd (fadd yyyy yyyy) (fadd yyyy yyyy)) (fadd (fadd yyyy yyyy) (fadd yyyy yyyy))
    let y3 := fsub (fmul e (fsub d x3)) c8
    let yz := fmul a.y a.z
    ⟨x3, y3, fadd yz yz⟩

def add (a b : Point) : Point :=
  if isZero a.z then b
  else if isZero b.z then a
  else
    let z1z1 := fmul a.z a.z
    let z2z2 := fmul b.z b.z
    let u1 := fmul a.x z2z2
    let u2 := fmul b.x z1z1
    let s1 := fmul a.y (fmul b.z z2z2)
    let s2 := fmul b.y (fmul a.z z1z1)
    if same u1 u2 then
      if same s1 s2 then double a else infinity
    else
      let h := fsub u2 u1
      let r := fsub s2 s1
      let hh := fmul h h
      let hhh := fmul h hh
      let v := fmul u1 hh
      let x3 := fsub (fsub (fmul r r) hhh) (fadd v v)
      let y3 := fsub (fmul r (fsub v x3)) (fmul s1 hhh)
      ⟨x3, y3, fmul h (fmul a.z b.z)⟩

/-- `k` times a point. -/
def scale (k : Num) (a : Point) : Point := Id.run do
  let mut result := infinity
  let mut i := 256
  while i > 0 do
    i := i - 1
    result := double result
    if (k[i / 32]! >>> (i % 32).toUInt64) &&& 1 == 1 then
      result := add result a
  return result

/-- Thirty-two big-endian bytes at `o` as a number. -/
def ofBytes (b : ByteArray) (o : Nat) : Num := Id.run do
  let mut out : Num := Array.emptyWithCapacity 8
  for i in [0:8] do
    let at_ := o + 28 - 4 * i
    out := out.push ((b[at_]!.toUInt64 <<< 24) ||| (b[at_ + 1]!.toUInt64 <<< 16) ||| (b[at_ + 2]!.toUInt64 <<< 8) ||| b[at_ + 3]!.toUInt64)
  return out

def toBytes (a : Num) (out0 : ByteArray) : ByteArray := Id.run do
  let mut out := out0
  let mut i := 8
  while i > 0 do
    i := i - 1
    out := out.push (a[i]! >>> 24).toUInt8
    out := out.push (a[i]! >>> 16).toUInt8
    out := out.push (a[i]! >>> 8).toUInt8
    out := out.push a[i]!.toUInt8
  return out

/-- The public key (64 bytes: x then y) whose signature `(r, s)` over the
32-byte `hash` this is, given which of the candidate points to take
(`recovery`, 0 to 3). Empty if there is none. -/
def recover (hash : ByteArray) (recovery : Nat) (signature : ByteArray) : ByteArray := Id.run do
  if hash.size != 32 || signature.size != 64 || recovery > 3 then
    return ByteArray.empty
  let r := ofBytes signature 0
  let s := ofBytes signature 32
  if isZero r || isZero s || atLeast r n || atLeast s n then
    return ByteArray.empty
  -- the point R: its x is r (or r + n), its y the square root with the parity asked for
  let mut x := r
  if recovery >= 2 then
    -- r + n must still be below p
    let mut sum : Num := Array.emptyWithCapacity 9
    let mut carry : UInt64 := 0
    for i in [0:8] do
      let t := r[i]! + n[i]! + carry
      sum := sum.push (t &&& 0xFFFFFFFF)
      carry := t >>> 32
    if carry != 0 || atLeast sum p then
      return ByteArray.empty
    x := sum
  let rhs := fadd (fmul (fmul x x) x) #[7, 0, 0, 0, 0, 0, 0, 0]
  -- p is 3 modulo 4: a square root, if there is one, is the (p + 1)/4-th power
  let exponent : Num := #[0xBFFFFF0C, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0x3FFFFFFF]
  let mut y := powMod rhs exponent p pGap
  if !(same (fmul y y) rhs) then
    return ByteArray.empty
  if (y[0]! &&& 1 == 1) != (recovery % 2 == 1) then
    y := fsub zero y
  -- the key is (s·R − z·G) / r
  let z := reduce (ofBytes hash 0) n nGap
  let nMinus2 : Num := #[0xD036413F, 0xBFD25E8C, 0xAF48A03B, 0xBAAEDCE6, 0xFFFFFFFE, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF]
  let rInverse := powMod r nMinus2 n nGap
  let u1 := subMod zero (mulMod z rInverse n nGap) n
  let u2 := mulMod s rInverse n nGap
  let q := add (scale u1 generator) (scale u2 ⟨x, y, one⟩)
  if isZero q.z then
    return ByteArray.empty
  -- back from Jacobian coordinates
  let pMinus2 : Num := #[0xFFFFFC2D, 0xFFFFFFFE, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF]
  let zInverse := powMod q.z pMinus2 p pGap
  let zz := fmul zInverse zInverse
  return toBytes (fmul q.y (fmul zz zInverse)) (toBytes (fmul q.x zz) (ByteArray.emptyWithCapacity 64))

end Secp256k1
