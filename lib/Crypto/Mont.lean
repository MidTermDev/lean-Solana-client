import Fast
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
  /-- the modulus as four 64-bit words, and minus its inverse modulo 2⁶⁴ -/
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64
  inverse64 : UInt64
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
  let low := m[0]! ||| (m[1]! <<< 32)
  let mut y : UInt64 := 1
  for _ in [0:6] do
    y := y * (2 - low * y)
  return ⟨m, inverse, one, v, low, m[2]! ||| (m[3]! <<< 32), m[4]! ||| (m[5]! <<< 32), m[6]! ||| (m[7]! <<< 32), 0 - y⟩

/-- The Montgomery product digit by digit, from the modulus and the inverse of its lowest digit alone. -/
def mulDigits (m : Num) (inverse : UInt64) (a b : Num) : Num := Id.run do
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
    let q := (t[0]! * inverse) &&& 0xFFFFFFFF
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

/-- The Montgomery product: `a × b / 2²⁵⁶` modulo the modulus.

Worked in four 64-bit words (the eight 32-bit digits, paired), each product of two words taken whole:
its low half by an ordinary multiplication and its high half by `Fast.mulHi`. A carry out of an addition
is seen by the sum being smaller than what was added. One round per word of `b`: add `a` times that word,
then the multiple of the modulus that makes the lowest word zero, and drop that word. -/
def mul (f : Field) (a b : Num) : Num :=
  let a0 := a[0]! ||| (a[1]! <<< 32)
  let a1 := a[2]! ||| (a[3]! <<< 32)
  let a2 := a[4]! ||| (a[5]! <<< 32)
  let a3 := a[6]! ||| (a[7]! <<< 32)
  let b0 := b[0]! ||| (b[1]! <<< 32)
  let b1 := b[2]! ||| (b[3]! <<< 32)
  let b2 := b[4]! ||| (b[5]! <<< 32)
  let b3 := b[6]! ||| (b[7]! <<< 32)
  let m0 := f.w0
  let m1 := f.w1
  let m2 := f.w2
  let m3 := f.w3
  let inv := f.inverse64
  let z0 := (0 : UInt64)
  let z1 := (0 : UInt64)
  let z2 := (0 : UInt64)
  let z3 := (0 : UInt64)
  let z4 := (0 : UInt64)
  let lo1 := a0 * b0
  let hi2 := Fast.mulHi a0 b0
  let s3 := z0 + lo1
  let c4 := hi2 + Fast.bit (s3 < lo1)
  let lo5 := a1 * b0
  let hi6 := Fast.mulHi a1 b0
  let s7 := z1 + lo5
  let s8 := s7 + c4
  let c9 := hi6 + Fast.bit (s7 < lo5) + Fast.bit (s8 < c4)
  let lo10 := a2 * b0
  let hi11 := Fast.mulHi a2 b0
  let s12 := z2 + lo10
  let s13 := s12 + c9
  let c14 := hi11 + Fast.bit (s12 < lo10) + Fast.bit (s13 < c9)
  let lo15 := a3 * b0
  let hi16 := Fast.mulHi a3 b0
  let s17 := z3 + lo15
  let s18 := s17 + c14
  let c19 := hi16 + Fast.bit (s17 < lo15) + Fast.bit (s18 < c14)
  let s20 := z4 + c19
  let c21 := Fast.bit (s20 < c19)
  let q22 := s3 * inv
  let lo23 := q22 * m0
  let hi24 := Fast.mulHi q22 m0
  let s25 := s3 + lo23
  let c26 := hi24 + Fast.bit (s25 < lo23)
  let lo27 := q22 * m1
  let hi28 := Fast.mulHi q22 m1
  let s29 := s8 + lo27
  let s30 := s29 + c26
  let c31 := hi28 + Fast.bit (s29 < lo27) + Fast.bit (s30 < c26)
  let lo32 := q22 * m2
  let hi33 := Fast.mulHi q22 m2
  let s34 := s13 + lo32
  let s35 := s34 + c31
  let c36 := hi33 + Fast.bit (s34 < lo32) + Fast.bit (s35 < c31)
  let lo37 := q22 * m3
  let hi38 := Fast.mulHi q22 m3
  let s39 := s18 + lo37
  let s40 := s39 + c36
  let c41 := hi38 + Fast.bit (s39 < lo37) + Fast.bit (s40 < c36)
  let s42 := s20 + c41
  let c43 := c21 + Fast.bit (s42 < c41)
  let lo44 := a0 * b1
  let hi45 := Fast.mulHi a0 b1
  let s46 := s30 + lo44
  let c47 := hi45 + Fast.bit (s46 < lo44)
  let lo48 := a1 * b1
  let hi49 := Fast.mulHi a1 b1
  let s50 := s35 + lo48
  let s51 := s50 + c47
  let c52 := hi49 + Fast.bit (s50 < lo48) + Fast.bit (s51 < c47)
  let lo53 := a2 * b1
  let hi54 := Fast.mulHi a2 b1
  let s55 := s40 + lo53
  let s56 := s55 + c52
  let c57 := hi54 + Fast.bit (s55 < lo53) + Fast.bit (s56 < c52)
  let lo58 := a3 * b1
  let hi59 := Fast.mulHi a3 b1
  let s60 := s42 + lo58
  let s61 := s60 + c57
  let c62 := hi59 + Fast.bit (s60 < lo58) + Fast.bit (s61 < c57)
  let s63 := c43 + c62
  let c64 := Fast.bit (s63 < c62)
  let q65 := s46 * inv
  let lo66 := q65 * m0
  let hi67 := Fast.mulHi q65 m0
  let s68 := s46 + lo66
  let c69 := hi67 + Fast.bit (s68 < lo66)
  let lo70 := q65 * m1
  let hi71 := Fast.mulHi q65 m1
  let s72 := s51 + lo70
  let s73 := s72 + c69
  let c74 := hi71 + Fast.bit (s72 < lo70) + Fast.bit (s73 < c69)
  let lo75 := q65 * m2
  let hi76 := Fast.mulHi q65 m2
  let s77 := s56 + lo75
  let s78 := s77 + c74
  let c79 := hi76 + Fast.bit (s77 < lo75) + Fast.bit (s78 < c74)
  let lo80 := q65 * m3
  let hi81 := Fast.mulHi q65 m3
  let s82 := s61 + lo80
  let s83 := s82 + c79
  let c84 := hi81 + Fast.bit (s82 < lo80) + Fast.bit (s83 < c79)
  let s85 := s63 + c84
  let c86 := c64 + Fast.bit (s85 < c84)
  let lo87 := a0 * b2
  let hi88 := Fast.mulHi a0 b2
  let s89 := s73 + lo87
  let c90 := hi88 + Fast.bit (s89 < lo87)
  let lo91 := a1 * b2
  let hi92 := Fast.mulHi a1 b2
  let s93 := s78 + lo91
  let s94 := s93 + c90
  let c95 := hi92 + Fast.bit (s93 < lo91) + Fast.bit (s94 < c90)
  let lo96 := a2 * b2
  let hi97 := Fast.mulHi a2 b2
  let s98 := s83 + lo96
  let s99 := s98 + c95
  let c100 := hi97 + Fast.bit (s98 < lo96) + Fast.bit (s99 < c95)
  let lo101 := a3 * b2
  let hi102 := Fast.mulHi a3 b2
  let s103 := s85 + lo101
  let s104 := s103 + c100
  let c105 := hi102 + Fast.bit (s103 < lo101) + Fast.bit (s104 < c100)
  let s106 := c86 + c105
  let c107 := Fast.bit (s106 < c105)
  let q108 := s89 * inv
  let lo109 := q108 * m0
  let hi110 := Fast.mulHi q108 m0
  let s111 := s89 + lo109
  let c112 := hi110 + Fast.bit (s111 < lo109)
  let lo113 := q108 * m1
  let hi114 := Fast.mulHi q108 m1
  let s115 := s94 + lo113
  let s116 := s115 + c112
  let c117 := hi114 + Fast.bit (s115 < lo113) + Fast.bit (s116 < c112)
  let lo118 := q108 * m2
  let hi119 := Fast.mulHi q108 m2
  let s120 := s99 + lo118
  let s121 := s120 + c117
  let c122 := hi119 + Fast.bit (s120 < lo118) + Fast.bit (s121 < c117)
  let lo123 := q108 * m3
  let hi124 := Fast.mulHi q108 m3
  let s125 := s104 + lo123
  let s126 := s125 + c122
  let c127 := hi124 + Fast.bit (s125 < lo123) + Fast.bit (s126 < c122)
  let s128 := s106 + c127
  let c129 := c107 + Fast.bit (s128 < c127)
  let lo130 := a0 * b3
  let hi131 := Fast.mulHi a0 b3
  let s132 := s116 + lo130
  let c133 := hi131 + Fast.bit (s132 < lo130)
  let lo134 := a1 * b3
  let hi135 := Fast.mulHi a1 b3
  let s136 := s121 + lo134
  let s137 := s136 + c133
  let c138 := hi135 + Fast.bit (s136 < lo134) + Fast.bit (s137 < c133)
  let lo139 := a2 * b3
  let hi140 := Fast.mulHi a2 b3
  let s141 := s126 + lo139
  let s142 := s141 + c138
  let c143 := hi140 + Fast.bit (s141 < lo139) + Fast.bit (s142 < c138)
  let lo144 := a3 * b3
  let hi145 := Fast.mulHi a3 b3
  let s146 := s128 + lo144
  let s147 := s146 + c143
  let c148 := hi145 + Fast.bit (s146 < lo144) + Fast.bit (s147 < c143)
  let s149 := c129 + c148
  let c150 := Fast.bit (s149 < c148)
  let q151 := s132 * inv
  let lo152 := q151 * m0
  let hi153 := Fast.mulHi q151 m0
  let s154 := s132 + lo152
  let c155 := hi153 + Fast.bit (s154 < lo152)
  let lo156 := q151 * m1
  let hi157 := Fast.mulHi q151 m1
  let s158 := s137 + lo156
  let s159 := s158 + c155
  let c160 := hi157 + Fast.bit (s158 < lo156) + Fast.bit (s159 < c155)
  let lo161 := q151 * m2
  let hi162 := Fast.mulHi q151 m2
  let s163 := s142 + lo161
  let s164 := s163 + c160
  let c165 := hi162 + Fast.bit (s163 < lo161) + Fast.bit (s164 < c160)
  let lo166 := q151 * m3
  let hi167 := Fast.mulHi q151 m3
  let s168 := s147 + lo166
  let s169 := s168 + c165
  let c170 := hi167 + Fast.bit (s168 < lo166) + Fast.bit (s169 < c165)
  let s171 := s149 + c170
  let c172 := c150 + Fast.bit (s171 < c170)
  -- at most one modulus too large
  let r0 := s159
  let r1 := s164
  let r2 := s169
  let r3 := s171
  let over := c172 != 0 || (if r3 != m3 then r3 > m3 else if r2 != m2 then r2 > m2 else if r1 != m1 then r1 > m1 else r0 >= m0)
  if over then
    let k0 : UInt64 := if r0 < m0 then 1 else 0
    let k1 : UInt64 := if r1 < m1 || (r1 == m1 && k0 == 1) then 1 else 0
    let k2 : UInt64 := if r2 < m2 || (r2 == m2 && k1 == 1) then 1 else 0
    let d0 := r0 - m0
    let d1 := r1 - m1 - k0
    let d2 := r2 - m2 - k1
    let d3 := r3 - m3 - k2
    #[d0 &&& 0xFFFFFFFF, d0 >>> 32, d1 &&& 0xFFFFFFFF, d1 >>> 32, d2 &&& 0xFFFFFFFF, d2 >>> 32, d3 &&& 0xFFFFFFFF, d3 >>> 32]
  else
    #[r0 &&& 0xFFFFFFFF, r0 >>> 32, r1 &&& 0xFFFFFFFF, r1 >>> 32, r2 &&& 0xFFFFFFFF, r2 >>> 32, r3 &&& 0xFFFFFFFF, r3 >>> 32]

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
