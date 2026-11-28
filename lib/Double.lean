import Fast

/-!
# Double-precision arithmetic, in integers

The chain computes one thing in floating point that every node must get
bit for bit: how much an epoch may pay in rewards (`Solana.Epoch`). The
compiler here has no floating point, so these are the IEEE 754 operations
that formula needs, on the 64 bits of a double, rounding to nearest, ties
to even. They cover positive, finite, normal numbers and zero, which is all
the formula meets; `pow` further expects ½ ≤ x < 1 and 2⁻¹⁴⁰ ≤ y < 2¹¹.
-/

namespace Double

/-- A number's 53 significant bits, and the exponent field. -/
def parts (x : UInt64) : UInt64 × UInt64 := ((x &&& 0xFFFFFFFFFFFFF) ||| 0x10000000000000, (x >>> 52) &&& 0x7FF)

/-- The double nearest to `m × 2^(e − 1086)`, or just above it if `sticky`. -/
def round (m0 : UInt64) (sticky : Bool) (e0 : UInt64) : UInt64 := Id.run do
  if m0 == 0 then
    return 0
  let mut m := m0
  let mut e := e0
  while m >>> 63 == 0 do
    m := m <<< 1
    e := e - 1
  let rest := m &&& 0x7FF
  let mut kept := m >>> 11
  if rest > 0x400 || (rest == 0x400 && (sticky || kept &&& 1 == 1)) then
    kept := kept + 1
    if kept == 0x20000000000000 then
      kept := 0x10000000000000
      e := e + 1
  return (e <<< 52) ||| (kept &&& 0xFFFFFFFFFFFFF)

def ofU64 (n : UInt64) : UInt64 := round n false 1086

/-- The whole part (what `as u64` gives in Rust). -/
def toU64 (x : UInt64) : UInt64 :=
  let (m, e) := parts x
  if x == 0 || e < 1023 then 0 else if e > 1086 then 0xFFFFFFFFFFFFFFFF
  else if e >= 1075 then m <<< (e - 1075) else m >>> (1075 - e)

def mul (x y : UInt64) : UInt64 :=
  if x == 0 || y == 0 then 0
  else
    let (mx, ex) := parts x
    let (my, ey) := parts y
    round (Fast.mulHi (mx <<< 11) (my <<< 11)) ((mx <<< 11) * (my <<< 11) != 0) (ex + ey - 1022)

def div (x y : UInt64) : UInt64 := Id.run do
  if x == 0 then
    return 0
  let (mx, ex) := parts x
  let (my, ey) := parts y
  let mut q := mx / my
  let mut r := mx % my
  for _ in [0:63] do
    r := r <<< 1
    q := q <<< 1
    if r >= my then
      r := r - my
      q := q ||| 1
  return round q (r != 0) (ex + 1023 - ey)

/-- `x + y`, or with `minus` the difference of the two. -/
def combine (x y : UInt64) (minus : Bool) : UInt64 :=
  if x == 0 then y else if y == 0 then x
  else
    -- (for positive numbers, the larger has the larger bits)
    let (ma, ea) := parts (if x >= y then x else y)
    let (mb, eb) := parts (if x >= y then y else x)
    let d := ea - eb
    -- the smaller, lined up with the larger; anything pushed off its end is remembered in its last place
    let lost : UInt64 := if d >= 64 || ((mb <<< 10) >>> d) <<< d != mb <<< 10 then 1 else 0
    let lined : UInt64 := if d >= 64 then 0 else (mb <<< 10) >>> d
    let b := lined ||| lost
    round (if minus then (ma <<< 10) - b else (ma <<< 10) + b) false (ea + 1)

def add (x y : UInt64) : UInt64 := combine x y false
def sub (x y : UInt64) : UInt64 := combine x y true

-- `pow` works in fractions of 256 bits: four 64-bit digits, least first, the last one the whole part.

def wide (m e : UInt64) : Array UInt64 := Id.run do
  let shift := (e - 883).toNat
  let mut w : Array UInt64 := Array.replicate 5 0
  w := w.set! (shift / 64) (m <<< (shift % 64).toUInt64)
  if shift % 64 != 0 then
    w := w.set! (shift / 64 + 1) (m >>> (64 - shift % 64).toUInt64)
  return #[w[0]!, w[1]!, w[2]!, w[3]!]

def wideAdd (a b : Array UInt64) (minus : Bool) : Array UInt64 := Id.run do
  let mut r := a
  let mut carry : UInt64 := 0
  for i in [0:4] do
    let s := if minus then a[i]! - b[i]! - carry else a[i]! + b[i]! + carry
    carry := if minus then (if a[i]! < b[i]! || (a[i]! == b[i]! && carry == 1) then 1 else 0)
      else (if s < a[i]! || (s == a[i]! && carry == 1) then 1 else 0)
    r := r.set! i s
  return r

def wideMul (a b : Array UInt64) : Array UInt64 := Id.run do
  let mut r : Array UInt64 := Array.replicate 8 0
  for i in [0:4] do
    let mut carry : UInt64 := 0
    for j in [0:4] do
      let low := a[i]! * b[j]!
      let s := r[i + j]! + low
      let t := s + carry
      carry := Fast.mulHi a[i]! b[j]! + (if s < low then 1 else 0) + (if t < carry then 1 else 0)
      r := r.set! (i + j) t
    r := r.set! (i + 4) carry
  return #[r[3]!, r[4]!, r[5]!, r[6]!]

/-- Division by a small number (below 2³²). -/
def wideOver (a : Array UInt64) (k : UInt64) : Array UInt64 := Id.run do
  let mut r := a
  let mut rest : UInt64 := 0
  for back in [0:4] do
    let i := 3 - back
    let high := (rest <<< 32) ||| (a[i]! >>> 32)
    let low := ((high % k) <<< 32) ||| (a[i]! &&& 0xFFFFFFFF)
    r := r.set! i (((high / k) <<< 32) ||| (low / k))
    rest := low % k
  return r

def wideZero (a : Array UInt64) : Bool := a[0]! == 0 && a[1]! == 0 && a[2]! == 0 && a[3]! == 0

/-- `x` to the power `y`: as `exp(−y · −ln x)`, both series summed to 190 bits, so that the result is
the nearest double unless the true value lies within 2⁻¹²⁰ of the middle between two. -/
def pow (x y : UInt64) : UInt64 := Id.run do
  let (mx, ex) := parts x
  let (my, ey) := parts y
  let one : Array UInt64 := #[0, 0, 0, 1]
  -- −ln x = u + u²/2 + u³/3 + …, with u = 1 − x
  let u := wideAdd one (wide mx ex) true
  let mut power := u
  let mut log := u
  for k in [2:400] do
    power := wideMul power u
    log := wideAdd log (wideOver power k.toUInt64) false
  -- z = y · −ln x, halved until it is below one
  let mut z := wideMul (wide my ey) log
  let mut halvings := 0
  while z[3]! != 0 do
    z := wideOver z 2
    halvings := halvings + 1
  -- exp(−z) = 1 − z + z²/2! − …: the terms added and the terms taken away, summed apart
  let mut term := one
  let mut plus := one
  let mut less : Array UInt64 := #[0, 0, 0, 0]
  for k in [1:200] do
    term := wideOver (wideMul term z) k.toUInt64
    if k % 2 == 1 then
      less := wideAdd less term false
    else
      plus := wideAdd plus term false
  let mut r := wideAdd plus less true
  for _ in [0:halvings] do
    r := wideMul r r
  -- its first 64 bits, and whether anything follows them
  let mut top := 3
  while top > 0 && r[top]! == 0 do
    top := top - 1
  let mut m := r[top]!
  let mut e : UInt64 := 894 + 64 * top.toUInt64
  if m == 0 then
    return 0
  let mut below := if top == 0 then 0 else r[top - 1]!
  while m >>> 63 == 0 do
    m := (m <<< 1) ||| (below >>> 63)
    below := below <<< 1
    e := e - 1
  return round m (below != 0 || (top >= 2 && (r[top - 2]! != 0 || (top == 3 && r[0]! != 0)))) e

end Double
