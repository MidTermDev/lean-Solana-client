/-!
# Reed–Solomon erasure coding over GF(2⁸)

Given `data` equal-sized pieces, compute `total - data` more such that any
`data` of the `total` are enough to rebuild all of them. Solana sends every
32 data shreds with 32 coding shreds made this way.

Each byte position is treated separately: the `data` bytes at that position
are a vector over the field with 256 elements, and each coded byte is a
fixed linear combination of them. The combinations are the rows of a matrix
built so that every square sub-matrix of rows is invertible: start from a
Vandermonde matrix (row `r` is 1, r, r², …) and multiply by the inverse of
its top square, which turns the first `data` rows into the identity, so the
data pieces are sent unchanged.

Arithmetic follows the `reed-solomon-erasure` crate, which Solana uses:
the field is built on the polynomial x⁸ + x⁴ + x³ + x² + 1 with generator 2.
-/

namespace ReedSolomon

/-- `logTable[x]` is the power of 2 that gives `x`. -/
def logTable : ByteArray := Id.run do
  let mut t := ByteArray.emptyWithCapacity 256
  for _ in [0:256] do
    t := t.push 0
  let mut b := 1
  for log in [0:255] do
    t := t.set! b log.toUInt8
    b := b * 2
    if b >= 256 then
      b := (b - 256) ^^^ 29
  return t

/-- `expTable[i]` is 2 to the power `i`, for `i` up to 509 so that two logarithms can be added without reducing. -/
def expTable : ByteArray := Id.run do
  let mut t := ByteArray.emptyWithCapacity 510
  for _ in [0:510] do
    t := t.push 0
  for i in [1:256] do
    let log := logTable[i]!.toNat
    t := t.set! log i.toUInt8
    t := t.set! (log + 255) i.toUInt8
  return t

def mul (a b : UInt8) : UInt8 :=
  if a == 0 || b == 0 then 0 else expTable[logTable[a.toNat]!.toNat + logTable[b.toNat]!.toNat]!

def inv (a : UInt8) : UInt8 := expTable[255 - logTable[a.toNat]!.toNat]!

def pow (a : UInt8) (n : Nat) : UInt8 :=
  if n == 0 then 1 else if a == 0 then 0 else expTable[(logTable[a.toNat]!.toNat * n) % 255]!

/-- Inverts an `n` × `n` matrix stored row by row. Returns an empty array if it is singular. -/
def invert (m : ByteArray) (n : Nat) : ByteArray := Id.run do
  -- Gauss–Jordan on [m | identity]
  let w := 2 * n
  let mut a := ByteArray.emptyWithCapacity (n * w)
  for r in [0:n] do
    for c in [0:n] do
      a := a.push m[r * n + c]!
    for c in [0:n] do
      a := a.push (if r == c then 1 else 0)
  for col in [0:n] do
    -- find a row with a non-zero entry in this column and bring it up
    let mut pivot := col
    while pivot < n && a[pivot * w + col]! == 0 do
      pivot := pivot + 1
    if pivot == n then
      return ByteArray.empty
    if pivot != col then
      for c in [0:w] do
        let x := a[col * w + c]!
        a := a.set! (col * w + c) a[pivot * w + c]!
        a := a.set! (pivot * w + c) x
    let scale := inv a[col * w + col]!
    for c in [0:w] do
      a := a.set! (col * w + c) (mul a[col * w + c]! scale)
    for r in [0:n] do
      let f := a[r * w + col]!
      if r != col && f != 0 then
        for c in [0:w] do
          a := a.set! (r * w + c) (a[r * w + c]! ^^^ mul f a[col * w + c]!)
  let mut out := ByteArray.emptyWithCapacity (n * n)
  for r in [0:n] do
    for c in [0:n] do
      out := out.push a[r * w + n + c]!
  return out

/-- The `total` × `data` encoding matrix: the identity on top, the coding rows below. -/
def matrix (data total : Nat) : ByteArray := Id.run do
  let mut top := ByteArray.emptyWithCapacity (data * data)
  for r in [0:data] do
    for c in [0:data] do
      top := top.push (pow r.toUInt8 c)
  let topInverse := invert top data
  let mut m := ByteArray.emptyWithCapacity (total * data)
  for r in [0:total] do
    for c in [0:data] do
      let mut x : UInt8 := 0
      for k in [0:data] do
        x := x ^^^ mul (pow r.toUInt8 k) topInverse[k * data + c]!
      m := m.push x
  return m

/-- Adds `coefficient` × `piece` into `acc`, byte by byte. The products of the
coefficient with all 256 byte values are tabulated first, so each byte costs one lookup. -/
def accumulate (acc piece : ByteArray) (coefficient : UInt8) : ByteArray := Id.run do
  if coefficient == 0 then
    return acc
  let shift := logTable[coefficient.toNat]!.toNat
  let mut products := (ByteArray.emptyWithCapacity 256).push 0
  for x in [1:256] do
    products := products.push expTable[shift + logTable[x]!.toNat]!
  let mut out := acc
  for i in [0:piece.size] do
    out := out.set! i (out[i]! ^^^ products[piece[i]!.toNat]!)
  return out

/-- The matrix for Solana's sets of 32 data and 32 coding shreds, computed once. -/
def matrix3264 : ByteArray := matrix 32 64

/-- Fills in the missing pieces. `pieces` has `total` entries, the first
`data` of them the data, all of one size; missing ones are empty. Returns
all `total` pieces, or an empty array if fewer than `data` are present.
With `coding` unset only the data pieces are filled in. -/
def reconstruct (data total : Nat) (pieces : Array ByteArray) (coding : Bool) : Array ByteArray := Id.run do
  let m := if data == 32 && total == 64 then matrix3264 else matrix data total
  let mut present : Array Nat := Array.emptyWithCapacity data
  let mut size := 0
  for i in [0:total] do
    if pieces[i]!.size != 0 && present.size < data then
      present := present.push i
      size := pieces[i]!.size
  if present.size < data then
    return Array.emptyWithCapacity 0
  -- the rows of the matrix that produced the pieces we have, inverted, give the data back
  let mut sub := ByteArray.emptyWithCapacity (data * data)
  for i in present do
    sub := sub ++ m.extract (i * data) (i * data + data)
  let decode := invert sub data
  if decode.size == 0 then
    return Array.emptyWithCapacity 0
  let mut zero := ByteArray.emptyWithCapacity size
  for _ in [0:size] do
    zero := zero.push 0
  let mut out := pieces
  for j in [0:data] do
    if out[j]!.size == 0 then
      let mut acc := zero
      for k in [0:data] do
        acc := accumulate acc pieces[present[k]!]! decode[j * data + k]!
      out := out.set! j acc
  for j in [data:total] do
    if coding && out[j]!.size == 0 then
      let mut acc := zero
      for k in [0:data] do
        acc := accumulate acc out[k]! m[j * data + k]!
      out := out.set! j acc
  return out

end ReedSolomon
