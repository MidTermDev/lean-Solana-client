import Crypto.Mont

/-!
# The Poseidon hash

A hash built from arithmetic modulo a prime, which makes it cheap to prove
things about inside a zero-knowledge proof; programs use it for Merkle trees
they will later prove membership in. Solana offers the variant circom uses:
the BN254 scalar field, fifth powers, eight full rounds.

The state is one more number than there are inputs. A round adds constants,
raises to the fifth power (every number in a full round, only the first in
a partial one) and multiplies by a fixed matrix.

Its constants are not arbitrary: the designers' script draws them from a
shift register seeded with the parameters, and so does this, rather than
carrying six thousand numbers.
-/

namespace Poseidon

/-- The order of the BN254 curve's group: the field the hash works in. -/
def modulus : Mont.Num := #[0xF0000001, 0x43E1F593, 0x79B97091, 0x2833E848, 0x8181585D, 0xB85045B6, 0xE131A029, 0x30644E72]

def field : Mont.Field := Mont.Field.make modulus

/-- Partial rounds, for 1 to 12 inputs. -/
def partialRounds : Array Nat := #[56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65]

/-- The designers' generator: an 80-bit shift register. Its seed says what
the constants are for (a prime field, this exponent, 254 bits, the width,
the round counts). Each output bit is kept or dropped according to the bit
before it. -/
structure Grain where
  bits : Array UInt64
  at_ : Nat

def Grain.step (g : Grain) : UInt64 × Grain :=
  let b := g.bits
  let i := g.at_
  let new := b[(i + 62) % 80]! ^^^ b[(i + 51) % 80]! ^^^ b[(i + 38) % 80]! ^^^ b[(i + 23) % 80]! ^^^ b[(i + 13) % 80]! ^^^ b[i]!
  (new, ⟨b.set! i new, (i + 1) % 80⟩)

def Grain.start (width fullRounds partials : Nat) : Grain := Id.run do
  let mut bits : Array UInt64 := Array.emptyWithCapacity 80
  -- field kind (2 bits: 1), S-box kind (4 bits: 0), then four numbers, then thirty ones
  let fields : Array Nat := #[1, 0, 254, width, fullRounds, partials]
  let widths : Array Nat := #[2, 4, 12, 12, 10, 10]
  for k in [0:6] do
    for j in [0:widths[k]!] do
      bits := bits.push ((fields[k]! >>> (widths[k]! - 1 - j)) % 2).toUInt64
  for _ in [0:30] do
    bits := bits.push 1
  let mut g : Grain := ⟨bits, 0⟩
  for _ in [0:160] do
    let (_, next) := g.step
    g := next
  return g

/-- The next 254-bit number from the generator, as eight digits. -/
def Grain.number (g0 : Grain) : Mont.Num × Grain := Id.run do
  let mut g := g0
  let mut digits : Mont.Num := Array.replicate 8 0
  let mut produced := 0
  while produced < 254 do
    let (keep, g1) := g.step
    let (bit, g2) := g1.step
    g := g2
    if keep == 1 then
      -- most significant bit first
      let position := 253 - produced
      digits := digits.set! (position / 32) (digits[position / 32]! ||| (bit <<< (position % 32).toUInt64))
      produced := produced + 1
  return (digits, g)

/-- The constants for a state of `width` numbers: one per number per round, then the matrix, all in Montgomery form. -/
structure Parameters where
  width : Nat
  partials : Nat
  constants : Array Mont.Num
  matrix : Array Mont.Num

def parameters (width : Nat) : Parameters := Id.run do
  let partials := partialRounds[width - 2]!
  let f := field
  let mut g := Grain.start width 8 partials
  -- round constants: numbers at or above the modulus are passed over
  let mut constants : Array Mont.Num := Array.emptyWithCapacity ((8 + partials) * width)
  while constants.size < (8 + partials) * width do
    let (v, next) := g.number
    g := next
    if !(Mont.atLeast v modulus) then
      constants := constants.push (f.enter v)
  -- the matrix: 1 / (x_i + y_j) for numbers x and y drawn next (these are reduced, not passed over)
  let mut drawn : Array Mont.Num := Array.emptyWithCapacity (2 * width)
  for _ in [0:2 * width] do
    let (v, next) := g.number
    g := next
    drawn := drawn.push (f.enter (if Mont.atLeast v modulus then Mont.subRaw v modulus else v))
  let mut matrix : Array Mont.Num := Array.emptyWithCapacity (width * width)
  for i in [0:width] do
    for j in [0:width] do
      matrix := matrix.push (Mont.inv f (Mont.addMod modulus drawn[i]! drawn[width + j]!))
  return ⟨width, partials, constants, matrix⟩

-- Generating a set of constants takes far longer than hashing with it, so each is made once, when first used.
def parameters2 : Parameters := parameters 2
def parameters3 : Parameters := parameters 3
def parameters4 : Parameters := parameters 4
def parameters5 : Parameters := parameters 5
def parameters6 : Parameters := parameters 6
def parameters7 : Parameters := parameters 7
def parameters8 : Parameters := parameters 8
def parameters9 : Parameters := parameters 9
def parameters10 : Parameters := parameters 10
def parameters11 : Parameters := parameters 11
def parameters12 : Parameters := parameters 12
def parameters13 : Parameters := parameters 13

/-- The constants for a state of 2 to 13 numbers. -/
def parametersFor (width : Nat) : Parameters :=
  if width == 2 then parameters2 else if width == 3 then parameters3 else if width == 4 then parameters4
  else if width == 5 then parameters5 else if width == 6 then parameters6 else if width == 7 then parameters7
  else if width == 8 then parameters8 else if width == 9 then parameters9 else if width == 10 then parameters10
  else if width == 11 then parameters11 else if width == 12 then parameters12 else parameters13

def fifth (f : Mont.Field) (x : Mont.Num) : Mont.Num :=
  let x2 := Mont.mul f x x
  Mont.mul f (Mont.mul f x2 x2) x

/-- The permutation, on a state in Montgomery form. -/
def permute (p : Parameters) (state0 : Array Mont.Num) : Array Mont.Num := Id.run do
  let f := field
  let t := p.width
  let mut state := state0
  for round in [0:8 + p.partials] do
    let mut next : Array Mont.Num := Array.emptyWithCapacity t
    for i in [0:t] do
      let v := Mont.addMod modulus state[i]! p.constants[round * t + i]!
      next := next.push (if round < 4 || round >= 4 + p.partials || i == 0 then fifth f v else v)
    let mut mixed : Array Mont.Num := Array.emptyWithCapacity t
    for i in [0:t] do
      let mut sum := Mont.zero
      for j in [0:t] do
        sum := Mont.addMod modulus sum (Mont.mul f p.matrix[i * t + j]! next[j]!)
      mixed := mixed.push sum
    state := mixed
  return state

/-- The hash of 1 to 12 inputs, each at most 32 bytes and below the modulus,
read and written most significant byte first or last. Empty if the inputs
cannot be hashed. -/
def hash (inputs : Array ByteArray) (bigEndian : Bool) : ByteArray := Id.run do
  if inputs.size == 0 || inputs.size > 12 then
    return ByteArray.empty
  let f := field
  let mut state : Array Mont.Num := Array.emptyWithCapacity (inputs.size + 1)
  state := state.push Mont.zero
  for input in inputs do
    if input.size == 0 || input.size > 32 then
      return ByteArray.empty
    -- a shorter input is the same number with fewer digits
    let mut padded := ByteArray.emptyWithCapacity 32
    if bigEndian then
      for _ in [0:32 - input.size] do
        padded := padded.push 0
      padded := padded ++ input
    else
      padded := padded ++ input
      for _ in [0:32 - input.size] do
        padded := padded.push 0
    let v := Mont.ofBytes padded 0 bigEndian
    if Mont.atLeast v modulus then
      return ByteArray.empty
    state := state.push (f.enter v)
  let out := permute (parametersFor (inputs.size + 1)) state
  return Mont.toBytes (f.leave out[0]!) bigEndian

end Poseidon
