import Crypto.Merlin
import Crypto.Ed25519
import Solana.Wire

/-!
# The proofs of the ZK ElGamal proof program

Token accounts can keep their balances encrypted. Whoever changes one must
then show, without revealing any amount, that the change is sound: that a
key is one whose secret is known, that a ciphertext holds zero, that two
hold the same amount, that an amount fits in so many bits. The proofs are
checked by a program built into the validator; this file is the checks.

An amount `x` is committed to as `x·G + r·H`, for two generators G and H and
a random `r`; a ciphertext is such a commitment with a handle `r·P` for each
key `P` that may read it. Each proof is a few points and numbers answering a
challenge drawn from a transcript (Merlin) of everything the proof is about,
and holds when some equations between points do. The validators check a
proof's equations in one sum, each times a power of a further challenge;
here each is checked by itself, which accepts the same proofs: those whose
equations all hold. Only the range proof, which is one equation over
hundreds of points, is checked as they do.

A proof arrives as 32-byte parts: first what it is about (its context:
keys, ciphertexts, commitments), then the proof's own points and numbers.
-/

namespace ZkProof
open Ed25519

/-- The second generator, H: G's encoding hashed (SHA3-512) to a point, so that nobody knows how the two are related. -/
def h : Point := Ristretto.fromUniform (Keccak.sponge (Ristretto.encode basePoint) 6 72 64)

/-- `Σ sᵢ·Pᵢ` with one chain of doublings; scalars are 32 little-endian bytes. -/
def combine (scalars : Array ByteArray) (points : Array Point) : Point := Id.run do
  let mut tables : Array (Array Point) := Array.emptyWithCapacity points.size
  for q in points do
    tables := tables.push (Point.table q)
  let mut r := Point.identity
  for i in [0:64] do
    r := Point.dbl (Point.dbl (Point.dbl (Point.dbl r)))
    for k in [0:points.size] do
      let n := nibble scalars[k]! (63 - i)
      if n != 0 then
        r := Point.add r tables[k]![n]!
  return r

/-- The transcript a proof of this kind starts from. -/
def transcript (label : String) : Merlin.Transcript :=
  (Merlin.Transcript.new "solana-zk-elgamal-proof-program-v1").append "dom-sep" label.toUTF8

/-- A challenge: 64 bytes drawn from the transcript, as a number modulo the group's order. -/
def challenge (t : Merlin.Transcript) (label : String) : Merlin.Transcript × ByteArray :=
  let (u, bytes) := t.challenge label 64
  (u, scReduce bytes)

/-- How the point that is nothing (the sum's zero) is written. -/
def noPoint : ByteArray := Fast.pushZeros ByteArray.empty 32

def part (d : ByteArray) (i : Nat) : ByteArray := d.extract (32 * i) (32 * i + 32)

/-- The points written in the first `count` parts of `d`: fewer, if one of them is not a point. -/
def points (d : ByteArray) (count : Nat) : Array Point := Id.run do
  let mut out : Array Point := Array.emptyWithCapacity count
  for i in [0:count] do
    match Ristretto.decode (part d i) with
    | none => return out
    | some p => out := out.push p
  return out

/-- Is each of these parts of `d` a point other than nothing, if it is a point at all? -/
def present (d : ByteArray) (which : Array Nat) : Bool := Id.run do
  for i in which do
    if part d i == noPoint then
      return false
  return true

/-- Is each of these parts of `d` a number below the group's order? -/
def canonical (d : ByteArray) (which : Array Nat) : Bool := Id.run do
  for i in which do
    if !(scIsCanonical (part d i)) then
      return false
  return true

/-- Adds consecutive parts of `d`, from part `first` on, to the transcript under these labels. -/
def appendParts (t : Merlin.Transcript) (labels : Array String) (d : ByteArray) (first : Nat) : Merlin.Transcript := Id.run do
  let mut u := t
  for k in [0:labels.size] do
    u := u.append labels[k]! (part d (first + k))
  return u

/-- Is `Σ sᵢ·Pᵢ` the point written as `y`? -/
def equals (scalars : Array ByteArray) (pts : Array Point) (y : ByteArray) : Bool :=
  Ristretto.encode (combine scalars pts) == y

-- ------------------------------------------------- proofs that are a few equations

/-- Proof 4: the holder of an encryption key `P = s⁻¹·H` knows `s`. Parts: P; Y, z. -/
def pubkeyValidity (d : ByteArray) : Bool :=
  let q := points d 1
  let t := ((transcript "pubkey-validity-instruction").append "pubkey" (part d 0)).append "dom-sep" "pubkey-proof".toUTF8
  let (_, c) := challenge (t.append "Y" (part d 1)) "c"
  q.size == 1 && present d #[0, 1] && canonical d #[2]
    && equals #[part d 2, c] #[h, q[0]!.neg] (part d 1)

/-- Proof 1: a ciphertext (C, D) under the key P holds zero. Parts: P, C, D; Y_P, Y_D, z. -/
def zeroCiphertext (d : ByteArray) : Bool :=
  let q := points d 3
  let t := ((transcript "zero-ciphertext-instruction").append "pubkey" (part d 0)).append "ciphertext" (d.extract 32 96)
  let (_, c) := challenge (appendParts (t.append "dom-sep" "zero-ciphertext-proof".toUTF8) #["Y_P", "Y_D"] d 3) "c"
  let z := part d 5
  q.size == 3 && present d #[0, 1, 2, 3] && canonical d #[5]
    && equals #[z, c] #[q[0]!, h.neg] (part d 3) && equals #[z, c] #[q[2]!, q[1]!.neg] (part d 4)

/-- Proof 3: a ciphertext (C, D) under the key P and a commitment hold the same amount.
Parts: P, C, D, the commitment; Y₀, Y₁, Y₂, z_s, z_x, z_r. -/
def commitmentEquality (d : ByteArray) : Bool :=
  let q := points d 4
  let t := (((transcript "ciphertext-commitment-equality-instruction").append "pubkey" (part d 0)).append "ciphertext" (d.extract 32 96)).append "commitment" (part d 3)
  let (_, c) := challenge (appendParts (t.append "dom-sep" "ciphertext-commitment-equality-proof".toUTF8) #["Y_0", "Y_1", "Y_2"] d 4) "c"
  let zs := part d 7
  let zx := part d 8
  q.size == 4 && present d #[0, 1, 2, 3, 4, 5, 6] && canonical d #[7, 8, 9]
    && equals #[zs, c] #[q[0]!, h.neg] (part d 4)
    && equals #[zx, zs, c] #[basePoint, q[2]!, q[1]!.neg] (part d 5)
    && equals #[zx, part d 9, c] #[basePoint, h, q[3]!.neg] (part d 6)

/-- Proof 2: two ciphertexts under two keys hold the same amount.
Parts: P₁, P₂, C₁, D₁, C₂, D₂; Y₀ to Y₃, z_s, z_x, z_r. -/
def ciphertextEquality (d : ByteArray) : Bool :=
  let q := points d 6
  let t := (((transcript "ciphertext-ciphertext-equality-instruction").append "first-pubkey" (part d 0)).append "second-pubkey" (part d 1)).append "first-ciphertext" (d.extract 64 128)
  let u := (t.append "second-ciphertext" (d.extract 128 192)).append "dom-sep" "ciphertext-ciphertext-equality-proof".toUTF8
  let (_, c) := challenge (appendParts u #["Y_0", "Y_1", "Y_2", "Y_3"] d 6) "c"
  let zs := part d 10
  let zx := part d 11
  let zr := part d 12
  q.size == 6 && present d #[0, 1, 2, 3, 6, 7, 8, 9] && canonical d #[10, 11, 12]
    && equals #[zs, c] #[q[0]!, h.neg] (part d 6)
    && equals #[zx, zs, c] #[basePoint, q[3]!, q[2]!.neg] (part d 7)
    && equals #[zx, zr, c] #[basePoint, h, q[4]!.neg] (part d 8)
    && equals #[zr, c] #[q[1]!, q[5]!.neg] (part d 9)

/-- A small number as a scalar. -/
def scalarOf (x : UInt64) : ByteArray := Fast.pushZeros (Fast.push64 ByteArray.empty x) 24

/-- Proof 5: a fee is the stated percentage of an amount, or the most a fee may be (which of the two is
not told). Parts: three commitments (to the fee, to what rounding leaves, to what is claimed to be left)
and the cap as 8 bytes; Y_max, z_max, c_max, Y_delta, Y_claimed, z_x, z_delta, z_claimed. -/
def percentageWithCap (d : ByteArray) : Bool :=
  let q := points d 3
  let proof := d.extract 104 d.size
  let cap := Wire.u64 d 96
  let t := appendParts (transcript "percentage-with-cap-instruction") #["percentage-commitment", "delta-commitment", "claimed-commitment"] d 0
  let u := ((t.append64 "max-value" cap).append "dom-sep" "percentage-with-cap-proof".toUTF8).append "Y_max_proof" (part proof 0)
  let (_, c) := challenge (appendParts u #["Y_delta", "Y_claimed"] proof 3) "c"
  let own := part proof 2
  let other := scSub c own
  let zx := part proof 5
  q.size == 3 && present d #[0, 1, 2] && present proof #[0, 3, 4] && canonical proof #[1, 2, 5, 6, 7]
    && equals #[part proof 1, scMul own (scalarOf cap), own] #[h, basePoint, q[0]!.neg] (part proof 0)
    && equals #[zx, part proof 6, other] #[basePoint, h, q[1]!.neg] (part proof 3)
    && equals #[zx, part proof 7, other] #[basePoint, h, q[2]!.neg] (part proof 4)

/-- Proofs 9 to 12: a ciphertext with a handle for each of two or three keys is well formed: every
handle is the commitment's `r` times its key. A batch is two such ciphertexts (the low and high halves
of an amount) shown at once, as low + t·high for a challenge t.
Parts: the keys; the commitment and the handles (twice, for a batch); Y₀ to Y_handles, z_r, z_x. -/
def validity (d : ByteArray) (handles : Nat) (batched : Bool) (label : String) : Bool := Id.run do
  let count := if batched then 3 * handles + 2 else 2 * handles + 1
  let q := points d count
  if q.size != count then
    return false
  let mut t := appendParts (transcript label) (if handles == 2 then #["first-pubkey", "second-pubkey"] else #["first-pubkey", "second-pubkey", "third-pubkey"]) d 0
  let width := 32 * (handles + 1)
  -- the commitment and the handles the equations are about
  let mut about : Array Point := Array.emptyWithCapacity (handles + 1)
  if batched then
    t := (t.append "grouped-ciphertext-lo" (d.extract (32 * handles) (32 * handles + width))).append "grouped-ciphertext-hi" (d.extract (32 * handles + width) (32 * handles + 2 * width))
    let (u, scale) := challenge ((t.append "dom-sep" "batched-validity-proof".toUTF8).append64 "handles" handles.toUInt64) "t"
    t := u
    for k in [0:handles + 1] do
      about := about.push (combine #[scOne, scale] #[q[handles + k]!, q[2 * handles + 1 + k]!])
  else
    t := t.append "grouped-ciphertext" (d.extract (32 * handles) (32 * handles + width))
    for k in [0:handles + 1] do
      about := about.push q[handles + k]!
  t := (t.append "dom-sep" "validity-proof".toUTF8).append64 "handles" handles.toUInt64
  let proof := d.extract (32 * count) d.size
  for k in [0:handles + 1] do
    t := t.append s!"Y_{k}" (part proof k)
  let (_, c) := challenge t "c"
  let zr := part proof (handles + 1)
  -- every key but the last, the commitments and every Y but the last must be points other than nothing
  let mut ok := canonical proof #[handles + 1, handles + 2] && part d handles != noPoint && (!batched || part d (2 * handles + 1) != noPoint)
  for k in [0:handles - 1] do
    ok := ok && part d k != noPoint
  for k in [0:handles] do
    ok := ok && part proof k != noPoint
  ok := ok && equals #[zr, part proof (handles + 2), c] #[h, basePoint, about[0]!.neg] (part proof 0)
  for k in [1:handles + 1] do
    ok := ok && equals #[zr, c] #[q[k - 1]!, about[k]!.neg] (part proof k)
  return ok

-- ----------------------------------------------------------------- the range proof

/-- The first `count` generators of the chain with this label: SHAKE256 output, 64 bytes a point. -/
def generators (label : String) (count : Nat) : Array Point := Id.run do
  let bytes := Keccak.sponge ("GeneratorsChain".toUTF8 ++ label.toUTF8) 0x1f 136 (64 * count)
  let mut out : Array Point := Array.emptyWithCapacity count
  for i in [0:count] do
    out := out.push (Ristretto.fromUniform (bytes.extract (64 * i) (64 * i + 64)))
  return out

/-- Proofs 6 to 8: each of up to eight committed amounts fits in its stated number of bits, which add up
to `bits` (64, 128 or 256). This is a Bulletproof: the bits of all the amounts are committed to at once
(A, S), a polynomial built from them is committed to (T₁, T₂) and opened at a challenge (t_x and two
blinding numbers), and an inner-product argument folds the `bits`-long vectors in half log₂ `bits`
times (a pair L, R each time) down to two numbers a and b. All of it is one sum that must be nothing.
Parts: eight commitments (unused ones zero) and eight bit counts as bytes; then A, S, T₁, T₂, t_x,
its blinding, the bits' blinding, the pairs L, R, and a, b. -/
def rangeProof (d : ByteArray) (bits : Nat) : Bool := Id.run do
  let mut count := 0
  while count < 8 && part d count != noPoint do
    count := count + 1
  let mut total := 0
  let mut sound : Bool := count > 0
  for i in [0:8] do
    let width := d[256 + i]!.toNat
    if i < count then
      total := total + width
      sound := sound && width >= 1 && width <= 64
    else
      sound := sound && width == 0 && part d i == noPoint
  let proof := d.extract 264 d.size
  let rounds := (proof.size / 32 - 9) / 2
  let last := 7 + 2 * rounds
  let commitments := points d count
  let opening := points proof 4
  let folds := points (proof.extract 224 proof.size) (2 * rounds)
  if !sound || total != bits || commitments.size != count || opening.size != 4 || folds.size != 2 * rounds
      || !(present proof #[0, 1, 2, 3]) || !(canonical proof #[4, 5, 6, last, last + 1]) then
    return false
  -- the challenges
  let start := ((transcript "batched-range-proof-instruction").append "commitments" (d.extract 0 256)).append "bit-lengths" (d.extract 256 264)
  let (t1, y) := challenge (appendParts ((start.append "dom-sep" "range-proof".toUTF8).append64 "n" bits.toUInt64) #["A", "S"] proof 0) "y"
  let (t2, z) := challenge t1 "z"
  let (t3, x) := challenge (appendParts t2 #["T_1", "T_2"] proof 2) "x"
  let (t4, w) := challenge (appendParts t3 #["t_x", "t_x_blinding", "e_blinding"] proof 4) "w"
  let (t5, _) := challenge t4 "c"
  let mut t := (t5.append "dom-sep" "inner-product".toUTF8).append64 "n" bits.toUInt64
  let mut us : Array ByteArray := Array.emptyWithCapacity rounds
  for k in [0:rounds] do
    if !(present proof #[7 + 2 * k, 8 + 2 * k]) then
      return false
    let (next, u) := challenge (appendParts t #["L", "R"] proof (7 + 2 * k)) "u"
    t := next
    us := us.push u
  let (_, e) := challenge (appendParts t #["ipp_a", "ipp_b"] proof last) "d"
  let a := part proof last
  let b := part proof (last + 1)
  let tx := part proof 4
  -- the squares of the folding challenges and of their inverses, and for every position the product
  -- of u or 1/u over the rounds, by the position's bits
  let mut product := scOne
  for u in us do
    product := scMul product u
  let allInverse := scInvert product
  let mut squares : Array ByteArray := Array.emptyWithCapacity rounds
  let mut inverseSquares : Array ByteArray := Array.emptyWithCapacity rounds
  for k in [0:rounds] do
    let mut inverse := allInverse
    for j in [0:rounds] do
      if j != k then
        inverse := scMul inverse us[j]!
    squares := squares.push (scMul us[k]! us[k]!)
    inverseSquares := inverseSquares.push (scMul inverse inverse)
  let mut s : Array ByteArray := Array.emptyWithCapacity bits
  s := s.push allInverse
  let mut lg := 0
  let mut half := 1
  for i in [1:bits] do
    if i == 2 * half then
      half := i
      lg := lg + 1
    s := s.push (scMul s[i - half]! squares[rounds - 1 - lg]!)
  -- what the polynomial's constant term must be, given y and z
  let zz := scMul z z
  let mut sumY := scZero
  let mut yPower := scOne
  for _ in [0:bits] do
    sumY := scAdd sumY yPower
    yPower := scMul yPower y
  let mut delta := scMul (scSub z zz) sumY
  let mut zPower := scMul zz z
  for j in [0:count] do
    delta := scSub delta (scMul zPower (scalarOf (0xFFFFFFFFFFFFFFFF >>> (64 - d[256 + j]!.toUInt64))))
    zPower := scMul zPower z
  -- the sum: the proof's points, G and H, the fold pairs, the two chains of generators, the commitments
  let mut scalars : Array ByteArray := #[scOne, x, scMul e x, scMul e (scMul x x), scNeg (scAdd (part proof 6) (scMul e (part proof 5))),
    scAdd (scMul w (scSub tx (scMul a b))) (scMul e (scSub delta tx))]
  let mut pts : Array Point := (opening.push h).push basePoint
  for k in [0:rounds] do
    scalars := scalars.push squares[k]!
    pts := pts.push folds[2 * k]!
  for k in [0:rounds] do
    scalars := scalars.push inverseSquares[k]!
    pts := pts.push folds[2 * k + 1]!
  let minusZ := scNeg z
  let chainG := generators "G" bits
  for i in [0:bits] do
    scalars := scalars.push (scSub minusZ (scMul a s[i]!))
    pts := pts.push chainG[i]!
  let chainH := generators "H" bits
  let yInverse := scInvert y
  yPower := scOne
  zPower := zz
  let mut i := 0
  for j in [0:count] do
    let mut two := zPower
    for _ in [0:d[256 + j]!.toNat] do
      scalars := scalars.push (scAdd z (scMul yPower (scSub two (scMul b s[bits - 1 - i]!))))
      pts := pts.push chainH[i]!
      yPower := scMul yPower yInverse
      two := scAdd two two
      i := i + 1
    zPower := scMul zPower z
  zPower := scMul e zz
  for j in [0:count] do
    scalars := scalars.push zPower
    pts := pts.push commitments[j]!
    zPower := scMul zPower z
  return Ristretto.encode (combine scalars pts) == noPoint

-- ------------------------------------------------------------------ the program's table

/-- What an instruction of each kind costs in compute units (kind 0 closes a stored context). -/
def costs : Array UInt64 := #[3300, 6000, 8000, 6400, 2600, 6500, 111000, 200000, 368000, 6400, 13000, 8100, 16400]

/-- The size of a proof of each kind with its context, and of the context alone, which comes first. -/
def sizes : Array Nat := #[0, 192, 416, 320, 96, 360, 936, 1000, 1064, 320, 416, 416, 544]
def contexts : Array Nat := #[0, 96, 192, 128, 32, 104, 264, 264, 264, 160, 256, 224, 352]

/-- Does a proof of this kind (1 to 12), given with its context, hold? -/
def holds (kind : UInt8) (d : ByteArray) : Bool :=
  if kind == 1 then zeroCiphertext d
  else if kind == 2 then ciphertextEquality d
  else if kind == 3 then commitmentEquality d
  else if kind == 4 then pubkeyValidity d
  else if kind == 5 then percentageWithCap d
  else if kind == 6 then rangeProof d 64
  else if kind == 7 then rangeProof d 128
  else if kind == 8 then rangeProof d 256
  else if kind == 9 then validity d 2 false "grouped-ciphertext-validity-2-handles-instruction"
  else if kind == 10 then validity d 2 true "batched-grouped-ciphertext-validity-2-handles-instruction"
  else if kind == 11 then validity d 3 false "grouped-ciphertext-validity-3-handles-instruction"
  else kind == 12 && validity d 3 true "batched-grouped-ciphertext-validity-3-handles-instruction"

end ZkProof
