import Solana.Alpenglow
import Encoding.Hex
import Encoding.Base58

/-! The BLS12-381 curve and the certificates built on it: points and their
compressed forms, the point a message hashes to, signatures by four keys
alone and added up, and the rule for when a footer's certificate proves a
block final.

`make oracle` prints the same report with the Rust library the validators
use (blstrs, through tests/oracle), and the two must agree. -/

open Bls12381

def hex (b : ByteArray) : String := Hex.encode b

def verdict (ok : Bool) : String := if ok then "holds" else "does not hold"

/-- A bitmap naming these ranks, of `count`. -/
def bitmapOf (ranks : Array Nat) (count : Nat) : ByteArray := Id.run do
  let mut b := Fast.pushZeros (Fast.push16 (ByteArray.empty.push 0) count.toUInt64) ((count + 7) / 8)
  for r in ranks do
    b := b.set! (3 + r / 8) (b[3 + r / 8]! ||| (1 <<< (r % 8).toUInt8))
  return b

/-- The sum of these validators' signatures (one each, by rank), compressed. -/
def sumOf (signatures : Array Point) (ranks : Array Nat) : ByteArray := Id.run do
  let mut sum := Point.infinity
  for r in ranks do
    sum := sum.add signatures[r]!
  return sum.toBytes true

/-- A footer that calls `slot` final: one aggregate, or two. -/
def footer (slot : UInt64) (block : ByteArray) (signatures bitmaps : Array ByteArray) : Alpenglow.Certs := Id.run do
  let mut b := Wire.putU64 (ByteArray.empty.push 1) slot ++ block
  for k in [0:signatures.size] do
    if k == 1 then
      b := b.push 1
    b := Wire.putU16 (b ++ signatures[k]!) bitmaps[k]!.size.toUInt64 ++ bitmaps[k]!
  if signatures.size == 1 then
    b := b.push 0
  return Alpenglow.parse ((b.push 0).push 0)

/-- Does a footer prove the block final, with these ranks having voted for it and these that its slot is final (none: only the first vote)? -/
def claim (signers : Alpenglow.Signers) (block : ByteArray) (forBlock forSlot : Array Point) (forIt final : Array Nat) (version : UInt64) : Bool :=
  if final.size == 0 then Alpenglow.finalProven (footer 474737400 block #[sumOf forBlock forIt] #[bitmapOf forIt 4]) signers version
  else Alpenglow.finalProven (footer 474737400 block #[sumOf forSlot final, sumOf forBlock forIt] #[bitmapOf final 4, bitmapOf forIt 4]) signers version

/-- Is a point on the twisted curve, `y² = x³ + 4(1 + u)`? -/
def onTwist (p : Point) : Bool :=
  let q := p.affine
  q.y.sqr.same ((q.x.sqr.mul q.x).add ⟨small 4, small 4⟩)

def reading (b : ByteArray) : String :=
  match Point.ofBytes b with
  | some _ => "accepted"
  | none => "rejected"

def readsBack (p : Point) : Bool :=
  match Point.ofBytes (p.toBytes true) with
  | some q => q.same p
  | none => false

def main : IO Unit := do
  IO.println s!"generator        {hex (generator.toBytes false)}"
  IO.println s!"twice it         {hex (generator.double.toBytes false)}"
  IO.println s!"minus it         {hex (generator.neg.toBytes false)}"
  let none_ := Point.infinity.toBytes true
  IO.println s!"no point         {hex none_}"
  for text in #["", "abc", "a vote"] do
    IO.println s!"point of \"{text}\": {hex ((hashToCurve text.toUTF8 Alpenglow.voteDomain).toBytes true)}"

  -- four validators: their secrets, their stakes (most first, so this is their rank order)
  let secrets : Array (Array UInt64) := #[#[1, 0, 0, 0], #[0x1234567890abcdef, 0x0fedcba098765432, 7, 0],
    #[0x0102030405060708, 0x1112131415161718, 0x2122232425262728, 0x3132333435363738], #[42, 42, 42, 42]]
  let stakes : Array UInt64 := #[40, 30, 20, 10]
  let mut block := ByteArray.emptyWithCapacity 32
  for i in [0:32] do
    block := block.push (7 * i + 1).toUInt8
  let forBlock := Alpenglow.vote 1 474737400 block 50093
  let forSlot := Alpenglow.vote 2 474737400 ByteArray.empty 50093
  IO.println s!"a vote for a block:     {hex forBlock}"
  IO.println s!"a vote a slot is final: {hex forSlot}"
  let mut voters : Array Snapshot.Voter := Array.emptyWithCapacity 4
  let mut blockVotes : Array Point := Array.emptyWithCapacity 4
  let mut slotVotes : Array Point := Array.emptyWithCapacity 4
  for k in [0:4] do
    let key := generator.scale secrets[k]!
    let signature := (hashToCurve forBlock Alpenglow.voteDomain).scale secrets[k]!
    IO.println s!"validator {k}: key {hex (key.toBytes false)}"
    IO.println s!"  signs the block {hex (signature.toBytes true)}"
    if k == 1 then
      IO.println s!"  which {verdict (verify key forBlock Alpenglow.voteDomain signature)}; for the other vote it {verdict (verify key forSlot Alpenglow.voteDomain signature)}; read back: {readsBack signature}"
    voters := voters.push ⟨(ByteArray.empty.push k.toUInt8), (ByteArray.empty.push k.toUInt8), stakes[k]!, key.toBytes false, ByteArray.empty, 0⟩
    blockVotes := blockVotes.push signature
    slotVotes := slotVotes.push ((hashToCurve forSlot Alpenglow.voteDomain).scale secrets[k]!)
  let signers := Alpenglow.signers 1099 voters
  IO.println s!"all keys added   {hex (signers.all.toBytes false)}, stake {signers.total}"

  -- aggregates: the stake behind each, or 0 if it is not their signature
  let all := #[0, 1, 2, 3]
  let nobody : Array Nat := Array.emptyWithCapacity 0
  IO.println s!"all four sign:   {hex (sumOf blockVotes all)}"
  IO.println s!"stake behind it: {Alpenglow.signedStake signers (bitmapOf all 4) (sumOf blockVotes all) forBlock}; behind 0, 1 and 3: {Alpenglow.signedStake signers (bitmapOf #[0, 1, 3] 4) (sumOf blockVotes #[0, 1, 3]) forBlock}"
  IO.println s!"a bitmap naming one who did not sign: {Alpenglow.signedStake signers (bitmapOf all 4) (sumOf blockVotes #[0, 1, 2]) forBlock}; the other vote: {Alpenglow.signedStake signers (bitmapOf all 4) (sumOf blockVotes all) forSlot}"
  IO.println s!"a rank that does not exist: {Alpenglow.signedStake signers (bitmapOf #[0, 1, 2, 5] 6) (sumOf blockVotes #[0, 1, 2]) forBlock}; nobody: {Alpenglow.signedStake signers (bitmapOf nobody 4) none_ forBlock}"

  -- when a block is final: four fifths voted for it, or three fifths did and three fifths that its slot is final
  IO.println s!"80 of 100 vote for the block: final {claim signers block blockVotes slotVotes #[0, 1, 3] nobody 50093}; 70: {claim signers block blockVotes slotVotes #[0, 1] nobody 50093}"
  IO.println s!"60 for the block and 60 that the slot is final: {claim signers block blockVotes slotVotes #[0, 2] #[1, 2, 3] 50093}; 60 and 50: {claim signers block blockVotes slotVotes #[0, 2] #[0, 3] 50093}"
  IO.println s!"another shred version: {claim signers block blockVotes slotVotes all nobody 50094}; no validators known: {Alpenglow.finalProven (footer 474737400 block #[sumOf blockVotes all] #[bitmapOf all 4]) (Alpenglow.signers 1100 (Array.emptyWithCapacity 0)) 50093}"

  -- a point of the twisted curve that is not in the group signatures live in
  let stray := (mapToCurve ⟨small 5, small 6⟩).toBytes true
  IO.println s!"a point outside the group: {hex stray}"
  IO.println s!"read as a signature: {reading stray} (it is on the curve: {onTwist (mapToCurve ⟨small 5, small 6⟩)}); a byte of a good one changed: {reading ((sumOf blockVotes all).set! 95 0)}"

  -- a validator's BLS key is derived from its identity key; with it goes a proof that its holder has the secret
  let seed := Sha256.hash "a validator".toUTF8
  let identity := Ed25519.publicKey seed
  let secret := Alpenglow.blsSecret seed identity
  let blsKey := (generator.scale secret).toBytes false
  let proof := ((hashToCurve ("ALPENGLOW".toUTF8 ++ identity ++ blsKey) Alpenglow.proofDomain).scale secret).toBytes true
  IO.println s!"the BLS key of identity {Base58.encode identity}: {hex blsKey}"
  IO.println s!"its proof of holding it, for a vote account at that address: {hex proof}"
  IO.println s!"which holds: {Alpenglow.possessed identity blsKey proof}; for another account: {Alpenglow.possessed seed blsKey proof}"
