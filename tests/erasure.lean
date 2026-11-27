import Solana.Shred

/-! Rebuilding shreds that never arrived.

`tests/blocks/mainnet-set-474338900-416.shreds` is one set of shreds from
Solana mainnet: its 32 data shreds as validators serve them, and the 25 of
its 32 coding shreds that happened to reach this node over turbine.

Removing data shreds and rebuilding them from the coding shreds must give
back the leader's shreds byte for byte, Merkle paths included: that checks
the Reed–Solomon arithmetic against the code that produced the block, and
the reconstruction of the Merkle tree against the root the leader signed. -/

def none_ : Array ByteArray := Array.emptyWithCapacity 0

/-- `shreds` without those at the positions listed in `drop`. -/
def without (shreds : Array ByteArray) (drop : Array Nat) : Array ByteArray := Id.run do
  let mut out := shreds
  for i in drop do
    out := out.set! i ByteArray.empty
  return out

def range (from_ to : Nat) : Array Nat := Id.run do
  let mut out : Array Nat := Array.emptyWithCapacity (to - from_)
  for i in [from_:to] do
    out := out.push i
  return out

def same (a b : Array ByteArray) : Bool := Id.run do
  if a.size != b.size then
    return false
  for i in [0:a.size] do
    if a[i]! != b[i]! then
      return false
  return true

def report (label : String) (original rebuilt : Array ByteArray) : IO Unit := do
  if rebuilt.size != 32 then
    IO.println s!"{label}: could not be rebuilt"
  else
    let mut identical := 0
    for i in [0:32] do
      if rebuilt[i]! == original[i]! then
        identical := identical + 1
    IO.println s!"{label}: {identical} of 32 data shreds identical to the leader's"

def main : IO Unit := do
  let file ← IO.FS.readBinFile "tests/blocks/mainnet-set-474338900-416.shreds"
  let mut data : Array ByteArray := Array.emptyWithCapacity 32
  let mut code : Array ByteArray := Array.emptyWithCapacity 32
  let mut codeCount := 0
  for i in [0:32] do
    data := data.push (file.extract (1203 * i) (1203 * i + 1203))
  for j in [0:32] do
    let c := file.extract (38496 + 1228 * j) (38496 + 1228 * j + 1228)
    if (Shred.parse c).ok then
      code := code.push c
      codeCount := codeCount + 1
    else
      code := code.push ByteArray.empty
  let first := Shred.parse data[0]!
  IO.println s!"slot {first.slot}, data shreds {first.index} to {first.index + 31}, {codeCount} of 32 coding shreds"
  let root := Shred.merkleRoot data[0]! first
  let mut agree := 0
  for d in data do
    if Shred.merkleRoot d (Shred.parse d) == root then
      agree := agree + 1
  for c in code do
    if c.size != 0 && Shred.merkleRoot c (Shred.parse c) == root then
      agree := agree + 1
  IO.println s!"shreds on a Merkle path to the same root: {agree} of {32 + codeCount}"

  report "5 data shreds missing" data (Shred.recoverSet (without data #[0, 5, 6, 17, 31]) code)
  report "the first 16 missing" data (Shred.recoverSet (without data (range 0 16)) code)
  -- as few as can work: 7 data shreds and 25 coding shreds make 32
  report "25 missing, 7 left" data (Shred.recoverSet (without data (range 7 32)) code)
  -- one fewer and it cannot be done
  report "26 missing, 6 left" data (Shred.recoverSet (without data (range 6 32)) code)
  report "nothing missing" data (Shred.recoverSet data code)
  report "no coding shreds" data (Shred.recoverSet (without data #[3]) (without code (range 0 32)))
  -- a shred that is not what the leader sent: the rebuilt set no longer hashes to the signed root
  let wrong := data[9]!.set! 300 (data[9]![300]! ^^^ 1)
  report "a data shred altered" data (Shred.recoverSet (without (data.set! 9 wrong) #[0, 1]) code)
  let wrongCode := code[0]!.set! 500 (code[0]![500]! ^^^ 1)
  report "a coding shred altered" data (Shred.recoverSet (without data (range 20 32)) (code.set! 0 wrongCode))

  -- the arithmetic on its own: 4 pieces extended to 7, any 4 of which give back the rest
  let pieces : Array ByteArray := #["first piece..".toUTF8, "second piece.".toUTF8, "third piece..".toUTF8, "fourth piece.".toUTF8,
    ByteArray.empty, ByteArray.empty, ByteArray.empty]
  let coded := ReedSolomon.reconstruct 4 7 pieces true
  let lost := ((coded.set! 0 ByteArray.empty).set! 2 ByteArray.empty).set! 5 ByteArray.empty
  let back := ReedSolomon.reconstruct 4 7 lost true
  IO.println s!"4 of 7 pieces give back all 7: {same back coded}; the data is sent unchanged: {coded[1]! == pieces[1]!}"
  IO.println s!"3 of 7 are not enough: {(ReedSolomon.reconstruct 4 7 (lost.set! 1 ByteArray.empty) true).size == 0}"
  -- the field: 2 generates all 255 non-zero elements, and every one has an inverse
  let mut inverses := 0
  for x in [1:256] do
    if ReedSolomon.mul x.toUInt8 (ReedSolomon.inv x.toUInt8) == 1 then
      inverses := inverses + 1
  IO.println s!"elements with an inverse: {inverses} of 255; 2 to the 255th: {ReedSolomon.pow 2 255}"
