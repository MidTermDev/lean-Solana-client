import Fast
import Encoding.Hex
import Crypto.Sha256

/-! `lib/Fast.lean` defines, in Lean, the operations `leanc` compiles to
single instructions. Here both are run on the same inputs: what this
prints under the official toolchain is the definitions' answer, and the
compiled program has to print the same, with the processor's own vector
instructions where it has them (and the definitions, compiled, where it
does not). -/

/-- A file of 40 registers with nothing regular about it. -/
def file : ByteArray := Id.run do
  let mut f := ByteArray.emptyWithCapacity 2560
  let mut x : UInt64 := 0x9E3779B97F4A7C15
  for _ in [0:2560] do
    x := x ^^^ (x <<< 13)
    x := x ^^^ (x >>> 7)
    x := x ^^^ (x <<< 17)
    f := f.push (x >>> 32).toUInt8
  return f

def digest (f : ByteArray) : String := Hex.encode ((Sha256.hash f).extract 0 12)

def main : IO Unit := do
  let f := file
  IO.println s!"the file: {digest f}"
  -- numbers in byte arrays, in range and across the end
  let mut line := ""
  for o in #[0, 1, 7, 2552, 2553, 2555, 2558, 2559, 2560, 5000] do
    line := line ++ s!" {Fast.le16 f o}/{Fast.le32 f o}/{Fast.le64 f o}"
  IO.println s!"reads:{line}"
  let mut g := f
  g := Fast.put16 g 3 0xBEEF
  g := Fast.put32 g 100 0x01234567
  g := Fast.put64 g 2552 0x0123456789ABCDEF
  g := Fast.put64 g 9 0xFFFFFFFFFFFFFFFF
  g := Fast.put32 g 21 0xFFFFFFFF00000000
  g := Fast.put16 g 2558 0x1FFFF
  IO.println s!"writes: {digest g}; the original is untouched: {digest f}"
  IO.println s!"high halves: {Fast.mulHi 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF} {Fast.mulHi 0x123456789ABCDEF0 0xFEDCBA9876543210} {Fast.mulHi 3 5} {Fast.mulHi 0x8000000000000000 2}"
  -- the vector operations: by instruction where the processor has them
  let wide := Fast.wide
  let mut v := f
  v := if wide then Fast.add32 v 3 1 2 else Fast.Ref.add32 v 3 1 2
  IO.println s!"add32: {digest v}"
  v := if wide then Fast.xor v 4 3 0 else Fast.Ref.xor v 4 3 0
  IO.println s!"xor: {digest v}"
  v := if wide then Fast.ror32 v 5 4 7 else Fast.Ref.ror32 v 5 4 7
  v := if wide then Fast.ror32 v 5 5 16 else Fast.Ref.ror32 v 5 5 16
  v := if wide then Fast.ror32 v 6 5 31 else Fast.Ref.ror32 v 6 5 31
  IO.println s!"ror32: {digest v}"
  v := if wide then Fast.and v 7 6 39 else Fast.Ref.and v 7 6 39
  IO.println s!"and: {digest v}"
  v := if wide then Fast.add16 v 8 7 6 else Fast.Ref.add16 v 8 7 6
  v := if wide then Fast.sub16 v 9 8 5 else Fast.Ref.sub16 v 9 8 5
  IO.println s!"add16, sub16: {digest v}"
  v := if wide then Fast.add64 v 10 9 8 else Fast.Ref.add64 v 10 9 8
  v := if wide then Fast.srl64 v 11 10 13 else Fast.Ref.srl64 v 11 10 13
  v := if wide then Fast.sll64 v 12 11 51 else Fast.Ref.sll64 v 12 11 51
  IO.println s!"add64, srl64, sll64: {digest v}"
  -- in place: a register may be an operand and the result
  v := if wide then Fast.add32 v 12 12 12 else Fast.Ref.add32 v 12 12 12
  v := if wide then Fast.xor v 39 39 0 else Fast.Ref.xor v 39 39 0
  IO.println s!"in place, and the last register: {digest v}"
  let ifma := Fast.ifma
  v := if ifma then Fast.madd52lo v 13 12 11 10 else Fast.Ref.madd52lo v 13 12 11 10
  v := if ifma then Fast.madd52hi v 14 13 9 8 else Fast.Ref.madd52hi v 14 13 9 8
  IO.println s!"madd52lo, madd52hi: {digest v}"
  v := if wide then Fast.move v 15 14 else Fast.Ref.move v 15 14
  v := if wide then Fast.set32 v 16 (Fast.le64 f 77) else Fast.Ref.set32 v 16 (Fast.le64 f 77)
  v := if wide then Fast.add32x3 v 17 16 15 14 else Fast.Ref.add32x3 v 17 16 15 14
  v := if wide then Fast.xorRor32 v 18 17 3 12 else Fast.Ref.xorRor32 v 18 17 3 12
  v := if wide then Fast.xorRor32 v 18 18 2 7 else Fast.Ref.xorRor32 v 18 18 2 7
  IO.println s!"move, set32, add32x3, xorRor32: {digest v}"
  v := if wide then Fast.unpackLow32 v 19 18 17 else Fast.Ref.unpackLow32 v 19 18 17
  v := if wide then Fast.unpackHigh32 v 20 18 17 else Fast.Ref.unpackHigh32 v 20 18 17
  v := if wide then Fast.unpackLow64 v 21 20 19 else Fast.Ref.unpackLow64 v 21 20 19
  v := if wide then Fast.unpackHigh64 v 22 20 19 else Fast.Ref.unpackHigh64 v 22 20 19
  v := if wide then Fast.shuffle128 v 23 22 21 0x88 else Fast.Ref.shuffle128 v 23 22 21 0x88
  v := if wide then Fast.shuffle128 v 24 22 21 0xDD else Fast.Ref.shuffle128 v 24 22 21 0xDD
  v := if wide then Fast.shuffle128 v 24 24 23 0x1B else Fast.Ref.shuffle128 v 24 24 23 0x1B
  v := if wide then Fast.unpackLow32 v 19 19 20 else Fast.Ref.unpackLow32 v 19 19 20
  IO.println s!"interleaving and picking quarters: {digest v}"
  v := if wide then Fast.quarter32 v 25 26 27 28 3 4 else Fast.Ref.quarter32 v 25 26 27 28 3 4
  v := if wide then Fast.quarter32 v 28 25 26 27 39 0 else Fast.Ref.quarter32 v 28 25 26 27 39 0
  IO.println s!"the quarter-round: {digest v}"
  IO.println s!"and the file they started from: {digest f}"
