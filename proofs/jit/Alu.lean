-- MIT, Copyright (c) 2026 MidTermDev. Source: lean-Solana-client b9fa957. See LICENSE.
-- Extracts of lib/Fast.lean, lib/Solana/Jit.lean and lib/Solana/SbpfBase.lean.
namespace Fast
/-- Writes the low four bytes of `v` at `o`. -/
def put32 (b : ByteArray) (o : Nat) (v : UInt64) : ByteArray := Id.run do
  let mut out := b
  for i in [0:4] do
    out := out.set! (o + i) (v >>> (8 * i).toUInt64).toUInt8
  return out

def push16 (b : ByteArray) (v : UInt64) : ByteArray := (b.push v.toUInt8).push (v >>> 8).toUInt8

/-- Appends the low four bytes of `v`. -/
def push32 (b : ByteArray) (v : UInt64) : ByteArray := push16 (push16 b v) (v >>> 16)

/-- Appends `v`, eight bytes. -/
def push64 (b : ByteArray) (v : UInt64) : ByteArray := push32 (push32 b v) (v >>> 32)

end Fast

namespace Sbpf
@[inline] def sext32 (x : UInt64) : UInt64 := ((x &&& 0xFFFFFFFF) ^^^ 0x80000000) - 0x80000000
/-- Arithmetic shift right by `n` (0..63). -/
def arsh (a n : UInt64) : UInt64 :=
  if n == 0 then a
  else if a &&& 0x8000000000000000 != 0 then (a >>> n) ||| (0xFFFFFFFFFFFFFFFF <<< (64 - n))
  else a >>> n

def bswap (x : UInt64) (bytes : Nat) : UInt64 := Id.run do
  let mut r : UInt64 := 0
  for i in [0:bytes] do
    r := (r <<< 8) ||| ((x >>> (8 * i).toUInt64) &&& 0xFF)
  return r

/-- The 64-bit operations. `op` is the high nibble of the opcode. Division by zero is the caller's problem. -/
def alu64 (op a b : UInt64) : UInt64 :=
  if op == 0x00 then a + b
  else if op == 0x10 then a - b
  else if op == 0x20 then a * b
  else if op == 0x30 then a / b
  else if op == 0x40 then a ||| b
  else if op == 0x50 then a &&& b
  else if op == 0x60 then a <<< (b &&& 63)
  else if op == 0x70 then a >>> (b &&& 63)
  else if op == 0x80 then 0 - a
  else if op == 0x90 then a % b
  else if op == 0xa0 then a ^^^ b
  else if op == 0xb0 then b
  else arsh a (b &&& 63)

/-- The 32-bit operations of sBPF v0. Add, subtract and multiply sign-extend
their 32-bit result to 64 bits; everything else zero-extends. -/
def alu32 (op a b : UInt64) : UInt64 :=
  let x := a &&& 0xFFFFFFFF
  let y := b &&& 0xFFFFFFFF
  if op == 0x00 then sext32 ((x + y) &&& 0xFFFFFFFF)
  else if op == 0x10 then sext32 ((x - y) &&& 0xFFFFFFFF)
  else if op == 0x20 then sext32 ((x * y) &&& 0xFFFFFFFF)
  else if op == 0x30 then x / y
  else if op == 0x40 then x ||| y
  else if op == 0x50 then x &&& y
  else if op == 0x60 then (x <<< (y &&& 31)) &&& 0xFFFFFFFF
  else if op == 0x70 then x >>> (y &&& 31)
  else if op == 0x80 then (0 - x) &&& 0xFFFFFFFF
  else if op == 0x90 then x % y
  else if op == 0xa0 then x ^^^ y
  else if op == 0xb0 then y
  else arsh (sext32 x) (y &&& 31) &&& 0xFFFFFFFF

end Sbpf

namespace Jit
def cTemp : Nat := 15

def rax : UInt64 := 0
def rdx : UInt64 := 2
def rbp : UInt64 := 5
/-- The machine register that holds sBPF register `g` (0-9). -/
def hostOf (g : UInt64) : UInt64 :=
  if g >= 4 then g + 4 else if g == 0 then 3 else if g == 1 then 7 else if g == 2 then 6 else 1

/-- What comes before the opcode: the operand-size prefix and REX. `w` is the width of the operation:
0 = 32 bits, 1 = 64, 2 = 16, 3 = 8 (which always takes a REX, so that registers 4-7 mean their low bytes). -/
def lead (b : ByteArray) (w reg index base : UInt64) : ByteArray :=
  let b := if w == 2 then b.push 0x66 else b
  let wide : UInt64 := if w == 1 then 0x48 else 0x40
  let rex := wide ||| ((reg >>> 3) <<< 2) ||| ((index >>> 3) <<< 1) ||| (base >>> 3)
  if rex != 0x40 || w == 3 then b.push rex.toUInt8 else b

/-- An opcode: one byte, or 0F and a byte if `op` is 0x100 or more. -/
def opcode (b : ByteArray) (op : UInt64) : ByteArray :=
  if op >= 0x100 then (b.push 0x0F).push (op &&& 0xFF).toUInt8 else b.push op.toUInt8

/-- `op reg, rm` on two registers. -/
def rr (b : ByteArray) (w op reg rm : UInt64) : ByteArray :=
  (opcode (lead b w reg 0 rm) op).push (((reg &&& 7) <<< 3) ||| (rm &&& 7) ||| 0xC0).toUInt8

/-- `op reg, [base + disp]`. -/
def rm (b : ByteArray) (w op reg base disp : UInt64) : ByteArray :=
  let b := opcode (lead b w reg 0 base) op
  let r := (reg &&& 7) <<< 3
  let low := base &&& 7
  let mode : UInt64 := if disp == 0 && low != 5 then 0 else if disp + 128 < 256 then 0x40 else 0x80
  let b := b.push (mode ||| r ||| low).toUInt8
  let b := if low == 4 then b.push 0x24 else b
  if mode == 0x40 then b.push disp.toUInt8 else if mode == 0x80 then Fast.push32 b disp else b

/-- Add (0), or (1), and (4), subtract (5), exclusive or (6), compare (7) a constant to a register. -/
def ri (b : ByteArray) (w ext reg imm : UInt64) : ByteArray :=
  if imm + 128 < 256 then (rr b w 0x83 ext reg).push imm.toUInt8
  else Fast.push32 (rr b w 0x81 ext reg) imm

/-- Loads a 64-bit constant in the shortest way. -/
def loadConstant (b : ByteArray) (reg value : UInt64) : ByteArray :=
  if value < 0x100000000 then
    Fast.push32 ((lead b 0 0 0 reg).push (0xB8 ||| (reg &&& 7)).toUInt8) value
  else if value >= 0xFFFFFFFF80000000 then
    Fast.push32 (rr b 1 0xC7 0 reg) value
  else
    Fast.push64 ((lead b 1 0 0 reg).push (0xB8 ||| (reg &&& 7)).toUInt8) value

/-- A shift by the count in any register (BMI2): 0 = left, 1 = right, 2 = right keeping the sign. -/
def shiftBy (b : ByteArray) (w which dst src count : UInt64) : ByteArray :=
  let pp : UInt64 := if which == 0 then 1 else if which == 1 then 3 else 2
  let b := b.push 0xC4
  let b := b.push ((((dst >>> 3) ^^^ 1) <<< 7) ||| (((src >>> 3) ^^^ 1) <<< 5) ||| 0x42).toUInt8
  let b := b.push ((w <<< 7) ||| ((count ^^^ 15) <<< 3) ||| pp).toUInt8
  (b.push 0xF7).push (((dst &&& 7) <<< 3) ||| (src &&& 7) ||| 0xC0).toUInt8

/-- A jump on condition `cc` whose target is not known yet; the four bytes to fill in are the last four. -/
def jumpIf (b : ByteArray) (cc : UInt64) : ByteArray :=
  Fast.push32 ((b.push 0x0F).push (0x80 ||| cc).toUInt8) 0

/-- A word of `cpu`, as a displacement from rbp. -/
@[inline] def slot (i : Nat) : UInt64 := (8 * i).toUInt64

/-- The ALU arm of classOf, returning kind 2 outside the two ALU classes. -/
def aluKind (opc s imm32 : UInt64) : UInt64 :=
  let cls := opc &&& 7
  let op := opc &&& 0xF0
  let named := opc &&& 8 != 0
  if cls == 7 || cls == 4 then
    if op == 0xd0 then (if cls == 4 && (imm32 == 16 || imm32 == 32 || imm32 == 64) then 0 else 2)
    else if op > 0xd0 then 2
    else if op == 0x30 || op == 0x90 then (if named then (if s == 10 then 2 else 0) else if imm32 == 0 then 2 else 0)
    else 0
  else 2

/-- Notes a way out: the jump whose last four bytes are at `site` leaves for the interpreter at
instruction `pc`, with `uncounted` instructions of the block counted and not run. -/
def fault (faults : Array UInt64) (site pc : Nat) (uncounted : UInt64) : Array UInt64 :=
  ((faults.push site.toUInt64).push pc.toUInt64).push uncounted

/-- Append one admitted ALU instruction. A guarded division records its rel32 field
at the same absolute offset used by the final fault-stub relocation pass. -/
def aluCode (b : ByteArray) (faults : Array UInt64) (pc : Nat) (uncounted : UInt64)
    (cls op d s : UInt64) (named : Bool) (imm32 : UInt64) : ByteArray × Array UInt64 := Id.run do
  let mut b := b
  let mut faults := faults
  let imm := Sbpf.sext32 imm32
  let w : UInt64 := if cls == 7 then 1 else 0
  let dh := hostOf d
  -- the second operand, if it is a register: r10 is fetched into rax
  if named && s == 10 then
    b := rm b 1 0x8B rax rbp (slot 10)
  let sh := if s == 10 then rax else hostOf s
  if op == 0x00 || op == 0x10 || op == 0x40 || op == 0x50 || op == 0xa0 then
    let ext : UInt64 := if op == 0x00 then 0 else if op == 0x10 then 5 else if op == 0x40 then 1 else if op == 0x50 then 4 else 6
    b := if named then rr b w (ext * 8 + 1) sh dh else ri b w ext dh imm
    if w == 0 && (op == 0x00 || op == 0x10) then
      b := rr b 1 0x63 dh dh                                -- the 32-bit sum, sign-extended
  else if op == 0x20 then
    b := if named then rr b w 0x1AF dh sh else Fast.push32 (rr b w 0x69 dh dh) imm
    if w == 0 then
      b := rr b 1 0x63 dh dh
  else if op == 0x30 || op == 0x90 then
    if named then
      b := rr b w 0x85 sh sh
      b := jumpIf b 4
      faults := fault faults (b.size - 4) pc uncounted
    else
      b := Fast.push32 (rm b w 0xC7 0 rbp (slot cTemp)) imm
    b := rr b w 0x89 dh rax
    b := rr b 0 0x31 rdx rdx
    b := if named then rr b w 0xF7 6 sh else rm b w 0xF7 6 rbp (slot cTemp)
    b := rr b w 0x89 (if op == 0x30 then rax else rdx) dh
  else if op == 0x60 || op == 0x70 || op == 0xc0 then
    let which : UInt64 := if op == 0x60 then 0 else if op == 0x70 then 1 else 2
    if named then
      b := shiftBy b w which dh dh sh
    else
      let n := imm &&& (if w == 1 then 63 else 31)
      if n == 0 then
        b := if w == 0 then rr b 0 0x89 dh dh else b
      else
        b := (rr b w 0xC1 (if which == 0 then 4 else if which == 1 then 5 else 7) dh).push n.toUInt8
  else if op == 0x80 then
    b := rr b w 0xF7 3 dh
  else if op == 0xb0 then
    if named then
      b := if s == 10 then rr b w 0x89 rax dh else rr b w 0x89 sh dh
    else
      b := loadConstant b dh (if w == 1 then imm else imm32)
  else
    -- byte order: the low 2, 4 or 8 bytes, reversed if `named`
    if imm32 == 16 then
      if named then
        b := (rr b 2 0xC1 0 dh).push 8                      -- rol r16, 8
      b := rr b 0 0x1B7 dh dh                               -- movzx r32, r16
    else if imm32 == 32 then
      b := if named then ((lead b 0 0 0 dh).push 0x0F).push (0xC8 ||| (dh &&& 7)).toUInt8 else rr b 0 0x89 dh dh
    else if named then
      b := ((lead b 1 0 0 dh).push 0x0F).push (0xC8 ||| (dh &&& 7)).toUInt8
  return (b, faults)

end Jit
