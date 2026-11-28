import KernelBV
import X86
import Alu

namespace Certificate
open X86

def width (w : Bool) : UInt64 := if w then 1 else 0
def ext : Bin → UInt64
  | .add => 0 | .bor => 1 | .band => 4 | .sub => 5 | .xor => 6 | _ => 0

def shiftExt : Shift → UInt64
  | .shl => 4 | .shr => 5 | .sar => 7
def which : Shift → UInt64
  | .shl => 0 | .shr => 1 | .sar => 2

/-- Use the production encoder primitives. Header decoding in X86 is independent. -/
def headBytes (f : Form) (b : ByteArray) : ByteArray :=
  match f with
  | .rr w .mul d s => Jit.rr b (width w) 0x1af d s
  | .rr w .mov d s => Jit.rr b (width w) 0x89 s d
  | .rr w k d s => Jit.rr b (width w) (ext k * 8 + 1) s d
  | .imulI w d s => Jit.rr b (width w) 0x69 d s
  | .grp w sh k d => Jit.rr b (width w) (if sh then 0x83 else 0x81) (ext k) d
  | .neg w d => Jit.rr b (width w) 0xf7 3 d
  | .shiftI w k d => Jit.rr b (width w) 0xc1 (shiftExt k) d
  | .bmi w k d s c => Jit.shiftBy b (width w) (which k) d s c
  | .movI d => (Jit.lead b 0 0 0 d).push (0xb8 ||| (d &&& 7)).toUInt8
  | .movS d => Jit.rr b 1 0xc7 0 d
  | .sxd d s => Jit.rr b 1 0x63 d s
  | .zx d s => Jit.rr b 0 0x1b7 d s
  | .rol16 d => Jit.rr b 2 0xc1 0 d
  | .swap w d => ((Jit.lead b (width w) 0 0 d).push 0x0f).push (0xc8 ||| (d &&& 7)).toUInt8
  | .frameLoad => Jit.rm b 1 0x8b 0 5 80
  | .tempStore w => Jit.rm b (width w) 0xc7 0 5 120
  | .test w a b' => Jit.rr b (width w) 0x85 b' a
  | .jz => (b.push 0x0f).push 0x84
  | .divR w s => Jit.rr b (width w) 0xf7 6 s
  | .divM w => Jit.rm b (width w) 0xf7 6 5 120

def emit (b : ByteArray) (i : Ins) : ByteArray :=
  let h := headBytes i.form b
  match i.form.size with
  | 1 => h.push i.imm.toUInt8
  | 4 => Fast.push32 h i.imm
  | _ => h

def wire (b : ByteArray) : List UInt8 := b.data.toList

@[simp] theorem wire_empty : wire ByteArray.empty = [] := rfl
@[simp] theorem wire_push (b : ByteArray) (x : UInt8) : wire (b.push x) = wire b ++ [x] := by
  simp [wire, ByteArray.push]

private theorem lead_append (b : ByteArray) (w r i d : UInt64) :
    wire (Jit.lead b w r i d) = wire b ++ wire (Jit.lead .empty w r i d) := by
  by_cases h : w = 2 <;> by_cases k : w = 1 <;> simp [Jit.lead, h, k] <;>
    split <;> simp_all [List.append_assoc]

private theorem opcode_append (b : ByteArray) (op : UInt64) :
    wire (Jit.opcode b op) = wire b ++ wire (Jit.opcode .empty op) := by
  unfold Jit.opcode
  split <;> simp

private theorem rr_append (b : ByteArray) (w op r d : UInt64) :
    wire (Jit.rr b w op r d) = wire b ++ wire (Jit.rr .empty w op r d) := by
  simp only [Jit.rr, wire_push]
  rw [opcode_append, lead_append, opcode_append (Jit.lead .empty ..)]
  simp [List.append_assoc]

private theorem head_append (b : ByteArray) (f : Form) :
    wire (headBytes f b) = wire b ++ wire (headBytes f .empty) := by
  cases f
  case rr w k d s => cases k <;> apply rr_append
  case bmi => simp [headBytes, Jit.shiftBy, List.append_assoc]
  all_goals first
    | apply rr_append
    | simp only [headBytes, wire_push, wire_empty, List.append_assoc,
        List.nil_append, List.cons_append]
      first | rfl | (rw [lead_append b]; simp [List.append_assoc])
    | simp [headBytes, Jit.rm, Jit.opcode, Jit.lead, width, List.append_assoc] <;>
        repeat' (split <;> simp_all [List.append_assoc])

def good (f : Form) : Bool := header.read (wire (headBytes f .empty)) == some (f, [])

def immBytes (i : Ins) : List UInt8 :=
  match i.form.size with
  | 1 => [i.imm.toUInt8]
  | 4 => [i.imm.toUInt8, (i.imm >>> 8).toUInt8, (i.imm >>> 16).toUInt8,
          (i.imm >>> 16 >>> 8).toUInt8]
  | _ => []

def raw (i : Ins) := wire (headBytes i.form .empty) ++ immBytes i

theorem wire_emit (b : ByteArray) (i : Ins) : wire (emit b i) = wire b ++ raw i := by
  unfold emit raw immBytes
  split <;> simp [Fast.push32, Fast.push16, head_append b, List.append_assoc]

def clipped (i : Ins) : Ins := { i with imm := match i.form.size with
  | 1 => i.imm.toUInt8.toUInt64 | 4 => i.imm.toUInt32.toUInt64 | _ => 0 }

private theorem assemble (v : UInt64) :
    v.toUInt8.toUInt64 ||| (((v >>> 8).toUInt8.toUInt64 |||
      (((v >>> 16).toUInt8.toUInt64 ||| ((v >>> 16 >>> 8).toUInt8.toUInt64 <<< 8)) <<< 8)) <<< 8)
      = v.toUInt32.toUInt64 := by each_bit

private theorem sizes (f : Form) : f.size = 0 ∨ f.size = 1 ∨ f.size = 4 := by
  cases f
  case grp w sh k d =>
    cases sh
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)
  all_goals first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)

private theorem read_imm (i : Ins) :
    (payload i.form.size).read (immBytes i) = some ((clipped i).imm, []) := by
  rcases sizes i.form with h|h|h <;> simp only [immBytes, clipped, h]
  · rfl
  · change some (_, []) = some (_, [])
    congr 2
    bv_decide
  · change some (_, []) = some (_, [])
    congr 2
    simpa only [UInt64.zero_shiftLeft, UInt64.or_zero] using assemble i.imm

theorem decode_raw (i : Ins) (h : good i.form = true) (rest : List UInt8) :
    decode.read (raw i ++ rest) = some (clipped i, rest) := by
  have hd : header.read (wire (headBytes i.form .empty)) = some (i.form, []) := by
    simpa [good] using h
  have h₁ := header.append_ok hd (immBytes i ++ rest)
  have h₂ := (payload i.form.size).append_ok (read_imm i) rest
  simp only [List.nil_append] at h₁ h₂
  change (header.read _).bind _ = _
  simp [raw, List.append_assoc, h₁, h₂, Reader.bindR, Reader.pureR, bind, pure]
  rfl
end Certificate
