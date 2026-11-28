import Plan
import Sign

namespace Certificate
open X86
set_option maxHeartbeats 3000000

@[simp] theorem narrow32 (x : UInt64) : narrow false x = x &&& 0xffffffff := by
  unfold narrow; word_decide
@[simp] theorem narrow64 (x : UInt64) : narrow true x = x := rfl
@[simp] theorem sx_id (x : UInt64) : sx32 x = Sbpf.sext32 x := by
  exact UInt64.toNat_inj.mp ((sx32_nat x).trans (sext_nat x).symm)

theorem imm_long (x : UInt32) :
    sx32 (Sbpf.sext32 x.toUInt64).toUInt32.toUInt64 = Sbpf.sext32 x.toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp only [sx32_nat, sext_nat, UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
  split <;> split <;> omega

theorem imm_short (x : UInt32) (h : Sbpf.sext32 x.toUInt64 + 128 < 256) :
    sx8 (Sbpf.sext32 x.toUInt64).toUInt8.toUInt64 = Sbpf.sext32 x.toUInt64 := by
  apply UInt64.toNat_inj.mp
  change (Sbpf.sext32 x.toUInt64 + 128).toNat < 256 at h
  simp (config := {ground := true}) only [sx8_nat, UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, UInt64.toNat_add,
    sext_nat, UInt32.toNat_toUInt64] at *
  split at h <;> split <;> split <;> omega

theorem shift_value (k : Shift) (w : Bool) (x y : UInt64) :
    narrow w (shift w k x y) =
      let op := match k with | .shl => Op.shl | .shr => .shr | .sar => .sar
      if w then Sbpf.alu64 op.nibble x y else Sbpf.alu32 op.nibble x y := by
  cases k <;> cases w <;>
    simp [shift, Op.nibble, Sbpf.alu64, Sbpf.alu32, Sbpf.arsh, UInt64.and_assoc] <;>
    repeat' (split <;> simp_all)
  apply UInt64.toNat_inj.mp
  simp (config := {ground := true}) only [UInt64.toNat_and, natMask]
  apply Nat.mod_eq_of_lt
  rw [UInt64.toNat_shiftRight]
  exact Nat.lt_of_le_of_lt (Nat.shiftRight_le ..) (by simp [natMask, Nat.mod_lt])

private def byteFold (v : UInt64) (n : Nat) : UInt64 :=
  match n with
  | 0 => 0
  | k+1 => (byteFold v k <<< 8) ||| ((v >>> (8*k).toUInt64) &&& 255)

private theorem swap2 (v : UInt64) : Sbpf.bswap v 2 = byteFold v 2 := by
  simp [Sbpf.bswap, byteFold, List.range', Id.run] <;> rfl
private theorem swap4 (v : UInt64) : Sbpf.bswap v 4 = byteFold v 4 := by
  simp [Sbpf.bswap, byteFold, List.range', Id.run] <;> rfl
private theorem swap8 (v : UInt64) : Sbpf.bswap v 8 = byteFold v 8 := by
  simp [Sbpf.bswap, byteFold, List.range', Id.run] <;> rfl

theorem big16 (v : UInt64) :
    ((v &&& 0xffffffffffff0000) ||| (UInt64.ofBitVec (((v.toBitVec.truncate 16).rotateLeft 8).zeroExtend 64))).toUInt16.toUInt64 =
    Sbpf.bswap (v &&& 65535) 2 := by rw [swap2]; simp [byteFold]; word_decide

theorem big32 (v : UInt64) : narrow false (reverseBytes 4 v) = Sbpf.bswap (v &&& 0xffffffff) 4 := by
  rw [swap4]; simp [byteFold, reverseBytes]; each_bit

theorem big64 (v : UInt64) : reverseBytes 8 v = Sbpf.bswap v 8 := by
  rw [swap8]; simp [byteFold, reverseBytes]; each_bit
end Certificate
