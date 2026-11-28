import Semantics
import Arithmetic

namespace Certificate
open X86

private theorem bounded32 {x : UInt64} (h : x.toNat < 2^32) :
    x &&& 0xffffffff = x := by
  rw [← narrow32]
  apply UInt64.toNat_inj.mp
  simpa [narrow] using Nat.mod_eq_of_lt h

private theorem masked_bound (x : UInt64) : (x &&& 0xffffffff).toNat < 2^32 := by
  rw [← narrow32]
  simpa [narrow] using x.toUInt32.toNat_lt

private theorem quotient32 (x y : UInt64) :
    ((x &&& 0xffffffff) / y) &&& 0xffffffff = (x &&& 0xffffffff) / y := by
  apply bounded32
  rw [UInt64.toNat_div]
  exact Nat.lt_of_le_of_lt (Nat.div_le_self ..) (masked_bound x)

private theorem remainder32 (x y : UInt64) :
    ((x &&& 0xffffffff) % y) &&& 0xffffffff = (x &&& 0xffffffff) % y := by
  apply bounded32
  rw [UInt64.toNat_mod]
  exact Nat.lt_of_le_of_lt (Nat.mod_le ..) (masked_bound x)

private theorem zeroAx : reg 0 = 0 := rfl
private theorem twoDx : reg 2 = 2 := rfl
private theorem diff : (0 : Fin 16) ≠ 2 := by decide

theorem division_correct (rem w named : Bool) (d s g : UInt64) (i : UInt32) (m : State)
    (g0 : reg g ≠ 0) (g2 : reg g ≠ 2)
    (s0 : named = true → reg s ≠ 0) (s2 : named = true → reg s ≠ 2)
    (valid : named = false → i ≠ 0) (rel : UInt32 := 0) :
    observation g (execute (division w named rem d s (Sbpf.sext32 i.toUInt64) rel) m) =
      expected (reg g == reg d) (m.regs (reg g)) m.frame
        (reference (if rem then .umod else .udiv) w named i (m.regs (reg d)) (m.regs (reg s))) rel := by
  have low : Sbpf.sext32 i.toUInt64 &&& 0xffffffff = i.toUInt64  := by
    rw [sext_low, mask_cast, UInt32.toUInt32_toUInt64]
  have lowMod : Sbpf.sext32 i.toUInt64 % 0x100000000 = i.toUInt64 := sext_mod i
  have tmp : ((m.temp &&& 0xffffffff00000000) ||| i.toUInt64) &&& 0xffffffff = i.toUInt64 := by each_bit
  have long := imm_long i
  simp at long
  have nz32 : i ≠ 0 → i.toUInt64 ≠ 0  := by
    intro h e
    exact h (by simpa (config := {ground := true}) only [UInt32.toUInt32_toUInt64] using congrArg UInt64.toUInt32 e)
  have nz64 : i ≠ 0 → Sbpf.sext32 i.toUInt64 ≠ 0  := by
    intro h e
    apply nz32 h
    rw [← sext_mod i, e]
    rfl
  cases rem <;> cases w <;> cases named <;>
    by_cases hit : reg g = reg d <;>
    by_cases z : m.regs (reg s) = 0 <;>
    by_cases z32 : m.regs (reg s) &&& 0xffffffff = 0 <;>
    simp_all [division, execute, clipped, ins, exec, Form.size, State.write, bin, observation,
      expected, reference, Op.nibble, Sbpf.alu64, Sbpf.alu32, divide, zeroAx, twoDx, diff,
      Ne.symm diff, UInt64.and_assoc, quotient32, remainder32]
end Certificate
