import Semantics
import Division

namespace Certificate
open X86
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

private theorem arith_step (m : State) (w named : Bool) (k : Bin) (d s : UInt64) (i : UInt32) :
    exec (clipped (arith w named k d s (Sbpf.sext32 i.toUInt64))) m =
    .next (m.write d (narrow w (bin k (m.regs (reg d))
      (if named then m.regs (reg s) else Sbpf.sext32 i.toUInt64)))) := by
  cases named
  · have small := imm_short i
    have long := imm_long i
    simp at small long
    by_cases h : Sbpf.sext32 i.toUInt64 + 128 < 256
    · simp [exec, clipped, arith, ins, Form.size, h, small h, Id.run]
    · simp [exec, clipped, arith, ins, Form.size, h, long, Id.run]
  · rfl

/-- Raw host numbers may alias. Only the architectural scratch registers need to
be distinct from live mapped operands when a division is performed. -/
private def Law (op : Op) (w named : Bool) (d s g : UInt64) (i : UInt32) (m : State) :=
  observation g (execute (body op w named d s i) m) =
    expected (reg g == reg d) (m.regs (reg g)) m.frame
      (reference op w named i (m.regs (reg d)) (m.regs (reg s)))

private theorem basic_law (op : Op) (w named : Bool) (d s g : UInt64) (i : UInt32) (m : State)
    (h : op = .add ∨ op = .sub ∨ op = .bor ∨ op = .band ∨ op = .xor) :
    Law op w named d s g i m := by
  unfold Law
  rcases h with rfl|rfl|rfl|rfl|rfl <;> cases w <;> simp only [body, signTail, Bool.false_eq_true, ite_false, ite_true, execute, arith_step]
  all_goals simp [clipped, ins, exec, Form.size, State.write, bin, observation, expected,
    reference, Op.nibble, Sbpf.alu64, Sbpf.alu32, Id.run]
  all_goals by_cases h : reg g = reg d <;> simp only [h, ite_true, ite_false]
  all_goals first
    | (apply congrArg Sbpf.sext32; simp only [mask_cast, UInt64.toUInt32_add, UInt64.toUInt32_sub, UInt32.toUInt32_toUInt64])
    | each_bit

private theorem mul_law (w named : Bool) (d s g : UInt64) (i : UInt32) (m : State) :
    Law .mul w named d s g i m := by
  have long := imm_long i
  simp at long
  unfold Law
  cases w <;> cases named <;> by_cases h : reg g = reg d <;>
    simp [body, signTail, execute, clipped, ins, exec, Form.size, State.write, bin,
      observation, expected, reference, Op.nibble, Sbpf.alu64, Sbpf.alu32, h, long]
  all_goals apply congrArg Sbpf.sext32; simp only [mask_cast, UInt64.toUInt32_mul, UInt32.toUInt32_toUInt64]

private theorem neg_law (w named : Bool) (d s g : UInt64) (i : UInt32) (m : State) :
    Law .neg w named d s g i m := by
  unfold Law
  cases w <;> by_cases h : reg g = reg d <;>
    simp [body, execute, clipped, ins, exec, Form.size, State.write, observation, expected,
      reference, Op.nibble, Sbpf.alu64, Sbpf.alu32, h] <;> simp only [mask_cast, UInt64.toUInt32_neg, UInt32.toUInt32_toUInt64]

private theorem mov_law (w named : Bool) (d s g : UInt64) (i : UInt32) (m : State) :
    Law .mov w named d s g i m := by
  have long := imm_long i
  simp at long
  unfold Law
  cases w <;> cases named <;> by_cases hi : Sbpf.sext32 i.toUInt64 >= 0x100000000 <;> by_cases h : reg g = reg d <;>
    simp [body, execute, clipped, ins, exec, Form.size, State.write, bin, observation, expected,
      reference, Op.nibble, Sbpf.alu64, Sbpf.alu32, h, hi, long]
  all_goals apply UInt64.toNat_inj.mp
  all_goals simp (config := {ground := true}) [natMask, sext_nat, UInt64.le_iff_toNat_le] at *
  all_goals repeat' (split at * <;> simp_all)
  all_goals have bound := i.toNat_lt; omega

private theorem count_byte (w : Bool) (k : Shift) (a v : UInt64) :
    shift w k a (v &&& (if w then 63 else 31)).toUInt8.toUInt64 = shift w k a v := by
  have h : (v &&& (if w then 63 else 31)).toUInt8.toUInt64 &&& (if w then 63 else 31) =
      v &&& (if w then 63 else 31) := by cases w <;> each_bit
  simp only [shift, h]

private theorem shift_zero (w : Bool) (k : Shift) (a v : UInt64)
    (hz : v &&& (if w then 63 else 31) = 0) : narrow w (shift w k a v) = narrow w a := by
  cases w <;> cases k <;> simp_all [shift, UInt64.and_assoc, sext_low]

private theorem shift_effect (w named : Bool) (k : Shift) (d s g v : UInt64) (m : State) :
    observation g (execute (shifts w named k d s v) m) =
      expected (reg g == reg d) (m.regs (reg g)) m.frame
        (some (narrow w (shift w k (m.regs (reg d)) (if named then m.regs (reg s) else v)))) := by
  cases named
  · simp only [Bool.false_eq_true, ite_false]
    by_cases hz : v &&& (if w then 63 else 31) = 0
    · rw [shift_zero w k _ v hz]
      cases w <;> by_cases hit : reg g = reg d <;>
        simp_all [shifts, observation, execute, clipped, ins, exec, Form.size, bin, State.write, expected]
    · have hc := count_byte w k (m.regs (reg d)) v
      simp at hc
      simp [shifts, hz, observation, execute, clipped, ins, exec, Form.size, State.write, expected, hc]
  · rfl

private theorem shift_law (op : Op) (w named : Bool) (d s g : UInt64) (i : UInt32) (m : State)
    (whichOp : op = .shl ∨ op = .shr ∨ op = .sar) : Law op w named d s g i m := by
  rcases whichOp with rfl|rfl|rfl <;>
    simp only [Law, body, shift_effect, shift_value] <;> rfl

private theorem endian_law (w named : Bool) (d s g : UInt64) (i : UInt32) (m : State)
    (size : i = 16 ∨ i = 32 ∨ i = 64) : Law .endian w named d s g i m := by
  unfold Law
  rcases size with rfl|rfl|rfl <;> cases named <;> by_cases hit : reg g = reg d <;>
    simp [body, execute, clipped, ins, exec, Form.size, State.write, bin, observation, expected,
      reference, hit, big32, big64]
  all_goals first | (rw [← big16]; word_decide) | (rw [← big32]; simp [narrow32]) | word_decide

theorem host_scratch : ∀ (g : Fin 10), reg (host g) ≠ 0 ∧ reg (host g) ≠ 2 := by decide +kernel

private theorem source_scratch : ∀ (s : Fin 11), s.val ≠ 10 → reg (source s) ≠ 0 ∧ reg (source s) ≠ 2 := by
  decide +kernel

theorem host_eq : ∀ (g d : Fin 10), (reg (host g) == reg (host d)) = (g == d) := by decide +kernel

/-- A body step after the optional frame read. The only source restriction for
a register divide is the one already enforced by the translator. -/
theorem body_correct (op : Op) (w named : Bool) (d g : Fin 10) (s : Fin 11) (i : UInt32)
    (m : State) (ok : admitted op w named s i = true) :
    observation (host g) (execute (body op w named (host d) (source s) i) m) =
      expected (g == d) (m.regs (reg (host g))) m.frame
        (reference op w named i (m.regs (reg (host d))) (m.regs (reg (source s)))) := by
  rw [← host_eq]
  change Law op w named (host d) (source s) (host g) i m
  cases op
  case add | sub | bor | band | xor => exact basic_law _ _ _ _ _ _ _ _ (by simp)
  case shl | shr | sar => exact shift_law _ _ _ _ _ _ _ _ (by simp)
  case mul => apply mul_law
  case neg => apply neg_law
  case mov => apply mov_law
  case endian =>
    apply endian_law
    simp [admitted] at ok
    rcases ok.2 with (h|h)|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  case udiv =>
    apply division_correct (rel := 0) false w named _ _ _ _ _ (host_scratch g).1 (host_scratch g).2
    · rintro rfl; exact (source_scratch s (by simpa [admitted] using ok)).1
    · rintro rfl; exact (source_scratch s (by simpa [admitted] using ok)).2
    · rintro rfl; simpa [admitted] using ok
  case umod =>
    apply division_correct (rel := 0) true w named _ _ _ _ _ (host_scratch g).1 (host_scratch g).2
    · rintro rfl; exact (source_scratch s (by simpa [admitted] using ok)).1
    · rintro rfl; exact (source_scratch s (by simpa [admitted] using ok)).2
    · rintro rfl; simpa [admitted] using ok
end Certificate
