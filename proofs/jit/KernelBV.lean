import Std

namespace Certificate.Bits

/-- Enumerate the *output bit index* of a word identity. Operands remain symbolic. -/
def below (p : Nat → Prop) : Nat → Prop
  | 0 => True
  | n+1 => p n ∧ below p n

theorem below_apply {p : Nat → Prop} {n : Nat} (h : below p n) {i : Nat} (hi : i < n) : p i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases h with ⟨last, first⟩
    by_cases eq : i = n
    · simpa [eq] using last
    · exact ih first (by omega)

theorem bit_ext {n : Nat} {x y : BitVec n}
    (h : below (fun i => x.getLsbD i = y.getLsbD i) n) : x = y :=
  BitVec.eq_of_getLsbD_eq fun _ hi => below_apply h hi

theorem mask5 (x : BitVec 64) : x % 32#64 = x &&& 31#64 := by
  apply BitVec.eq_of_toNat_eq
  exact (Nat.and_two_pow_sub_one_eq_mod x.toNat 5).symm

theorem mask6 (x : BitVec 64) : x % 64#64 = x &&& 63#64 := by
  apply BitVec.eq_of_toNat_eq
  exact (Nat.and_two_pow_sub_one_eq_mod x.toNat 6).symm

theorem mask8 (x : BitVec 64) : x % 256#64 = x &&& 255#64 := by
  apply BitVec.eq_of_toNat_eq
  exact (Nat.and_two_pow_sub_one_eq_mod x.toNat 8).symm

theorem mask16 (x : BitVec 64) : x % 65536#64 = x &&& 65535#64 := by
  apply BitVec.eq_of_toNat_eq
  exact (Nat.and_two_pow_sub_one_eq_mod x.toNat 16).symm

theorem mask32 (x : BitVec 64) : x % 4294967296#64 = x &&& 4294967295#64 := by
  apply BitVec.eq_of_toNat_eq
  exact (Nat.and_two_pow_sub_one_eq_mod x.toNat 32).symm

macro "each_bit" : tactic => `(tactic| (
  first | apply UInt64.toBitVec_inj.mp | apply UInt32.toBitVec_inj.mp |
    apply UInt8.toBitVec_inj.mp | skip
  apply bit_ext
  simp only [below, and_true]
  repeat' apply And.intro
  all_goals simp (config := {ground := true}) [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
      BitVec.getLsbD_ofNat, mask5, mask6, mask8, mask16, mask32] <;> try rfl))

-- Use the bv_decide normalizer where it can finish by rewriting alone.
macro "word_decide" : tactic => `(tactic| first | rfl | (solve | bv_normalize) | (solve | omega) | each_bit)
end Certificate.Bits
