import Encoding

namespace Certificate
open X86

theorem natMask (x : Nat) : x &&& 0xffffffff = x % 0x100000000 :=
  Nat.and_two_pow_sub_one_eq_mod x 32

private theorem flip31 (n : Nat) (bound : n < 4294967296) :
    n ^^^ 2147483648 = if n < 2147483648 then n + 2147483648 else n - 2147483648 := by
  have lo := Nat.xor_mod_two_pow (a := n) (b := 2147483648) (n := 31)
  have hi := Nat.xor_div_two_pow (a := n) (b := 2147483648) (n := 31)
  simp (config := {ground := true}) at hi lo
  split
  · have q : n / 2147483648 = 0 := by omega
    simp [q] at hi
    omega
  · have q : n / 2147483648 = 1 := by omega
    simp [q] at hi
    omega

theorem sext_nat (x : UInt64) :
    (Sbpf.sext32 x).toNat =
      if x.toNat % 4294967296 < 2147483648 then x.toNat % 4294967296
      else x.toNat % 4294967296 + 18446744069414584320 := by
  simp [Sbpf.sext32, UInt64.toNat_sub, natMask, flip31 _ (Nat.mod_lt x.toNat (by decide : 0 < 4294967296))]
  split <;> omega

theorem sx32_nat (x : UInt64) : (sx32 x).toNat =
      if x.toNat % 4294967296 < 2147483648 then x.toNat % 4294967296
      else x.toNat % 4294967296 + 18446744069414584320 := by
  unfold sx32
  simp (config := {ground := true}) [BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  split <;> split <;> omega

theorem sx8_nat (x : UInt64) : (sx8 x).toNat =
      if x.toNat % 256 < 128 then x.toNat % 256
      else x.toNat % 256 + 18446744073709551360 := by
  unfold sx8
  simp (config := {ground := true}) [BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  split <;> split <;> omega

theorem sext_mod (i : UInt32) : Sbpf.sext32 i.toUInt64 % 4294967296 = i.toUInt64 := by
  apply UInt64.toNat_inj.mp
  have bound := i.toNat_lt
  simp (config := {ground := true}) [sext_nat]
  split <;> omega

theorem mask_cast (x : UInt64) : x &&& 0xffffffff = x.toUInt32.toUInt64 := by
  apply UInt64.toNat_inj.mp
  simp [natMask]

theorem sext_low (x : UInt64) : Sbpf.sext32 x &&& 0xffffffff = x &&& 0xffffffff := by
  apply UInt64.toNat_inj.mp
  simp [natMask, sext_nat]
  split <;> omega
end Certificate
