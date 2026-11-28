import Plan

namespace Certificate
open X86
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

@[local simp] private theorem addReg (w : Bool) (d : Fin 10) (s : Fin 11) :
    good (.rr w .add (host d) (source s)) = true := by decide +revert +kernel
@[local simp] private theorem addImm (w : Bool) (short : Bool) (d : Fin 10) :
    good (.grp w short .add (host d)) = true := by decide +revert +kernel
@[local simp] private theorem subReg (w : Bool) (d : Fin 10) (s : Fin 11) :
    good (.rr w .sub (host d) (source s)) = true := by decide +revert +kernel
@[local simp] private theorem subImm (w : Bool) (short : Bool) (d : Fin 10) :
    good (.grp w short .sub (host d)) = true := by decide +revert +kernel
@[local simp] private theorem mulReg (w : Bool) (d : Fin 10) (s : Fin 11) :
    good (.rr w .mul (host d) (source s)) = true := by decide +revert +kernel
@[local simp] private theorem borReg (w : Bool) (d : Fin 10) (s : Fin 11) :
    good (.rr w .bor (host d) (source s)) = true := by decide +revert +kernel
@[local simp] private theorem borImm (w : Bool) (short : Bool) (d : Fin 10) :
    good (.grp w short .bor (host d)) = true := by decide +revert +kernel
@[local simp] private theorem bandReg (w : Bool) (d : Fin 10) (s : Fin 11) :
    good (.rr w .band (host d) (source s)) = true := by decide +revert +kernel
@[local simp] private theorem bandImm (w : Bool) (short : Bool) (d : Fin 10) :
    good (.grp w short .band (host d)) = true := by decide +revert +kernel
@[local simp] private theorem xorReg (w : Bool) (d : Fin 10) (s : Fin 11) :
    good (.rr w .xor (host d) (source s)) = true := by decide +revert +kernel
@[local simp] private theorem xorImm (w : Bool) (short : Bool) (d : Fin 10) :
    good (.grp w short .xor (host d)) = true := by decide +revert +kernel
@[local simp] private theorem movReg (w : Bool) (d : Fin 10) (s : Fin 11) :
    good (.rr w .mov (host d) (source s)) = true := by decide +revert +kernel
@[local simp] private theorem shlReg (w : Bool) (d : Fin 10) (s : Fin 11) :
    good (.bmi w .shl (host d) (host d) (source s)) = true := by decide +revert +kernel
@[local simp] private theorem shlImm (w : Bool) (d : Fin 10) :
    good (.shiftI w .shl (host d)) = true := by decide +revert +kernel
@[local simp] private theorem shrReg (w : Bool) (d : Fin 10) (s : Fin 11) :
    good (.bmi w .shr (host d) (host d) (source s)) = true := by decide +revert +kernel
@[local simp] private theorem shrImm (w : Bool) (d : Fin 10) :
    good (.shiftI w .shr (host d)) = true := by decide +revert +kernel
@[local simp] private theorem sarReg (w : Bool) (d : Fin 10) (s : Fin 11) :
    good (.bmi w .sar (host d) (host d) (source s)) = true := by decide +revert +kernel
@[local simp] private theorem sarImm (w : Bool) (d : Fin 10) :
    good (.shiftI w .sar (host d)) = true := by decide +revert +kernel
@[local simp] private theorem frame  :
    good (.frameLoad) = true := by decide +revert +kernel
@[local simp] private theorem sx (d : Fin 10) :
    good (.sxd (host d) (host d)) = true := by decide +revert +kernel
@[local simp] private theorem zx (d : Fin 10) :
    good (.zx (host d) (host d)) = true := by decide +revert +kernel
@[local simp] private theorem imulImm (w : Bool) (d : Fin 10) :
    good (.imulI w (host d) (host d)) = true := by decide +revert +kernel
@[local simp] private theorem neg (w : Bool) (d : Fin 10) :
    good (.neg w (host d)) = true := by decide +revert +kernel
@[local simp] private theorem movSelf (d : Fin 10) :
    good (.rr false .mov (host d) (host d)) = true := by decide +revert +kernel
@[local simp] private theorem movImm (d : Fin 10) :
    good (.movI (host d)) = true := by decide +revert +kernel
@[local simp] private theorem movSigned (d : Fin 10) :
    good (.movS (host d)) = true := by decide +revert +kernel
@[local simp] private theorem rol (d : Fin 10) :
    good (.rol16 (host d)) = true := by decide +revert +kernel
@[local simp] private theorem swap (w : Bool) (d : Fin 10) :
    good (.swap w (host d)) = true := by decide +revert +kernel
@[local simp] private theorem temp (w : Bool) :
    good (.tempStore w) = true := by decide +revert +kernel
@[local simp] private theorem test (w : Bool) (s : Fin 11) :
    good (.test w (source s) (source s)) = true := by decide +revert +kernel
@[local simp] private theorem jz  :
    good (.jz) = true := by decide +revert +kernel
@[local simp] private theorem toAx (w : Bool) (d : Fin 10) :
    good (.rr w .mov 0 (host d)) = true := by decide +revert +kernel
@[local simp] private theorem clearDx  :
    good (.rr false .xor 2 2) = true := by decide +revert +kernel
@[local simp] private theorem divReg (w : Bool) (s : Fin 11) :
    good (.divR w (source s)) = true := by decide +revert +kernel
@[local simp] private theorem divMem (w : Bool) :
    good (.divM w) = true := by decide +revert +kernel
@[local simp] private theorem fromAx (w : Bool) (d : Fin 10) :
    good (.rr w .mov (host d) 0) = true := by decide +revert +kernel
@[local simp] private theorem fromDx (w : Bool) (d : Fin 10) :
    good (.rr w .mov (host d) 2) = true := by decide +revert +kernel

/-- Every header in the symbolic instruction sequence decodes on all legal register fields. -/
theorem plan_good (op : Op) (w named : Bool) (d : Fin 10) (s : Fin 11) (i : UInt32) :
    ∀ x ∈ plan op w named d s i, good x.form = true := by
  rw [← List.all_eq_true]
  cases op <;> cases w <;> cases named <;>
    simp [plan, body, shifts, division, arith, signTail, ins] <;>
    repeat' (split <;> simp_all)
  all_goals by_cases h : i.toUInt64 = 16 <;> by_cases k : i.toUInt64 = 32 <;> simp_all
end Certificate
