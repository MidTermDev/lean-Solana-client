import Plan
import Sign

namespace Certificate
open X86
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
attribute [local irreducible] Jit.aluCode plan Jit.rr Jit.rm Fast.push32

private theorem mov_range (i : UInt32) : i.toUInt64 < 0x100000000 := i.toNat_lt
private theorem mov_high (i : UInt32) : ¬ Sbpf.sext32 i.toUInt64 < 0x100000000 →
    Sbpf.sext32 i.toUInt64 >= 0xffffffff80000000  := by
  simp (config := {ground := true}) only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, sext_nat, UInt32.toNat_toUInt64]
  split <;> omega

/-- Equality at the actual ByteArray interface, for arbitrary incoming buffer and fixup list. -/
private def ByteEq (op : Op) (w named : Bool) (d : Fin 10) (s : Fin 11) (i : UInt32) : Prop :=
  ∀ (b : ByteArray) (sites : Array UInt64) (pc : Nat) (uncounted : UInt64),
    (Jit.aluCode b sites pc uncounted (cls w) op.nibble d.val.toUInt64 s.val.toUInt64 named i.toUInt64).1 =
      (plan op w named d s i).foldl emit b

theorem extraction (op : Op) (w named : Bool) (d : Fin 10) (s : Fin 11) (i : UInt32) :
    ByteEq op w named d s i := by
  cases op <;> cases w <;> cases named <;> intro b sites pc uncounted
  all_goals by_cases frame : s.val.toUInt64 = 10
  all_goals delta Jit.aluCode plan
  all_goals
    dsimp only [body, Op.nibble, cls, Id.run, bind, pure, signTail,
      arith, shifts, division, host, source, ins, emit, headBytes, width, ext, Form.size, Jit.ri,
      List.foldl, List.append]
    simp [frame, Jit.ri, List.foldl, body, ins, emit, headBytes, signTail, width, ext, Form.size,
      Id.run, pure, bind, arith, shifts, division, host, source, Jit.loadConstant, mov_range,
      Jit.jumpIf, Jit.slot, Jit.cTemp, Jit.rbp, Jit.rax, Jit.rdx, which, shiftExt] <;> try rfl
  all_goals repeat' (split <;> simp_all [mov_high, emit, headBytes, ins, Form.size, width, ext,
    shiftExt, List.foldl, Jit.rr, Jit.rax, Jit.rdx] <;> try rfl)
  all_goals rename_i lo hi; exact False.elim ((UInt64.not_lt.mpr hi) lo)
end Certificate
