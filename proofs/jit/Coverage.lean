-- Interpreter dispatch adapted from lib/Solana/Sbpf.lean at b9fa957 (MIT, see LICENSE).
import Semantics

namespace Certificate

structure OperandForm where
  op : Op
  wide : Bool
  named : Bool
  deriving DecidableEq

/-- Interpret the literal opcode byte. Bits 0–2 are the class, bit 3 selects the
operand, and bits 4–7 select the operation. -/
def opcodeForm (byte : UInt8) : Option OperandForm := do
  let cls := byte &&& 7
  if cls != 4 && cls != 7 then none else
    let ops : Array Op := #[.add,.sub,.mul,.udiv,.bor,.band,.shl,.shr,.neg,.umod,.xor,.mov,.sar,.endian]
    let op ← ops[(byte >>> 4).toNat]?
    return ⟨op, cls == 7, byte &&& 8 != 0⟩

def byteOf (f : OperandForm) : UInt64 := f.op.nibble ||| (if f.named then 8 else 0) ||| cls f.wide

theorem recovered : ∀ b : Fin 256, (opcodeForm b.val.toUInt8).all (fun f =>
    byteOf f == b.val.toUInt8.toUInt64) = true := by decide +kernel

private def rep (i : UInt32) : Fin 5 :=
  if i == 0 then 0 else if i == 16 then 1 else if i == 32 then 2 else if i == 64 then 3 else 4
private def value (r : Fin 5) : UInt32 := #[0,16,32,64,1][r.val]!

/-- All immediates have one of five behaviours in classOf's ALU guard. -/
private theorem repr_checks (i : UInt32) :
    (value (rep i) = 0 ↔ i = 0) ∧ (value (rep i) = 16 ↔ i = 16) ∧
    (value (rep i) = 32 ↔ i = 32) ∧ (value (rep i) = 64 ↔ i = 64) := by
  by_cases a : i = 0 <;> by_cases b : i = 16 <;> by_cases c : i = 32 <;> by_cases d : i = 64 <;>
    simp [rep, a,b,c,d, value] <;> decide

def accepted (b : UInt8) (s : Fin 11) (i : UInt32) : Bool :=
  (opcodeForm b).any (fun f => admitted f.op f.wide f.named s i)

private theorem finite_gate : ∀ (b : Fin 256) (s : Fin 11) (r : Fin 5),
    accepted b.val.toUInt8 s (value r) =
      (Jit.aluKind b.val.toUInt8.toUInt64 s.val.toUInt64 (value r).toUInt64 == 0) := by
  decide +kernel

private theorem gate_congr (b : UInt8) (s : Fin 11) (i : UInt32) :
    (Jit.aluKind b.toUInt64 s.val.toUInt64 (value (rep i)).toUInt64 == 0) =
      (Jit.aluKind b.toUInt64 s.val.toUInt64 i.toUInt64 == 0) := by
  obtain ⟨h0,h16,h32,h64⟩ := repr_checks i
  have lift (x : UInt32) (n : UInt32) : (x.toUInt64 == n.toUInt64) = (x == n) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, ← UInt64.toNat_inj, UInt32.toNat_toUInt64, UInt32.toNat_inj]
  have same (n : UInt32) (h : value (rep i) = n ↔ i = n) :
      ((value (rep i)).toUInt64 == n.toUInt64) = (i.toUInt64 == n.toUInt64) := by
    rw [lift, lift, Bool.eq_iff_iff]
    simpa using h
  have e0 : ((value (rep i)).toUInt64 == 0) = (i.toUInt64 == 0) := same 0 h0
  have e16 : ((value (rep i)).toUInt64 == 16) = (i.toUInt64 == 16) := same 16 h16
  have e32 : ((value (rep i)).toUInt64 == 32) = (i.toUInt64 == 32) := same 32 h32
  have e64 : ((value (rep i)).toUInt64 == 64) = (i.toUInt64 == 64) := same 64 h64
  simp only [Jit.aluKind, e0,e16,e32,e64]

theorem exact_domain (b : Fin 256) (s : Fin 11) (i : UInt32) :
    accepted b.val.toUInt8 s i =
    (Jit.aluKind b.val.toUInt8.toUInt64 s.val.toUInt64 i.toUInt64 == 0) := by
  rw [← gate_congr, ← finite_gate]
  unfold accepted
  cases opcodeForm b.val.toUInt8 with
  | none => rfl
  | some f =>
    obtain ⟨h0,h16,h32,h64⟩ := repr_checks i
    cases f with | mk op w n =>
      cases op <;> cases n <;> apply Bool.eq_iff_iff.mpr <;> simp [admitted, h0, h16, h32, h64]

/-- Literal post-decode arithmetic cases in Sbpf.lean, with v2=false. Errors
are represented by none. The domain theorem excludes invalid endian widths. -/
def interpreter (opc : UInt64) (i : UInt32) (a src : UInt64) : Option UInt64 :=
  let op := opc &&& 0xf0
  let cls := opc &&& 7
  let b := if opc &&& 8 != 0 then src else Sbpf.sext32 i.toUInt64
  if opc == 0xdc || opc == 0xd4 then
    let bytes := if i.toUInt64 == 16 then 2 else if i.toUInt64 == 32 then 4 else if i.toUInt64 == 64 then 8 else 0
    if bytes == 0 then none else
      let low := if bytes == 8 then a else a &&& (((1 : UInt64) <<< (8 * bytes).toUInt64) - 1)
      some (if opc == 0xdc then Sbpf.bswap low bytes else low)
  else if op > 0xc0 then none
  else if (op == 0x30 || op == 0x90) && (if cls == 7 then b == 0 else b &&& 0xffffffff == 0)
    then none
  else some (if cls == 7 then Sbpf.alu64 op a b else Sbpf.alu32 op a b)

theorem interpreter_reference (f : OperandForm) (s : Fin 11) (i : UInt32) (a b : UInt64)
    (ok : admitted f.op f.wide f.named s i = true) :
    interpreter (byteOf f) i a b = reference f.op f.wide f.named i a b := by
  rcases f with ⟨op,w,n⟩
  cases op <;> cases w <;> cases n <;>
    simp [admitted, interpreter, byteOf, reference, Op.nibble, cls] at *
  all_goals rcases ok with (h|h)|h <;> subst i <;> rfl

theorem byte_fields (f : OperandForm) : ((byteOf f) &&& 7) = cls f.wide ∧
    ((byteOf f) &&& 0xf0) = f.op.nibble ∧ ((byteOf f &&& 8) != 0) = f.named := by
  rcases f with ⟨op,w,n⟩
  cases op <;> cases w <;> cases n <;> decide
theorem admitted_form (b : Fin 256) (s : Fin 11) (i : UInt32)
    (h : Jit.aluKind b.val.toUInt8.toUInt64 s.val.toUInt64 i.toUInt64 = 0) :
    ∃ f, byteOf f = b.val.toUInt8.toUInt64 ∧ admitted f.op f.wide f.named s i = true := by
  have ok : accepted b.val.toUInt8 s i = true := by rw [exact_domain, h]; rfl
  have back := recovered b
  unfold accepted at ok
  cases e : opcodeForm b.val.toUInt8 with
  | none => rw [e] at ok; contradiction
  | some f =>
    rw [e] at back ok
    exact ⟨f, by simpa only [Option.all_some, beq_iff_eq] using back, ok⟩
end Certificate
