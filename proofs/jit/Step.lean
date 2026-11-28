import Interpreter
import Coverage

namespace Certificate

/-- The two statuses distinguish an unsupported encoding from a legal zero divide.
Every successful write is the upstream array update at the decoded destination. -/
theorem step_result (regs : Array UInt64) (opc : UInt64) (dst src : Nat) (i : UInt32) :
    Sbpf.aluStep regs opc dst src i.toUInt64 false =
      match interpreter opc i regs[dst]! regs[src]! with
      | some x => (Sbpf.finished, regs.set! dst x)
      | none => (if opc == 0xdc || opc == 0xd4 || (opc &&& 0xf0 > 0xc0)
                 then Sbpf.unsupportedInstruction else Sbpf.divideByZero, regs) := by
  by_cases endian : opc = 0xdc ∨ opc = 0xd4
  · by_cases a : i.toUInt64 = 16 <;> by_cases b : i.toUInt64 = 32 <;> by_cases c : i.toUInt64 = 64 <;>
      simp [Sbpf.aluStep, interpreter, endian, a, b, c, Id.run, pure, bind]
  · by_cases high : opc &&& 0xf0 > 0xc0
    · simp [Sbpf.aluStep, interpreter, endian, high, Id.run, pure, bind]
    · let operand := if opc &&& 8 = 0 then Sbpf.sext32 i.toUInt64 else regs[src]!
      by_cases zero : (opc &&& 0xf0 = 0x30 ∨ opc &&& 0xf0 = 0x90) ∧
          (if opc &&& 7 = 7 then operand = 0 else operand &&& 0xffffffff = 0)
      all_goals simp only [operand] at zero
      all_goals simp [Sbpf.aluStep, interpreter, endian, high, zero, Id.run, pure, bind]

/-- On the accepted domain the only early exit of the interpreter arm is divideByZero. -/
theorem step_admitted (regs : Array UInt64) (f : OperandForm) (dst : Nat) (s : Fin 11) (i : UInt32)
    (ok : admitted f.op f.wide f.named s i = true) :
    Sbpf.aluStep regs (byteOf f) dst s.val i.toUInt64 false =
      match interpreter (byteOf f) i regs[dst]! regs[s.val]! with
      | some x => (Sbpf.finished, regs.set! dst x)
      | none => (Sbpf.divideByZero, regs) := by
  rw [step_result]
  cases v : interpreter (byteOf f) i regs[dst]! regs[s.val]! with
  | some => rfl
  | none =>
    rcases f with ⟨op,w,n⟩
    cases op <;> cases w <;> cases n <;> simp [byteOf, cls, Op.nibble, admitted] at *
    all_goals rcases ok with (h | h) | h <;> subst i <;> simp [interpreter] at v
/-- Only a real divideByZero status can match a taken machine edge. -/
def stepObservation (step : UInt64 × Array UInt64) (g : Fin 10) :
    Option (Option UInt32 × UInt64 × UInt64) :=
  if step.1 == Sbpf.finished then some (none, step.2[g.val]!, step.2[10]!)
  else if step.1 == Sbpf.divideByZero then some (some 0, step.2[g.val]!, step.2[10]!)
  else none

end Certificate
