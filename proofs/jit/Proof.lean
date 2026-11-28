import Relocation
import Step
import Body

namespace Certificate
open X86

/-- The virtual frame pointer is stored at cpu[10], separately from r14's machine address. -/
def guest (m : State) (s : Fin 11) : UInt64 :=
  if s.val.toUInt64 == 10 then m.frame else m.regs (reg (Jit.hostOf s.val.toUInt64))

/-- Install any eleven guest values, preserving the caller's free choice of scratch
values, the temporary slot, and flags. Reads of r10 use the frame slot. -/
def install (rs : Fin 11 → UInt64) (m : State) : State :=
  {m with frame := rs 10, regs := fun r =>
    match (List.finRange 10).find? (fun d => reg (host d) == r) with
    | some d => rs d.castSucc
    | none => m.regs r}

theorem install_reads (rs : Fin 11 → UInt64) (m : State) (g : Fin 10) :
    (install rs m).regs (reg (host g)) = rs g.castSucc ∧ (install rs m).frame = rs 10 := by
  have map : ∀ d : Fin 10, (List.finRange 10).find? (fun j => reg (host j) == reg (host d)) = some d :=
    by decide +kernel
  simp [install, map]

/-- Decode until the end or the first taken edge. Each instruction consumes at least one byte. -/
def evaluate (b : ByteArray) (m : State) := run (wire b).length (wire b) m

theorem evaluate_code (op : Op) (w named : Bool) (d : Fin 10) (s : Fin 11) (i : UInt32) (m : State) :
    evaluate (code op w named d s i).1 m = execute (plan op w named d s i) m := by
  unfold evaluate code
  rw [extraction op w named d s i .empty #[] 0 0, wire_fold, wire_empty, List.nil_append]
  have headers := plan_good op w named d s i
  exact run_decode _ _ _ (enough_bytes _ headers) headers

/-- One admitted instruction in either JIT-enabled version. For every observed r0–r9,
check its value and r10's value together. A zero divisor must take the recorded
rel32 edge before changing any guest register. -/
theorem alu_correct (op : Op) (w named : Bool) (d g : Fin 10) (s : Fin 11) (i : UInt32)
    (m : State) (ok : admitted op w named s i = true) :
    observation (host g) (evaluate (code op w named d s i).1 m) =
      expected (g == d) (m.regs (reg (host g))) m.frame
        (reference op w named i (m.regs (reg (host d))) (guest m s)) := by
  rw [evaluate_code]
  by_cases frame : s.val.toUInt64 = 10
  · cases named
    · simpa [plan, frame, guest, reference] using body_correct op w false d g s i m ok
    · have law := body_correct op w true d g s i (m.write 0 m.frame) ok
      simpa [plan, frame, guest, execute, clipped, ins, exec, Form.size, source,
        State.write, show reg 0 = 0 from rfl, (host_scratch d).1, (host_scratch g).1] using law
  · simpa [plan, guest, source, frame] using body_correct op w named d g s i m ok

/-- A guarded DIV/MOD with any 32-bit relocation installed at the recorded
site. Successful arithmetic and the taken displacement are both observed. -/
theorem linked_division_correct (rem w : Bool) (d g : Fin 10) (s : Fin 11)
    (i rel : UInt32) (m : State) (h : s.val ≠ 10) :
    observation (host g) (evaluate (relocated rem w d s i rel) m) =
      expected (g == d) (m.regs (reg (host g))) m.frame
        (reference (divOp rem) w true i (m.regs (reg (host d))) (guest m s)) rel := by
  have hd := relocated_good rem w d s i rel h
  unfold evaluate
  rw [relocated_wire rem w d s i rel h, run_decode _ _ _ (enough_bytes _ hd) hd]
  have hs : ∀ z : Fin 11, z.val ≠ 10 → reg (source z) ≠ 0 ∧ reg (source z) ≠ 2 := by decide +kernel
  have hf : ∀ z : Fin 11, z.val ≠ 10 → z.val.toUInt64 ≠ 10 := by decide +kernel
  simpa [host_eq, guest, source, hf s h, divOp] using
    division_correct rem w true (host d) (source s) (host g) i m
      (host_scratch g).1 (host_scratch g).2 (fun _ => (hs s h).1) (fun _ => (hs s h).2)
      (by simp) rel

/-- Entry point expressed at the pinned compile branch: literal opcode and fields,
the same acceptance guard, and the interpreter's cases on the literal opcode.
The separate frame/tidiness checks give exactly the register bounds in the type. -/
theorem opcode_correct (b : Fin 256) (d g : Fin 10) (s : Fin 11) (i : UInt32) (m : State)
    (acceptedByJit : Jit.aluKind b.val.toUInt8.toUInt64 s.val.toUInt64 i.toUInt64 = 0) :
    let opc := b.val.toUInt8.toUInt64
    let bytes := (Jit.aluCode .empty #[] 0 0 (opc &&& 7) (opc &&& 0xf0)
      d.val.toUInt64 s.val.toUInt64 (opc &&& 8 != 0) i.toUInt64).1
    observation (host g) (evaluate bytes m) =
      expected (g == d) (m.regs (reg (host g))) m.frame
        (interpreter opc i (m.regs (reg (host d))) (guest m s)) := by
  obtain ⟨f, eqByte, ok⟩ := admitted_form b s i acceptedByJit
  dsimp only
  rw [← eqByte, (byte_fields f).1, (byte_fields f).2.1, (byte_fields f).2.2,
    interpreter_reference f s i _ _ ok]
  exact alu_correct f.op f.wide f.named d g s i m ok

theorem guest_install (rs : Fin 11 → UInt64) (m : State) (s : Fin 11) :
    guest (install rs m) s = rs s := by
  refine Fin.lastCases ?_ (fun j => ?_) s
  · rfl
  · have small : ∀ j : Fin 10, j.val.toUInt64 ≠ 10 := by decide +kernel
    simpa [guest, small j, host] using (install_reads rs m j).1

/-- Direct comparison on the caller's eleven sBPF registers. The host state supplies
only unmapped register values, the temporary slot and the initial flag. -/
theorem installed_opcode_correct (b : Fin 256) (d g : Fin 10) (s : Fin 11) (i : UInt32)
    (rs : Fin 11 → UInt64) (m : State)
    (acceptedByJit : Jit.aluKind b.val.toUInt8.toUInt64 s.val.toUInt64 i.toUInt64 = 0) :
    let opc := b.val.toUInt8.toUInt64
    let bytes := (Jit.aluCode .empty #[] 0 0 (opc &&& 7) (opc &&& 0xf0)
      d.val.toUInt64 s.val.toUInt64 (opc &&& 8 != 0) i.toUInt64).1
    observation (host g) (evaluate bytes (install rs m)) =
      expected (g == d) (rs g.castSucc) (rs 10) (interpreter opc i (rs d.castSucc) (rs s)) := by
  simpa only [guest_install, (install_reads rs m g).1, (install_reads rs m d).1,
    (install_reads rs m d).2] using opcode_correct b d g s i (install rs m) acceptedByJit
/-- The machine and interpreter agree on normal/taken control flow, the observed register
and the frame slot. Registers past r10 may hold arbitrary interpreter bookkeeping. -/
theorem pinned_step_correct (b : Fin 256) (d g : Fin 10) (s : Fin 11) (i : UInt32)
    (regs : Array UInt64) (size : 11 ≤ regs.size) (m : State)
    (acceptedByJit : Jit.aluKind b.val.toUInt8.toUInt64 s.val.toUInt64 i.toUInt64 = 0) :
    let opc := b.val.toUInt8.toUInt64
    let bytes := (Jit.aluCode .empty #[] 0 0 (opc &&& 7) (opc &&& 0xf0)
      d.val.toUInt64 s.val.toUInt64 (opc &&& 8 != 0) i.toUInt64).1
    let step := Sbpf.aluStep regs opc d.val s.val i.toUInt64 false
    observation (host g) (evaluate bytes (install (fun r => regs[r.val]!) m)) =
      stepObservation step g := by
  dsimp only
  rw [installed_opcode_correct b d g s i (fun r => regs[r.val]!) m acceptedByJit]
  obtain ⟨f, eqByte, ok⟩ := admitted_form b s i acceptedByJit
  rw [← eqByte, step_admitted regs f d.val s i ok]
  change expected (g == d) regs[g.val]! regs[10]!
    (interpreter _ i regs[d.val]! regs[s.val]!) = _
  cases interpreter (byteOf f) i regs[d.val]! regs[s.val]! with
  | none => rfl
  | some x =>
    have frame := Array.getElem!_set!_ne regs d.val 10 x (by omega)
    by_cases eq : g = d
    · subst g
      simp only [expected, stepObservation, Sbpf.finished, beq_self_eq_true, ite_true, frame,
        Array.getElem!_set!_self regs d.val x (by omega)]
    · have hg : d.val ≠ g.val := fun h => eq (Fin.ext h.symm)
      simp only [expected, stepObservation, Sbpf.finished, beq_self_eq_true, ite_true,
        beq_eq_false_iff_ne.mpr eq, Bool.false_eq_true, ite_false, frame,
        Array.getElem!_set!_ne regs d.val g.val x hg]

end Certificate
