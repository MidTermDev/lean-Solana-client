import Extraction
import Headers
import Execution

namespace Certificate
open X86

private theorem wire_set (b : ByteArray) (n : Nat) (x : UInt8) :
    wire (b.set! n x) = (wire b).set n x := by
  cases b; simp [wire, ByteArray.set!]

/-- The upstream four-byte patch leaves the entire surrounding byte stream intact. -/
private theorem patch_field (b : ByteArray) (pre post : List UInt8) (v : UInt32)
    (shape : wire b = pre ++ 0::0::0::0::post) :
    wire (Fast.put32 b pre.length v.toUInt64) =
      pre ++ immBytes (ins .jz v.toUInt64) ++ post := by
  have top : (v.toUInt64 >>> 24).toUInt8 = (v.toUInt64 >>> 16 >>> 8).toUInt8 := by word_decide
  simp [Fast.put32, List.range', Id.run, immBytes, ins, Form.size,
    top, List.append_assoc]
  change wire ((((b.set! _ _).set! _ _).set! _ _).set! _ _) = _
  simp [wire_set, shape, List.set_append_right]

def divOp (rem : Bool) : Op := if rem then .umod else .udiv

/-- The first rel32 byte, measured from the beginning of the instruction fragment. -/
def guardPrefix (w : Bool) (s : Fin 11) :=
  raw (ins (.test w (source s) (source s))) ++ [0x0f, 0x84]

private theorem not_frame (s : Fin 11) (h : s.val ≠ 10) : s.val.toUInt64 ≠ 10 := by
  revert h; revert s; decide +kernel

theorem register_div_plan (rem w : Bool) (d : Fin 10) (s : Fin 11) (i : UInt32) (h : s.val ≠ 10) :
    plan (divOp rem) w true d s i = division w true rem (host d) (source s) (Sbpf.sext32 i.toUInt64) := by
  cases rem <;> simp [plan, divOp, body, not_frame s h]

theorem div_sites (rem w : Bool) (d : Fin 10) (s : Fin 11) (i : UInt32) (h : s.val ≠ 10) :
    (code (divOp rem) w true d s i).2 = #[(guardPrefix w s).length.toUInt64,0,0] := by
  have frame := not_frame s h
  let test := Jit.rr .empty (width w) 0x85 (source s) (source s)
  have extractSites : (code (divOp rem) w true d s i).2 =
      Jit.fault #[] ((Jit.jumpIf test 4).size - 4) 0 0 := by
    cases rem <;> cases w <;> unfold code <;> delta Jit.aluCode <;>
      simp [divOp, cls, Op.nibble, source, frame, Id.run, pure, test, width]
  rw [extractSites]
  have prelen : (guardPrefix w s).length = test.size + 2 := by
    change ((wire test ++ []) ++ [15,132]).length = test.size + 2
    rw [List.append_nil, List.length_append]
    rfl
  rw [prelen]
  simp [Jit.jumpIf, Fast.push32, Fast.push16, ByteArray.size_push, Jit.fault]

def relocated (rem w : Bool) (d : Fin 10) (s : Fin 11) (i : UInt32) (rel : UInt32) :=
  Fast.put32 (code (divOp rem) w true d s i).1 (guardPrefix w s).length rel.toUInt64

theorem relocated_wire (rem w : Bool) (d : Fin 10) (s : Fin 11) (i rel : UInt32) (h : s.val ≠ 10) :
    wire (relocated rem w d s i rel) =
      (division w true rem (host d) (source s) (Sbpf.sext32 i.toUInt64) rel).flatMap raw := by
  let tail : List Ins := [ins (.rr w .mov 0 (host d)), ins (.rr false .xor 2 2),
      ins (.divR w (source s)), ins (.rr w .mov (host d) (if rem then 2 else 0))]
  have shape : wire (code (divOp rem) w true d s i).1 =
      guardPrefix w s ++ 0::0::0::0::tail.flatMap raw := by
    unfold code
    rw [extraction, wire_fold, wire_empty, List.nil_append, register_div_plan rem w d s i h]
    simp [division, guardPrefix, tail, List.append_assoc, raw, immBytes, ins, Form.size,
      headBytes, wire]
  unfold relocated
  rw [patch_field _ _ _ _ shape]
  simp [division, guardPrefix, tail, List.append_assoc, raw, immBytes, ins, Form.size,
    headBytes, wire]

theorem relocated_good (rem w : Bool) (d : Fin 10) (s : Fin 11) (i rel : UInt32) (h : s.val ≠ 10) :
    ∀ x ∈ division w true rem (host d) (source s) (Sbpf.sext32 i.toUInt64) rel, good x.form = true := by
  have orig := plan_good (divOp rem) w true d s i
  rw [register_div_plan rem w d s i h] at orig
  simpa [division, ins] using orig
end Certificate
