import Encoding

namespace Certificate
open X86

def execute : List Ins → State → Outcome
  | [], m => .next m
  | i :: rest, m =>
    match exec (clipped i) m with
    | .next m' => execute rest m'
    | other => other

theorem wire_fold (xs : List Ins) (b : ByteArray) :
    wire (xs.foldl emit b) = wire b ++ xs.flatMap raw := by
  induction xs generalizing b with
  | nil => simp
  | cons i xs ih => simp [ih, wire_emit, List.append_assoc]

theorem run_decode (xs : List Ins) (m : State) (fuel : Nat) (enough : xs.length ≤ fuel) (ok : ∀ i ∈ xs, good i.form = true) :
    run fuel (xs.flatMap raw) m = execute xs m := by
  induction xs generalizing m fuel with
  | nil => cases fuel <;> rfl
  | cons i xs ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show fuel ≠ 0 by simp only [List.length_cons] at enough; omega)
    have hn : xs.length ≤ n := Nat.le_of_succ_le_succ enough
    have dec := decode_raw i (ok i (by simp)) (xs.flatMap raw)
    have tailOk := fun j hj => ok j (List.mem_cons_of_mem i hj)
    change run (n+1) (raw i ++ xs.flatMap raw) m = _
    generalize hb : raw i ++ xs.flatMap raw = bytes at dec ⊢
    cases bytes with
    | nil => contradiction
    | cons b bs =>
      simp only [run, dec, execute]
      cases exec (clipped i) m <;> simp_all

theorem enough_bytes (xs : List Ins) (ok : ∀ i ∈ xs, good i.form = true) :
    xs.length ≤ (xs.flatMap raw).length := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons i rest ih =>
    have hi := decode_raw i (ok i (by simp)) []
    have ne : raw i ≠ [] := by
      intro h
      rw [h] at hi
      contradiction
    have hlen := List.length_pos_iff.mpr ne
    have tail := ih (fun j hj => ok j (List.mem_cons_of_mem i hj))
    simp only [List.flatMap_cons, List.length_cons, List.length_append]
    omega
end Certificate
