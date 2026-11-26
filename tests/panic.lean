/-! Out-of-bounds access must stop the program, not corrupt memory. -/

def main : IO Unit := do
  let xs : Array Nat := #[1, 2, 3]
  IO.println "before"
  let i := xs.size + 2
  IO.println s!"{xs[i]!}"
  IO.println "unreachable"
