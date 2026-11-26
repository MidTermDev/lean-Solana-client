import Solana.Table

/-! Guards the property the client's performance rests on: updating a large
immutable structure that has a single owner must happen in place. If the
ownership analysis ever regressed into copying, the 200,000 inserts below
would copy a 4 MB array each (about 800 GB in total) instead of finishing
in milliseconds. Native only: the official interpreter takes minutes here. -/

def main : IO Unit := do
  let mut s := Set64.create (1 <<< 19)
  let t0 ← IO.monoMsNow
  for i in [0:200000] do
    s := s.insert (i.toUInt64 * 0x9E3779B97F4A7C15 + 1)
  let mut hits := 0
  for i in [0:400000] do
    if s.contains (i.toUInt64 * 0x9E3779B97F4A7C15 + 1) then
      hits := hits + 1
  let t1 ← IO.monoMsNow
  IO.println s!"count {s.count}, hits {hits}"
  IO.println (if t1 - t0 < 3000 then "in place" else "TOO SLOW: the table is being copied")
