/-! # Counting occurrences of 64-bit keys

A small histogram for a few hundred distinct keys at most (client ids,
software versions): linear search over two parallel arrays. -/

structure Tally where
  keys : Array UInt64
  counts : Array UInt64

namespace Tally

def create (capacity : Nat) : Tally :=
  ⟨Array.emptyWithCapacity capacity, Array.emptyWithCapacity capacity⟩

/-- Counts one more occurrence of `k`. -/
def add (t : Tally) (k : UInt64) : Tally := Id.run do
  let ⟨keys, counts⟩ := t
  for i in [0:keys.size] do
    if keys[i]! == k then
      return ⟨keys, counts.set! i (counts[i]! + 1)⟩
  return ⟨keys.push k, counts.push 1⟩

/-- Indices of the entries, most frequent first (ties: first seen first). -/
def order (t : Tally) : Array Nat := Id.run do
  let mut left := t.counts
  let mut out : Array Nat := Array.emptyWithCapacity left.size
  for _ in [0:left.size] do
    let mut best := 0
    let mut bestCount : UInt64 := 0
    for j in [0:left.size] do
      if left[j]! > bestCount then
        best := j
        bestCount := left[j]!
    if bestCount == 0 then
      break
    out := out.push best
    left := left.set! best 0
  return out

end Tally
