import Double

/-! `Double`: the IEEE 754 operations done in integers, on numbers drawn at
random, each kind summed into one figure. `tests/double.py` draws the same
numbers and does the same with the processor's doubles; the figures it
prints are the ones expected here. -/

def draw (s : UInt64) : UInt64 :=
  let a := s ^^^ (s <<< 13)
  let b := a ^^^ (a >>> 7)
  b ^^^ (b <<< 17)

/-- A double with a random fraction and an exponent in `[low, low + span)`. -/
def number (r low span : UInt64) : UInt64 := ((low + (r >>> 52) % span) <<< 52) ||| (r &&& 0xFFFFFFFFFFFFF)

def main : IO Unit := do
  let mut s : UInt64 := 0x9E3779B97F4A7C15
  let mut sums : Array UInt64 := Array.replicate 7 0
  for _ in [0:2000] do
    s := draw s
    let x := number s 1003 41
    s := draw s
    let y := number s 1003 41
    let big := if x >= y then x else y
    let small := if x >= y then y else x
    let results := #[Double.mul x y, Double.div x y, Double.add x y, Double.sub big small,
      Double.ofU64 (s >>> (x % 64)), Double.toU64 (number s 1020 70),
      Double.pow (number s 1022 1) (number x 1016 12)]
    for k in [0:7] do
      sums := sums.set! k (sums[k]! * 31 + results[k]!)
  let names := #["mul", "div", "add", "sub", "ofU64", "toU64", "pow"]
  for k in [0:7] do
    IO.println s!"{names[k]!}: {sums[k]!}"
  -- the rate of epoch 1099: 0.08 × (1 − 0.15)^5.022694543573436
  IO.println s!"rate: {Double.mul 0x3FB47AE147AE147B (Double.pow (Double.sub 0x3FF0000000000000 0x3FC3333333333333) 0x4014173D3D09C83F)}"
