import Crypto.ChaCha
import Solana.Snapshot

/-!
# The leader schedule

Which validator produces which slot is not announced; every node computes
it. For each epoch, the validators with stake are put in order (most stake
first, ties by vote address), and a generator seeded with the epoch's
number picks one of them, with probability proportional to stake, for each
run of four slots.

The stakes that count for an epoch are fixed one epoch earlier, and a
snapshot's manifest carries them for the epochs around it.
-/

namespace LeaderSchedule

/-- Slots a leader gets in a row. -/
def run : Nat := 4

/-- The high and low halves of a 64 × 64-bit product. -/
def wide (x y : UInt64) : UInt64 × UInt64 :=
  let x0 := x &&& 0xFFFFFFFF
  let x1 := x >>> 32
  let y0 := y &&& 0xFFFFFFFF
  let y1 := y >>> 32
  let low := x0 * y0
  let mid1 := x1 * y0 + (low >>> 32)
  let mid2 := x0 * y1 + (mid1 &&& 0xFFFFFFFF)
  (x1 * y1 + (mid1 >>> 32) + (mid2 >>> 32), (mid2 <<< 32) ||| (low &&& 0xFFFFFFFF))

/-- A number below `range`, each equally likely: the top half of a random
number times `range`, drawn again in the rare case that would favour some
values. -/
def below (r0 : ChaCha.Rng) (range : UInt64) : UInt64 × ChaCha.Rng := Id.run do
  let max : UInt64 := 0xFFFFFFFFFFFFFFFF
  let zone := max - (max - range + 1) % range
  let mut r := r0
  for _ in [0:1000] do
    let (x, next) := r.next64
    r := next
    let (high, low) := wide x range
    if low <= zone then
      return (high, r)
  return (0, r)

/-- True when `a` sorts before `b`: more stake first, and among equals the greater vote address first. -/
def before (a b : Snapshot.Voter) : Bool := Id.run do
  if a.stake != b.stake then
    return a.stake > b.stake
  for i in [0:32] do
    if a.vote[i]! != b.vote[i]! then
      return a.vote[i]! > b.vote[i]!
  return false

/-- The voters in schedule order, each once. -/
def sorted (voters : Array Snapshot.Voter) : Array Snapshot.Voter := Id.run do
  -- merge sort, bottom up
  let mut a := voters
  let mut width := 1
  while width < a.size do
    let mut merged : Array Snapshot.Voter := Array.emptyWithCapacity a.size
    let mut start := 0
    while start < a.size do
      let mid := if start + width < a.size then start + width else a.size
      let stop := if start + 2 * width < a.size then start + 2 * width else a.size
      let mut i := start
      let mut j := mid
      while i < mid || j < stop do
        if j >= stop || (i < mid && !(before a[j]! a[i]!)) then
          merged := merged.push a[i]!
          i := i + 1
        else
          merged := merged.push a[j]!
          j := j + 1
      start := stop
    a := merged
    width := width * 2
  -- the same vote address with the same stake counts once
  let mut out : Array Snapshot.Voter := Array.emptyWithCapacity a.size
  for v in a do
    if out.size == 0 || out[out.size - 1]!.stake != v.stake || out[out.size - 1]!.vote != v.vote then
      out := out.push v
  return out

/-- The schedule of an epoch of `slots` slots: for each run of four slots, the index of its leader in `sorted voters`. -/
def draw (voters : Array Snapshot.Voter) (epoch : UInt64) (slots repeat_ : Nat) : Array Nat := Id.run do
  let order := sorted voters
  if order.size == 0 then
    return Array.emptyWithCapacity 0
  -- running totals of stake; a draw below the total picks the first voter whose running total exceeds it
  let mut totals : Array UInt64 := Array.emptyWithCapacity order.size
  let mut total : UInt64 := 0
  for v in order do
    total := total + v.stake
    totals := totals.push total
  if total == 0 then
    return Array.emptyWithCapacity 0
  let mut seed := ByteArray.emptyWithCapacity 32
  for i in [0:32] do
    seed := seed.push (if i < 8 then (epoch >>> (8 * i).toUInt64).toUInt8 else 0)
  let mut rng := ChaCha.Rng.seeded seed
  let mut out : Array Nat := Array.emptyWithCapacity (slots / repeat_)
  for _ in [0:slots / repeat_] do
    let (chosen, next) := below rng total
    rng := next
    -- the first of the running totals (all but the last) that is greater than the number drawn
    let mut low := 0
    let mut high := order.size - 1
    while low < high do
      let mid := (low + high) / 2
      if totals[mid]! <= chosen then
        low := mid + 1
      else
        high := mid
    out := out.push low
  return out

-- A table of schedules, for handing to other processes: for each epoch,
--   epoch, first slot, number of slots, number of leaders (8 bytes each),
--   the leaders' identities (32 bytes each, in schedule order),
--   and two bytes for each run of four slots: which of them leads it.

/-- The schedules of every epoch whose stakes the manifest records. `what` chooses what is kept for each
leader: 0 its identity, 1 its vote account, 2 the address that collects its block fees. -/
def table (m : Snapshot.Manifest) (what : Nat) : ByteArray := Id.run do
  let mut t := ByteArray.emptyWithCapacity 1200000
  for e in m.epochStakes do
    let order := sorted e.voters
    if m.slotsPerEpoch != 0 && e.epoch >= m.firstNormalEpoch && order.size != 0 && order.size < 65536 then
      let picks := draw e.voters e.epoch m.slotsPerEpoch.toNat run
      if picks.size != 0 then
        t := Wire.putU64 t e.epoch
        t := Wire.putU64 t (m.firstNormalSlot + (e.epoch - m.firstNormalEpoch) * m.slotsPerEpoch)
        t := Wire.putU64 t m.slotsPerEpoch
        t := Wire.putU64 t order.size.toUInt64
        for v in order do
          t := t ++ (if what == 1 then v.vote else if what == 2 && v.collector.size == 32 then v.collector else v.node)
        for p in picks do
          t := Wire.putU16 t p.toUInt64
  return t

/-- The identity that leads `slot` according to the table, or nothing if the table does not cover the slot. -/
def leaderAt (t : ByteArray) (slot : UInt64) : ByteArray := Id.run do
  let mut o := 0
  while o + 32 <= t.size do
    let first := Wire.u64 t (o + 8)
    let slots := Wire.u64 t (o + 16)
    let leaders := (Wire.u64 t (o + 24)).toNat
    let picks := o + 32 + 32 * leaders
    if slot >= first && slot < first + slots then
      let which := (Wire.u16 t (picks + 2 * ((slot - first).toNat / run))).toNat
      return t.extract (o + 32 + 32 * which) (o + 64 + 32 * which)
    o := picks + 2 * (slots.toNat / run)
  return ByteArray.empty

/-- The first slot and the slot after the last that the table covers (0 and 0 if it is empty). -/
def covers (t : ByteArray) : UInt64 × UInt64 := Id.run do
  let mut o := 0
  let mut low : UInt64 := 0
  let mut high : UInt64 := 0
  while o + 32 <= t.size do
    let first := Wire.u64 t (o + 8)
    let slots := Wire.u64 t (o + 16)
    if low == 0 || first < low then
      low := first
    if first + slots > high then
      high := first + slots
    o := o + 32 + 32 * (Wire.u64 t (o + 24)).toNat + 2 * (slots.toNat / run)
  return (low, high)

end LeaderSchedule
