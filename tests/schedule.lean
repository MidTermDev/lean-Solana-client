import Solana.LeaderSchedule
import Encoding.Base58
import Crypto.Sha256

/-! The leader schedule, against Agave's own test vectors.

Every expected value below is copied from Agave's tests (v4.4.1,
`random/src/range.rs`, `random/src/weighted.rs`, `leader-schedule/src/lib.rs`):
the numbers a ChaCha20 generator must give, the picks of a weighted draw, and
whole schedules, the long ones as the hash of the vote addresses in order.
The last of them have 65,536 validators with equal stake, where only the
tie-break decides the order. -/

def seed16 : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 32
  for _ in [0:32] do
    b := b.push 16
  return b

/-- A validator whose vote address is `n` in its first two bytes. -/
def voterOf (n : Nat) (stake : UInt64) : Snapshot.Voter := Id.run do
  let mut key := ByteArray.emptyWithCapacity 32
  key := key.push n.toUInt8
  key := key.push (n >>> 8).toUInt8
  for _ in [0:30] do
    key := key.push 0
  return ⟨key, key, stake, ByteArray.empty, ByteArray.empty, 0⟩

def power (i pow : Nat) : UInt64 :=
  (if pow == 0 then 1 else if pow == 1 then i else if pow == 2 then i * i else i * i * i).toUInt64

/-- The schedule for these stakes, as positions in the list given (as Agave's test prints it). -/
def order (epoch : UInt64) (stakes : Array UInt64) (slots repeat_ : Nat) : String := Id.run do
  let mut voters : Array Snapshot.Voter := Array.emptyWithCapacity stakes.size
  for i in [0:stakes.size] do
    voters := voters.push (voterOf i stakes[i]!)
  let sorted := LeaderSchedule.sorted voters
  let mut out := ""
  for p in LeaderSchedule.draw voters epoch slots repeat_ do
    out := out ++ s!"{sorted[p]!.vote[0]!} "
  return out

/-- A schedule of `slots` slots over 65,536 validators with stake `i ^ pow`, hashed as Agave's test hashes it. -/
def hashed (epoch : UInt64) (slots pow : Nat) : String := Id.run do
  let mut voters : Array Snapshot.Voter := Array.emptyWithCapacity 65536
  for i in [0:65536] do
    voters := voters.push (voterOf i (power i pow))
  let sorted := LeaderSchedule.sorted voters
  let mut all := ByteArray.emptyWithCapacity (32 * slots)
  for p in LeaderSchedule.draw voters epoch slots 1 do
    all := all ++ sorted[p]!.vote
  return Base58.encode (Sha256.hash all)

def main : IO Unit := do
  -- the generator and the uniform draw
  let mut rng := ChaCha.Rng.seeded seed16
  let mut line := ""
  for _ in [0:10] do
    let (v, next) := LeaderSchedule.below rng 294533
    rng := next
    line := line ++ s!"{v} "
  IO.println s!"numbers below 294533: {line}"
  IO.println s!"            expected: 280405 7507 84194 272634 52124 190984 8676 230277 223574 126007 "
  let (high, low) := LeaderSchedule.wide 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF
  IO.println s!"the largest product: {high} {low}"

  -- weighted picks: weights 0, 1, 2, ... (to a power), ten draws
  let mut picks := ""
  let mut voters : Array Snapshot.Voter := Array.emptyWithCapacity 1000
  for i in [0:1000] do
    voters := voters.push (voterOf i (power i 1))
  -- (drawn in the order given, as Agave's weighted index is: sorting is the schedule's business)
  let mut totals : Array UInt64 := Array.emptyWithCapacity 1000
  let mut total : UInt64 := 0
  for v in voters do
    total := total + v.stake
    totals := totals.push total
  let mut r2 := ChaCha.Rng.seeded seed16
  for _ in [0:10] do
    let (chosen, next) := LeaderSchedule.below r2 total
    r2 := next
    let mut at_ := 0
    while at_ < 999 && totals[at_]! <= chosen do
      at_ := at_ + 1
    picks := picks ++ s!"{at_} "
  IO.println s!"weighted picks: {picks}"
  IO.println s!"      expected: 975 160 534 962 420 805 172 884 871 654 "

  -- whole schedules, in order
  IO.println s!"epoch 1, stakes 10 20 30:          {order 1 #[10, 20, 30] 12 1}"
  IO.println s!"                         expected: 1 1 2 1 1 0 0 1 2 1 0 1 "
  IO.println s!"the same, two slots each:          {order 1 #[10, 20, 30] 12 2}"
  IO.println s!"                         expected: 1 1 2 1 1 0 "
  IO.println s!"epoch 1, stakes 30 10 20:          {order 1 #[30, 10, 20] 12 1}"
  IO.println s!"                         expected: 2 2 0 2 2 1 1 2 0 2 1 2 "
  IO.println s!"seven validators:                  {order 1 #[10, 20, 25, 30, 35, 40, 100] 15 1}"
  IO.println s!"                         expected: 4 5 6 3 4 1 2 3 6 4 2 4 5 6 6 "
  IO.println s!"epoch 457468:                      {order 457468 #[10, 20, 30] 12 1}"
  IO.println s!"                         expected: 2 2 0 1 0 2 1 2 1 2 2 2 "
  IO.println s!"epoch 3466545, 14 slots:           {order 3466545 #[10, 20, 30] 14 1}"
  IO.println s!"                         expected: 2 2 0 0 2 1 1 1 0 0 2 2 1 2 "

  -- long schedules over 65,536 validators, hashed
  IO.println s!"epoch 42, equal stakes:  {hashed 42 10000 0}"
  IO.println s!"               expected: G2MGFXgdLATXWr1336i8PTcaUMc4GbJRMJdbxiarCttr"
  IO.println s!"epoch 42, stake i:       {hashed 42 10000 1}"
  IO.println s!"               expected: 9xLLKyyqF5YrdwPSDbqh5oVamSF7cqPqQLxEyHTexEiP"
  IO.println s!"epoch 346436, stake i³:  {hashed 346436 1000 3}"
  IO.println s!"               expected: H2bw3Y2AjxJyK7smy1ZBB4LJ7MY3i9bPQM3YdAChAww2"
  IO.println s!"epoch 454357, stake i²:  {hashed 454357 10000 2}"
  IO.println s!"               expected: 7KwK44Y7V3GzJLN8aGZtM8EEfAYmRvaiDyKYV6jg4MQn"

  -- the same validator and stake listed twice counts once; a validator with nothing is never drawn
  let twice := #[voterOf 1 50, voterOf 2 70, voterOf 1 50]
  IO.println s!"listed twice: {(LeaderSchedule.sorted twice).size} validators; nobody staked: {(LeaderSchedule.draw #[voterOf 1 0] 5 8 4).size} slots drawn"
