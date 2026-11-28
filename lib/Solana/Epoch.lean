import Double
import Crypto.SipHash
import Solana.Alpenglow

/-!
# The end of an epoch

Every 432,000 slots the chain settles the epoch that ended: stake that was
warming up or cooling down moves on, every stake account is owed a share of
what its validator earned, and the next epoch is given its budget. These
are the calculations, as Agave makes them; `client/RunReplay.lean` applies
them to the accounts.
-/

namespace Epoch

/-- What a stake account says of its delegation. -/
structure Delegation where
  voter : ByteArray
  stake : UInt64
  activation : UInt64
  deactivation : UInt64
  /-- its validator's credits when it was last rewarded -/
  credits : UInt64
  deriving Inhabited

/-- Is this the data of a stake account that is delegated? -/
def delegated (data : ByteArray) : Bool := data.size >= 197 && Wire.u32 data 0 == 2

def delegation (data : ByteArray) : Delegation :=
  ⟨data.extract 124 156, Wire.u64 data 156, Wire.u64 data 164, Wire.u64 data 172, Wire.u64 data 188⟩

-- The stake history (the sysvar's data) is a count, then for each epoch, newest first: the epoch, and the
-- cluster's effective, activating and deactivating stake in it.

/-- Where the history's entry for `epoch` is, or 0. -/
def past (history : ByteArray) (epoch : UInt64) : Nat :=
  let latest := Wire.u64 history 8
  if Wire.u64 history 0 == 0 || epoch > latest || latest - epoch >= Wire.u64 history 0 then 0
  else 8 + 32 * (latest - epoch).toNat

/-- The history with one more epoch at its front (it keeps 512). -/
def historyWith (history : ByteArray) (epoch effective activating deactivating : UInt64) : ByteArray := Id.run do
  let count := (Wire.u64 history 0).toNat
  let kept := if count >= 512 then 511 else count
  let mut b := Wire.putU64 (ByteArray.emptyWithCapacity history.size) (kept + 1).toUInt64
  for v in #[epoch, effective, activating, deactivating] do
    b := Wire.putU64 b v
  b := history.copySlice 8 b b.size (32 * kept)
  return Fast.pushZeros b (history.size - b.size)

/-- How much of `portion` may warm up or cool down in one epoch: its share of 9% of the cluster's effective stake. -/
def allowance (portion clusterPortion clusterEffective : UInt64) : UInt64 :=
  if clusterPortion == 0 then 0
  else if clusterPortion <= 9 * clusterEffective / 100 then portion
  else Alpenglow.ratio (9 * portion) clusterEffective clusterPortion 100

/-- A delegation's stake in `epoch`: effective, activating and deactivating. -/
def status (d : Delegation) (epoch : UInt64) (history : ByteArray) : UInt64 × UInt64 × UInt64 := Id.run do
  let mut effective := d.stake
  let mut activating : UInt64 := 0
  -- (an activation epoch of all ones marks the stake the chain began with: effective from the start)
  if d.activation == 0xFFFFFFFFFFFFFFFF then
    effective := d.stake
  else if d.activation == d.deactivation || epoch < d.activation then
    effective := 0
  else if epoch == d.activation then
    effective := 0
    activating := d.stake
  else if past history d.activation != 0 then
    -- warming up, epoch by epoch, as fast as the cluster's history allows
    let mut at_ := past history d.activation
    let mut before := d.activation
    effective := 0
    for _ in [0:513] do
      if at_ == 0 || Wire.u64 history (at_ + 16) == 0 then
        break
      let newly := allowance (d.stake - effective) (Wire.u64 history (at_ + 16)) (Wire.u64 history (at_ + 8))
      effective := effective + (if newly == 0 then 1 else newly)
      if effective >= d.stake then
        effective := d.stake
        break
      before := before + 1
      if before >= epoch || before >= d.deactivation then
        break
      at_ := past history before
    activating := d.stake - effective
  if epoch < d.deactivation then
    return (effective, activating, 0)
  if epoch == d.deactivation then
    return (effective, 0, effective)
  -- cooling down the same way
  let mut at_ := past history d.deactivation
  if at_ == 0 then
    return (0, 0, 0)
  let mut before := d.deactivation
  for _ in [0:513] do
    if at_ == 0 || Wire.u64 history (at_ + 24) == 0 then
      break
    let newly := allowance effective (Wire.u64 history (at_ + 24)) (Wire.u64 history (at_ + 8))
    effective := if newly >= effective then 0 else effective - (if newly == 0 then 1 else newly)
    before := before + 1
    if effective == 0 || before >= epoch then
      break
    at_ := past history before
  return (effective, 0, effective)

-- ------------------------------------------------------------------ rewards

/-- What the end of an epoch means for one stake account, if anything (`due`): its reward, its
validator's commission on it, and the stake and credits it is left with. -/
structure Reward where
  due : Bool
  staker : UInt64
  commission : UInt64
  stake : UInt64
  credits : UInt64
  deriving Inhabited

/-- Is a delegation of `stake` still the `current` one once it is cut down to what the balance, less
the `minimum` the account must hold, can back? -/
def backed (current stake balance minimum : UInt64) : Bool :=
  (if balance < minimum then 0 else if stake < balance - minimum then stake else balance - minimum) == current

/-- The reward of a stake account for `epoch`, which has just ended. `effective` and `active` are its
stake in that epoch and whether any of it was effective or activating; `lamports` and `minimum` its
balance and what its size must hold; `admitted` whether its validator is one the next epoch admits, and
if so the validator's last entry of credits (its epoch, the credits, the credits before it; zeros if it
has none), `total` the stake delegated to the validator in the epoch, and `bps` its commission. -/
def reward (d : Delegation) (epoch effective : UInt64) (active : Bool) (lamports minimum : UInt64) (admitted : Bool)
    (creditsEpoch earnedTo creditsBefore total bps : UInt64) : Reward := Id.run do
  if !admitted then
    return ⟨active && !(backed d.stake d.stake lamports minimum), 0, 0, d.stake, d.credits⟩
  let mut points : UInt64 := 0
  let mut seen := d.credits
  -- credits gone backwards, an epoch that paid nothing, or a stake made in this very epoch: no reward, but the credits are noted
  let mut forced := earnedTo < d.credits || d.activation == epoch
  if earnedTo < d.credits then
    seen := earnedTo
  else if earnedTo > d.credits && creditsEpoch == epoch then
    let earned := earnedTo - (if d.credits < creditsBefore then creditsBefore else d.credits)
    seen := earnedTo
    if earned != 0 && effective != 0 then
      if total == 0 then
        forced := true
      else
        points := Alpenglow.ratio earned effective total 1
  let paid := forced || points != 0 || (active && seen != d.credits)
  if forced then
    points := 0
  let staker := if bps >= 10000 then 0 else Alpenglow.ratio points (10000 - bps) 10000 1
  let stake := if d.stake + staker < staker then 0xFFFFFFFFFFFFFFFF else d.stake + staker
  if !paid && !(active && !(backed d.stake stake (lamports + staker) minimum)) then
    return ⟨false, 0, 0, d.stake, d.credits⟩
  return ⟨true, staker, points - staker, stake, if paid then seen else d.credits⟩

/-- The 32-byte keys of `keys`, each of them once. -/
def distinct (keys : ByteArray) : ByteArray := Id.run do
  let mut size := 1024
  while size < keys.size / 16 do
    size := 2 * size
  -- a table of where each key seen so far is (its number plus one), found from eight of its bytes
  let mut table : Array UInt64 := Array.replicate size 0
  let mut out := ByteArray.emptyWithCapacity keys.size
  for k in [0:keys.size / 32] do
    let mut at_ := (Wire.u64 keys (32 * k + 8)).toNat % size
    while table[at_]! != 0 && !(Wire.eqAt keys (32 * (table[at_]!.toNat - 1)) keys (32 * k) 32) do
      at_ := if at_ + 1 == size then 0 else at_ + 1
    if table[at_]! == 0 then
      table := table.set! at_ (k + 1).toUInt64
      out := keys.copySlice (32 * k) out out.size 32
  return out

/-- Which of `partitions` blocks pays the reward of the stake account `key`: the blocks are numbered from
the one after the epoch's first, whose parent's blockhash is `seed`. -/
def partition (seed key : ByteArray) (partitions : UInt64) : UInt64 :=
  Fast.mulHi partitions (SipHash.hash13 0 0 (seed ++ key))

-- ------------------------------------------------------------------- budget

/-- Mainnet's slots per year as slots became shorter: the slot each figure took effect at, and the figure (a double). -/
def slotsPerYear : Array UInt64 := #[0, 0x4192cf346bef9db2, 440640000, 0x41957f1756c8b439, 442368000, 0x41991445e53f7cee,
  447984000, 0x419e1853dfe56042, 454896000, 0x41a2cf346bef9db2]

/-- The slots per year in force at `slot`. -/
def yearAt (slot : UInt64) : UInt64 := Id.run do
  let mut rate := slotsPerYear[1]!
  for k in [0:slotsPerYear.size / 2] do
    if slotsPerYear[2 * k]! <= slot then
      rate := slotsPerYear[2 * k + 1]!
  return rate

/-- The years between two slots, as a double. -/
def years (start stop : UInt64) : UInt64 := Id.run do
  let mut cursor := start
  let mut duration : UInt64 := 0
  for k in [0:slotsPerYear.size / 2] do
    let from_ := slotsPerYear[2 * k]!
    if from_ > start && from_ < stop then
      duration := Double.add duration (Double.div (Double.ofU64 (from_ - cursor)) (yearAt cursor))
      cursor := from_
  return Double.add duration (Double.div (Double.ofU64 (stop - cursor)) (yearAt cursor))

/-- The most an epoch can pay in rewards: the inflation rate at its start (which has fallen by `taper` a
year from `initial` since slot 64,368,000, and stops at `terminal`), times the supply, times the epoch's
length in years, in double precision as the chain computes it. `inflation` is the snapshot manifest's:
initial, terminal, taper, the foundation's share and its term. -/
def budget (inflation : ByteArray) (epoch slotsPerEpoch supply : UInt64) : UInt64 :=
  let year := years 64368000 (epoch * slotsPerEpoch)
  let tapered := Double.mul (Wire.u64 inflation 0) (Double.pow (Double.sub 0x3FF0000000000000 (Wire.u64 inflation 16)) year)
  let total := if tapered > Wire.u64 inflation 8 then tapered else Wire.u64 inflation 8
  let rate := if year < Wire.u64 inflation 32 then Double.sub total (Double.mul total (Wire.u64 inflation 24)) else total
  let length := Double.div (Double.ofU64 slotsPerEpoch) (yearAt (epoch * slotsPerEpoch))
  Double.toU64 (Double.mul (Double.mul rate (Double.ofU64 supply)) length)

end Epoch
