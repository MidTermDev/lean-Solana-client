import Solana.Epoch

/-! The arithmetic of an epoch's end (`Solana.Epoch`).

* The budget of mainnet's epoch 1099 from the supply the chain had and the
  rewards it was about to pay: the chain wrote 61,809,996,919,773.
* SipHash-1-3 on three inputs, against the reference implementation, and
  the block (of 522) that pays a given stake account.
* A stake warming up and cooling down against a history in which the
  cluster's stake changes by a fixed amount each epoch; and the rewards of
  stake accounts in each of the situations the rules tell apart. -/

def u64s (values : Array UInt64) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for v in values do
    b := Wire.putU64 b v
  return b

def key (n : UInt8) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for _ in [0:32] do
    b := b.push n
  return b

def show_ (r : Epoch.Reward) : String :=
  if r.due then s!"reward {r.staker}, commission {r.commission}, stake {r.stake}, credits {r.credits}" else "nothing"

def main : IO Unit := do
  let inflation := u64s #[0x3FB47AE147AE147B, 0x3F8EB851EB851EB8, 0x3FC3333333333333, 0, 0]
  IO.println s!"budget of epoch 1099: {Epoch.budget inflation 1099 432000 638347057048434772}"
  IO.println s!"years to slot 474768000: {Epoch.years 64368000 474768000}"
  IO.println s!"siphash: {SipHash.hash13 0 0 "hello, world, this is a test of sip".toUTF8} {SipHash.hash13 0 0 ByteArray.empty} {SipHash.hash13 0 0 "12345678".toUTF8}"
  IO.println s!"partition: {Epoch.partition (key 7) (key 9) 522}"
  IO.println s!"distinct: {(Epoch.distinct (key 1 ++ key 2 ++ key 1 ++ key 3 ++ key 2)).size / 32} of 5"
  -- a history of epochs 100 down to 91: 1,000,000 effective, 100,000 activating, 50,000 deactivating in each
  let mut history := Fast.pushZeros (u64s #[0]) 16384
  for e in [91:101] do
    history := Epoch.historyWith history e.toUInt64 1000000 100000 50000
  IO.println s!"history: {Wire.u64 history 0} entries, the newest for epoch {Wire.u64 history 8}, epoch 95 at {Epoch.past history 95}, epoch 90 at {Epoch.past history 90}"
  let voter := key 5
  let never : UInt64 := 0xFFFFFFFFFFFFFFFF
  let spans : Array UInt64 := #[95, never, 95, 98, 80, never, 80, 97, never, never, 96, 96]
  for k in [0:spans.size / 2] do
    let activation := spans[2 * k]!
    let deactivation := spans[2 * k + 1]!
    let mut line := s!"stake of 250,000 from {activation} to {deactivation}:"
    for epoch in [94:102] do
      let (effective, activating, deactivating) := Epoch.status ⟨voter, 250000, activation, deactivation, 0⟩ epoch.toUInt64 history
      line := line ++ s!" {effective}/{activating}/{deactivating}"
    IO.println line
  -- rewards for epoch 100: the validator earned credits 5,000 to 9,000 in it, with 1,000,000 delegated to it
  let stake : Epoch.Delegation := ⟨voter, 250000, 80, 0xFFFFFFFFFFFFFFFF, 5000⟩
  IO.println s!"a quarter of the stake, 7% commission: {show_ (Epoch.reward stake 100 250000 true 3000000 2282880 true 100 9000 5000 1000000 700)}"
  IO.println s!"credits seen up to 7,000 already:      {show_ (Epoch.reward { stake with credits := 7000 } 100 250000 true 3000000 2282880 true 100 9000 5000 1000000 700)}"
  IO.println s!"credits seen beyond the validator's:   {show_ (Epoch.reward { stake with credits := 9500 } 100 250000 true 3000000 2282880 true 100 9000 5000 1000000 700)}"
  IO.println s!"a validator with no credits this epoch: {show_ (Epoch.reward stake 100 250000 true 3000000 2282880 true 99 5000 4000 1000000 700)}"
  IO.println s!"a stake made in this epoch:            {show_ (Epoch.reward { stake with activation := 100 } 100 0 true 3000000 2282880 true 100 9000 5000 1000000 700)}"
  IO.println s!"a validator not admitted:              {show_ (Epoch.reward stake 100 250000 true 3000000 2282880 false 0 0 0 0 0)}"
  IO.println s!"the same, its balance short:           {show_ (Epoch.reward stake 100 250000 true 2400000 2282880 false 0 0 0 0 0)}"
  IO.println s!"all commission, none:                  {show_ (Epoch.reward stake 100 250000 true 3000000 2282880 true 100 9000 5000 1000000 10000)} / {show_ (Epoch.reward stake 100 250000 true 3000000 2282880 true 100 9000 5000 1000000 0)}"
