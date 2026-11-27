import Solana.Accounts
import Crypto.Sha256

/-! The accounts store: a log and a hash index, filled, closed and reopened.

Addresses here are chosen to be awkward: many share the eight bytes the
index keeps, so that telling them apart depends on the log. (Runs as
machine code only: it uses files, which the official interpreter has no
implementation of here.) -/

def dir : String := "build/tests/store-tmp"

/-- Address number `i`. Every fourth one shares its first eight bytes with the one before. -/
def address (i : Nat) : ByteArray := Id.run do
  let h := Sha256.hash (s!"account {i}").toUTF8
  if i % 4 != 3 then
    return h
  let before := Sha256.hash (s!"account {i - 1}").toUTF8
  return before.extract 0 8 ++ h.extract 8 32

def dataOf (i version : Nat) : ByteArray := Id.run do
  let n := (i * 37 + version * 11) % 700
  let mut b := ByteArray.emptyWithCapacity n
  for k in [0:n] do
    b := b.push (i + k + version).toUInt8
  return b

/-- The record of account `i` at `version`, as the log holds it. -/
def recordOf (i version : Nat) : ByteArray :=
  let key := address i
  let owner := Sha256.hash "owner".toUTF8
  let data := dataOf i version
  Accounts.record (key ++ owner ++ data) 0 32 (1000 + i.toUInt64 + version.toUInt64) 0xFFFFFFFFFFFFFFFF (5 + version.toUInt64) (i % 9 == 0) 64 data.size

def main : IO Unit := do
  Sys.mkdir "build"
  Sys.mkdir "build/tests"
  Sys.mkdir dir
  let count := 20000
  let seed : UInt64 := 0x1234567890ABCDEF
  let mut shard ← Accounts.Shard.create dir 7 seed
  let mut pending := ByteArray.emptyWithCapacity 300000
  let mut fresh := 0
  let mut replaced := 0
  -- every account once, then every third again in a newer version
  for pass in [0:2] do
    for i in [0:count] do
      if pass == 0 || i % 3 == 0 then
        let r := recordOf i pass
        let (entry, loc) ← shard.locate pending r 0
        if loc == Accounts.none_ then
          fresh := fresh + 1
        else
          replaced := replaced + 1
        shard ← shard.point entry (loc == Accounts.none_) (Accounts.Shard.keyOf r 0) (shard.flushed + pending.size.toUInt64)
        pending := pending ++ r
        if pending.size >= 262144 then
          shard ← shard.flush pending
          pending := ByteArray.emptyWithCapacity 300000
  IO.println s!"filed {fresh} accounts, replaced {replaced}; the index holds {shard.used} in a table of {1 <<< shard.bits}"
  shard ← shard.close pending dir 7
  IO.println s!"closed: failed {shard.failed}"

  -- reopened: every account is found, in its newest version, byte for byte
  let store ← Accounts.Shard.openRead dir 7 seed
  IO.println s!"reopened: failed {store.failed}, table of {1 <<< store.bits}"
  let mut right := 0
  for i in [0:count] do
    let (_, loc) ← store.locate ByteArray.empty (address i) 0
    if loc != Accounts.none_ then
      let r ← store.recordAt ByteArray.empty loc
      let version := if i % 3 == 0 then 1 else 0
      let want := recordOf i version
      if r == want.extract 0 (Accounts.headerSize + Accounts.recDataLen want) && Accounts.recSlot r == 5 + version.toUInt64 then
        right := right + 1
  IO.println s!"found {right} of {count}, each its newest version"
  let mut absent := 0
  for i in [count:count + 5000] do
    let (_, loc) ← store.locate ByteArray.empty (address i) 0
    if loc == Accounts.none_ then
      absent := absent + 1
  IO.println s!"addresses never filed: {absent} of 5000 not found"
  let r ← store.recordAt ByteArray.empty (← store.locate ByteArray.empty (address 9) 0).2
  IO.println s!"account 9: {Accounts.recLamports r} lamports, executable {Accounts.recExecutable r}, {Accounts.recDataLen r} bytes, slot {Accounts.recSlot r}, rent epoch {Accounts.recRentEpoch r}"
  -- with another seed the table cannot be read: entries are placed by the seed
  let other ← Accounts.Shard.openRead dir 7 (seed + 1)
  let mut lost := 0
  for i in [0:2000] do
    let (_, loc) ← other.locate ByteArray.empty (address i) 0
    if loc == Accounts.none_ then
      lost := lost + 1
  IO.println s!"opened with the wrong seed: {lost} of 2000 not found"
  IO.println s!"a shard that is not there: failed {(← Accounts.Shard.openRead dir 8 seed).failed}"
  IO.println s!"which shard: {Accounts.shardOf (address 1) 0 16} {Accounts.shardOf (address 2) 0 16} {Accounts.shardOf (address 3) 0 16} of 16"
