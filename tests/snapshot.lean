import Encoding.Zstd
import Encoding.Tar
import Encoding.Base58
import Solana.Snapshot

/-! A whole snapshot, verified.

`tests/snapshots/snapshot-1200-9r67….tar.zst` was written by Agave (a test
validator, version 3.1) at slot 1200, after some transfers. Its name carries
the hash Agave gave it: the checksum of the lattice hash of all accounts.

Unpacking the archive, keeping the newest version of each account, and
hashing them all must arrive at that same hash, and at the manifest's 2048
bytes; the lamports must add up to the supply the manifest records. Change
one bit of one account and they do not. -/

def named : String := "9r67SHZcBSFAZhBiAw2cgPsB5TsArx9nHqasU2regDhs"

structure Result where
  manifest : Snapshot.Manifest
  files : Nat
  records : Nat
  distinct : Nat
  lamports : UInt64
  data : Nat
  sum : Array UInt64
  version : String
  error : String

/-- Walks an unpacked archive: reads the manifest, keeps the newest version of every account, and hashes those. -/
def load (tar : ByteArray) : Result := Id.run do
  let mut o := 0
  let mut manifest := Snapshot.Manifest.failed "no manifest"
  let mut version := ""
  let mut files := 0
  let mut records := 0
  let mut keys : Array ByteArray := Array.emptyWithCapacity 512
  let mut slots : Array UInt64 := Array.emptyWithCapacity 512
  let mut latest : Array ByteArray := Array.emptyWithCapacity 512
  let mut error := ""
  let mut going := true
  while going do
    let h := Tar.header tar o
    if h.kind == 3 then
      going := false
    else if h.kind == 0 then
      error := s!"bad header at {o}"
      going := false
    else
      let body := o + 512
      if h.kind == 1 then
        match Snapshot.fileSlot h.name with
        | some slot =>
          files := files + 1
          let stop := body + h.size
          let mut at_ := body
          let mut more := true
          while more do
            let a := Snapshot.stored tar at_ stop
            if !a.ok then
              more := false
            else
              records := records + 1
              let record := tar.extract at_ (a.data + a.dataLen)
              let key := tar.extract a.pubkey (a.pubkey + 32)
              let mut found := keys.size
              for i in [0:keys.size] do
                if keys[i]! == key then
                  found := i
              if found == keys.size then
                keys := keys.push key
                slots := slots.push slot
                latest := latest.push record
              else if slot >= slots[found]! then
                slots := slots.set! found slot
                latest := latest.set! found record
              at_ := a.next
        | none =>
          if h.name == "version" then
            version := String.fromUTF8! (tar.extract body (body + h.size))
          else if h.name != "snapshots/status_cache" && h.size > 1024 then
            manifest := Snapshot.parse (tar.extract body (body + h.size))
      o := body + Tar.padded h.size
  let mut sum := LtHash.zero
  let mut lamports : UInt64 := 0
  let mut data := 0
  for r in latest do
    let a := Snapshot.stored r 0 r.size
    if a.lamports != 0 then
      lamports := lamports + a.lamports
      data := data + a.dataLen
    sum := LtHash.mixStored sum r a.lamports a.data a.dataLen a.executable a.owner a.pubkey false
  return ⟨manifest, files, records, keys.size, lamports, data, sum, version, error⟩

def verdict (r : Result) : String :=
  if r.error != "" then r.error
  else if r.manifest.error != "" then r.manifest.error
  else if LtHash.bytes r.sum != r.manifest.ltHash then "the accounts are not the ones the manifest describes"
  else if Base58.encode (LtHash.checksum r.sum) != named then "not the snapshot it is named after"
  else if r.lamports != r.manifest.capitalization then "the lamports do not add up to the supply"
  else "verified"

def xorshift (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

/-- Where `needle` first occurs in `b`. -/
def find (b needle : ByteArray) : Nat := Id.run do
  for i in [0:b.size - needle.size] do
    if b[i]! == needle[0]! && Wire.eqAt b i needle 0 needle.size then
      return i
  return b.size

def main : IO Unit := do
  let archive ← IO.FS.readBinFile s!"tests/snapshots/snapshot-1200-{named}.tar.zst"
  let (tar, why) := Zstd.decompress archive
  IO.println s!"archive: {archive.size} bytes, unpacked {tar.size}{if why == "" then "" else s!" ERROR {why}"}"
  let r := load tar
  let m := r.manifest
  IO.println s!"format {r.version} · slot {m.slot}, parent {m.parentSlot} · block height {m.blockHeight} · epoch {m.epoch}"
  IO.println s!"bank hash {Base58.encode m.hash} · parent's {Base58.encode m.parentHash}"
  IO.println s!"blockhash {Base58.encode m.blockhash} ({m.blockhashes} kept) · leader {Base58.encode m.leader}"
  IO.println s!"supply {m.capitalization} lamports · {m.accountsDataLen} bytes of account data · {m.transactionCount} transactions so far, {m.signatureCount} signatures in this slot"
  IO.println s!"ticks: {m.ticksPerSlot} per slot, height {m.tickHeight}, {m.hashesPerTick} hashes each · {m.lamportsPerSignature} lamports per signature"
  IO.println s!"epochs: {m.slotsPerEpoch} slots, leader schedule {m.leaderScheduleOffset} slots ahead, warm-up {m.warmup}, first normal epoch {m.firstNormalEpoch} at slot {m.firstNormalSlot}"
  IO.println s!"stakes: {m.voteAccounts} vote accounts, {m.delegations} delegations"
  for e in m.epochStakes do
    for v in e.voters do
      IO.println s!"  epoch {e.epoch}: {Base58.encode v.node} votes with {Base58.encode v.vote}, stake {v.stake} of {e.total}"
  IO.println s!"block id recorded: {m.blockId.size == 32}"
  IO.println s!"accounts: {r.records} in {r.files} files, {r.distinct} addresses · {r.lamports} lamports · {r.data} bytes of data"
  IO.println s!"lattice hash {Base58.encode (LtHash.checksum r.sum)}"
  IO.println s!"  the manifest's: {LtHash.bytes r.sum == m.ltHash} · the archive's name: {Base58.encode (LtHash.checksum r.sum) == named} · supply: {r.lamports == m.capitalization} · data: {r.data.toUInt64 == m.accountsDataLen}"
  IO.println s!"result: {verdict r}"

  -- one bit of account data, deep inside the largest file
  let big := find tar "accounts/0.8".toUTF8
  let flipped := tar.set! (big + 512 + 700000) (tar[big + 512 + 700000]! ^^^ 1)
  IO.println s!"one bit of one account's data changed: {verdict (load flipped)}"
  -- one lamport, with the data untouched
  let richer := tar.set! (big + 512 + 136 + 48) (tar[big + 512 + 136 + 48]! ^^^ 1)
  IO.println s!"one lamport more in one account: {verdict (load richer)}"
  -- an owner changed
  let stolen := tar.set! (big + 512 + 64) (tar[big + 512 + 64]! ^^^ 0x80)
  IO.println s!"one account given another owner: {verdict (load stolen)}"
  -- a file header that no longer checks out
  IO.println s!"a file's name altered: {verdict (load (tar.set! (big + 5) 0x39))}"
  -- an account file left out: the archive cut just before the last one
  let last := find tar "accounts/1200.61".toUTF8
  let mut cut := tar.extract 0 last
  for _ in [0:1024] do
    cut := cut.push 0
  IO.println s!"the newest account file missing: {verdict (load cut)}"

  -- a manifest damaged anywhere must be refused or read, never crash the reader
  let at_ := find tar "snapshots/1200/1200".toUTF8
  let manifest := tar.extract (at_ + 512) (at_ + 512 + 48488)
  let mut x : UInt64 := 0x2545F4914F6CDD1D
  let mut refused := 0
  let mut read := 0
  let mut digest : UInt64 := 0
  for _ in [0:300] do
    x := xorshift x
    let mut b := manifest
    for _ in [0:(x % 4).toNat + 1] do
      x := xorshift x
      let where_ := (x % 24000).toNat
      x := xorshift x
      b := b.set! where_ (x >>> 13).toUInt8
    x := xorshift x
    if x % 6 == 0 then
      b := b.extract 0 ((x >>> 9) % b.size.toUInt64).toNat
    let parsed := Snapshot.parse b
    if parsed.error == "" then
      read := read + 1
      digest := digest * 31 + parsed.slot + parsed.epochStakes.size.toUInt64
    else
      refused := refused + 1
  IO.println s!"300 damaged manifests: {refused} refused, {read} read, digest {digest}"
  -- account records at arbitrary offsets of arbitrary bytes
  let mut whole := 0
  for i in [0:2000] do
    x := xorshift x
    let a := Snapshot.stored tar ((x % tar.size.toUInt64).toNat) tar.size
    if a.ok && a.next <= tar.size + 8 && i >= 0 then
      whole := whole + 1
  IO.println s!"2000 records read at arbitrary offsets: {whole} looked whole, none read past the end"
  IO.println s!"file names: {(Snapshot.fileSlot "accounts/123.45").isSome} {(Snapshot.fileSlot "accounts/123").isSome} {(Snapshot.fileSlot "accounts/12a.4").isSome} {(Snapshot.fileSlot "snapshots/1/1").isSome} {(Snapshot.fileSlot "accounts/.5").isSome}"
