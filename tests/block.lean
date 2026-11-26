import Solana.Block
import Encoding.Base58

/-! A real block, checked offline.

`tests/blocks/mainnet-474319150.block` is a block of Solana mainnet as
validators served it: its 320 data shreds, the key of its leader, and the two
values that tie it to its parent (the parent's blockhash and the Merkle root
of the parent's last set of shreds). It was fetched with `leansol block
--save`.

The block must pass every check, and each kind of damage must be caught by
the check meant for it. -/

def key (name : String) : ByteArray := Sha256.hash name.toUTF8

def none_ : Array ByteArray := Array.emptyWithCapacity 0

def leaf (s : ByteArray) : ByteArray := Sha256.hash ((ByteArray.empty.push 0) ++ s)

def summary (label : String) (r : Block.Report) : IO Unit :=
  IO.println s!"{label}: {if r.error == "" then "valid" else r.error}"

def main : IO Unit := do
  let file ← IO.FS.readBinFile "tests/blocks/mainnet-474319150.block"
  let leader := file.extract 8 40
  let previous := file.extract 40 72
  let previousRoot := file.extract 72 104
  let mut shreds : Array ByteArray := Array.emptyWithCapacity 512
  for i in [0:(file.size - 104) / Shred.dataPayload] do
    shreds := shreds.push (file.extract (104 + Shred.dataPayload * i) (104 + Shred.dataPayload * (i + 1)))
  -- the leader is one of several keys it might be, and not the first tried
  let candidates := key "somebody" ++ key "somebody else" ++ leader ++ key "another"
  let r := Block.verify shreds candidates 0 previous previousRoot
  summary "the block" r
  IO.println s!"  slot {r.slot}, parent {r.parentSlot}, leader {Base58.encode r.leader}"
  IO.println s!"  {r.shreds} shreds in {r.sets} sets, {r.bytes} bytes"
  IO.println s!"  {r.entries} entries, {r.ticks} tick, {r.hashes} hashes recomputed, linked to its parent: {r.linked}"
  IO.println s!"  {r.transactions} transactions, {r.signatures} signatures"
  IO.println s!"  blockhash {Base58.encode r.blockhash}"
  IO.println s!"  bank hash {Base58.encode r.bankHash}, parent id {Base58.encode r.parentId}"
  IO.println s!"  produced by {r.producer}"
  -- how the transactions are laid out: the newer layout puts the message first and the signatures last
  let mut newer := 0
  let mut older := 0
  for batch in Block.batches shreds do
    if Wire.u64 batch 0 != 0 then
      match Entry.parseBatch batch with
      | none => IO.println "  a batch does not parse"
      | some entries =>
        for e in entries do
          let mut o := e.start
          for _ in [0:e.count] do
            let (tx, next) := Tx.parseAt batch o
            o := next
            if tx.message.v1 then
              newer := newer + 1
            else
              older := older + 1
  IO.println s!"  {newer} transactions in the v1 layout, {older} in the older ones"

  -- one byte of one shred's data changed: its Merkle path no longer leads to the signed root
  let damaged := shreds[7]!.set! 200 (shreds[7]![200]! ^^^ 1)
  summary "a byte of shred 7 changed" (Block.verify (shreds.set! 7 damaged) candidates 0 previous previousRoot)
  -- a signature byte changed: the set is no longer signed by the leader
  let unsigned := shreds[64]!.set! 3 (shreds[64]![3]! ^^^ 1)
  summary "the signature on shred 64 changed" (Block.verify (shreds.set! 64 unsigned) candidates 0 previous previousRoot)
  -- two shreds swapped
  summary "shreds 3 and 4 swapped" (Block.verify ((shreds.set! 3 shreds[4]!).set! 4 shreds[3]!) candidates 0 previous previousRoot)
  -- the last shred missing: the block does not end
  summary "the last shred missing" (Block.verify shreds.pop candidates 0 previous previousRoot)
  -- the leader is not among the keys known
  summary "the leader unknown" (Block.verify shreds (key "somebody" ++ key "another") 0 previous previousRoot)
  -- a different parent: neither the proof of history nor the chain of sets connects
  summary "another block's hash as parent" (Block.verify shreds candidates 0 (key "not the parent") previousRoot)
  summary "another block's last set as parent" (Block.verify shreds candidates 0 previous (key "not the parent"))
  -- with the parent unknown the block still checks, from its first entry on
  let alone := Block.verify shreds candidates 0 ByteArray.empty ByteArray.empty
  summary "with no parent known" alone
  IO.println s!"  linked to its parent: {alone.linked}, hashes recomputed: {alone.hashes}"

  -- proof of history on its own: ticks hash the previous hash, entries with transactions mix their signatures in
  let start := key "start"
  let once := Sha256.hash start
  IO.println s!"a tick of 1 hash: {Entry.expected start 1 none_ == once}; of 3: {Entry.expected start 3 none_ == Sha256.hash (Sha256.hash once)}"
  let a := key "signature a" ++ key "a"
  let b := key "signature b" ++ key "b"
  let c := key "signature c" ++ key "c"
  IO.println s!"one signature mixed in: {Entry.expected start 1 #[a] == Sha256.hash (start ++ leaf a)}"
  IO.println s!"three signatures: the odd one pairs with itself: {Entry.signatureRoot #[a, b, c] == Sha256.hash ((ByteArray.empty.push 1) ++ Sha256.hash ((ByteArray.empty.push 1) ++ leaf a ++ leaf b) ++ Sha256.hash ((ByteArray.empty.push 1) ++ leaf c ++ leaf c))}"
