import Sys
import Fmt
import Net.Ip
import Encoding.Base58
import Solana.Block
import Solana.Repair
import RunProgram

/-!
`leansol block`: fetch a block from the network and check it.

Asks a running node (this program with `--metrics`) who is out there and
what the newest slot is, then asks those validators for the block's shreds
one by one with the repair protocol, and checks what comes back: Merkle
paths, the leader's signature, the chain of sets, the proof of history, and
every transaction signature. Nothing is taken from the node on trust except
the list of keys the leader might be.
-/

namespace RunBlock

def usage : String :=
  "leansol block — fetch a block from the cluster and verify it\n" ++
  "\n" ++
  "usage: leansol block [SLOT] [options]\n" ++
  "  SLOT                the slot to fetch (default: a few seconds behind the newest)\n" ++
  "  --node HOST:PORT    a running leansol node's --metrics address to learn peers from\n" ++
  "                      (default 127.0.0.1:9184)\n" ++
  "  --peers N           how many validators to ask (default 24)\n" ++
  "  --save FILE         also write the block to FILE: its shreds, its leader, and what links it to its parent\n" ++
  "  --file FILE         verify a block saved with --save instead of fetching one; needs no network\n" ++
  "\n" ++
  "Checks: each shred's Merkle path, the leader's signature on every set of shreds, that each\n" ++
  "set follows the one before, that the entries' hashes form an unbroken proof of history\n" ++
  "from the parent block, and every transaction signature.\n"

/-- A validator that can be asked for shreds. -/
structure Peer where
  key : ByteArray
  ip : UInt32
  port : UInt16
  /-- 0 = not tried, 1 = answered, 2 = silent so far -/
  state : Nat
  deriving Inhabited

/-- GET over plain HTTP. Returns the body, or empty. -/
def httpGet (ip : UInt32) (port : UInt16) (path : String) : IO ByteArray := do
  let fd ← Sys.tcpSocket
  Sys.setTimeout fd 20 5000
  if Sys.isErr (← Sys.connect fd ip port) then
    Sys.close fd
    return ByteArray.empty
  let _ ← Sys.sendAll fd s!"GET {path} HTTP/1.0\r\nHost: leansol\r\n\r\n".toUTF8
  let mut all := ByteArray.emptyWithCapacity 1048576
  repeat
    let chunk ← Sys.read fd 65536
    if chunk.size == 0 then
      break
    all := all ++ chunk
  Sys.close fd
  for i in [0:all.size] do
    if i + 3 < all.size && all[i]! == 13 && all[i + 1]! == 10 && all[i + 2]! == 13 && all[i + 3]! == 10 then
      return all.extract (i + 4) all.size
  return ByteArray.empty

/-- Where `needle` first occurs in `b` at or after `from_`, or `b.size`. -/
def findAt (b needle : ByteArray) (from_ : Nat) : Nat := Id.run do
  if needle.size == 0 || b.size < needle.size then
    return b.size
  for i in [from_:b.size - needle.size + 1] do
    if b[i]! == needle[0]! && Wire.eqAt b i needle 0 needle.size then
      return i
  return b.size

/-- The text after `"name": ` at or after `from_`, up to the next quote, comma or newline. -/
def jsonField (b : ByteArray) (name : String) (from_ : Nat) : String := Id.run do
  let key := s!"\"{name}\": ".toUTF8
  let at_ := findAt b key from_
  if at_ == b.size then
    return ""
  let mut start := at_ + key.size
  if start < b.size && b[start]! == 34 then
    start := start + 1
  let mut stop := start
  while stop < b.size && b[stop]! != 34 && b[stop]! != 44 && b[stop]! != 10 && b[stop]! != 125 do
    stop := stop + 1
  return String.fromUTF8! (b.extract start stop)

def number (s : String) : UInt64 :=
  match RunProgram.number s with
  | some n => n
  | none => 0

/-- Splits `ip:port`. Returns 0 for the address if it does not parse. -/
def parseAddr (s : String) : UInt32 × UInt16 :=
  let f := RunProgram.split s 58
  if f.size != 2 then (0, 0) else (Ip.parse f[0]!, (number f[1]!).toUInt16)

/-- Elements `[start, stop)` of an array of shreds. -/
def slice (a : Array ByteArray) (start stop : Nat) : Array ByteArray := Id.run do
  let mut out : Array ByteArray := Array.emptyWithCapacity (stop - start)
  for i in [start:stop] do
    out := out.push a[i]!
  return out

/-- State of fetching one slot's data shreds. -/
structure Fetch where
  shreds : Array ByteArray
  /-- index of the slot's last shred, or `Wire.bad` while unknown -/
  last : Nat
  have_ : Nat
  requests : Nat
  pings : Nat
  /-- the first index asked for, and how many were -/
  first : Nat
  wanted : Nat

/-- Did everything that was asked for arrive? -/
def Fetch.complete (f : Fetch) : Bool := f.last != Wire.bad && f.have_ >= f.wanted

/-- From the last shreds of a block: its blockhash and the Merkle root of its
last set, which the next block must build on. Empty if they cannot be read. -/
def ending (f : Fetch) : ByteArray × ByteArray := Id.run do
  if !f.complete then
    return (ByteArray.empty, ByteArray.empty)
  -- walk back from the end to just after the previous "data complete" mark
  let mut from_ := f.last
  while from_ > f.first && (Shred.parse f.shreds[from_ - 1]!).flags &&& Shred.flagDataComplete == 0 do
    from_ := from_ - 1
  if from_ == f.first && f.first != 0 then
    return (ByteArray.empty, Block.rootOf f.shreds[f.last]!)
  let mut tail : Array ByteArray := Array.emptyWithCapacity (f.last + 1 - from_)
  for i in [from_:f.last + 1] do
    tail := tail.push f.shreds[i]!
  return (Block.lastHash tail, Block.rootOf f.shreds[f.last]!)

/-- Fetches the data shreds of `slot` by repair: first asks everyone for the
slot's highest shred, to learn where it ends, then asks for each shred it
lacks, one validator per shred, and asks again only for those still missing
after a while. With `tail` non-zero only the last `tail` shreds are fetched
(enough to read how a block ends). On return `have_ == wanted` if everything
asked for arrived. -/
def fetchFrom (sock : UInt64) (seed pubkey : ByteArray) (peers0 : Array Peer) (slot : UInt64) (tail : Nat) (budgetMs : UInt64)
    (already : Array ByteArray) (knownLast : Nat) : IO (Fetch × Array Peer) := do
  let mut peers := peers0
  let mut shreds : Array ByteArray := Array.replicate 2048 ByteArray.empty
  let mut last := knownLast
  let mut have_ := 0
  -- shreds in hand before asking: only the others are requested
  for i in [0:already.size] do
    if i < 2048 && already[i]!.size != 0 then
      shreds := shreds.set! i already[i]!
      have_ := have_ + 1
  let mut requests := 0
  let mut pings := 0
  let mut nonce : UInt64 := 1
  -- when each shred was last asked for
  let mut asked : Array UInt64 := Array.replicate 2048 0
  let mut first := 0
  let mut wanted := if knownLast == Wire.bad then 0 else knownLast + 1
  let started ← Sys.nowMs
  let mut round := 0
  let mut turn := 0
  repeat
    let now ← Sys.nowMs
    if now - started > budgetMs || (last != Wire.bad && have_ >= wanted) then
      break
    -- ask: while the end is unknown, everyone for the highest shred; then, for each missing shred, the next peer in turn
    if last == Wire.bad then
      for k in [0:peers.size] do
        let p := peers[k]!
        if p.state != 2 || round % 4 == 0 then
          let _ ← Sys.sendTo sock p.ip p.port (Repair.request Repair.highestWindowIndex seed pubkey p.key now nonce slot 0)
          nonce := nonce + 1
          requests := requests + 1
    else
      let mut sent := 0
      for i in [first:last + 1] do
        if shreds[i]!.size == 0 && sent < 400 && now - asked[i]! >= 700 then
          asked := asked.set! i now
          -- prefer peers that have answered; fall back to the rest
          let mut chosen := Wire.bad
          for _ in [0:peers.size] do
            turn := (turn + 1) % peers.size
            if chosen == Wire.bad && peers[turn]!.state == 1 then
              chosen := turn
          if chosen == Wire.bad then
            turn := (turn + 1) % peers.size
            chosen := turn
          let p := peers[chosen]!
          let _ ← Sys.sendTo sock p.ip p.port (Repair.request Repair.windowIndex seed pubkey p.key now nonce slot i.toUInt64)
          nonce := nonce + 1
          requests := requests + 1
          sent := sent + 1
    round := round + 1
    -- listen for a while
    let listenUntil := now + (if last == Wire.bad then 300 else 100)
    repeat
      let d ← Sys.recvFrom sock 1500
      if d.data.size == 0 then
        if (← Sys.nowMs) >= listenUntil then
          break
      else
        let mut who := Wire.bad
        for k in [0:peers.size] do
          if peers[k]!.ip == d.ip && peers[k]!.port == d.port then
            who := k
        if who != Wire.bad then
          if d.data.size == 132 then
            -- a stranger's ping: prove we hold our key, then it will answer
            if Repair.isPing d.data then
              let _ ← Sys.sendTo sock d.ip d.port (Repair.pong seed pubkey d.data)
              pings := pings + 1
          else if d.data.size == Shred.dataPayload + 4 then
            let p := d.data.extract 0 Shred.dataPayload
            let h := Shred.parse p
            if h.ok && h.isData && h.slot == slot && h.index < 2048 then
              peers := peers.set! who { peers[who]! with state := 1 }
              if h.flags &&& Shred.flagLastInSlot == Shred.flagLastInSlot && last == Wire.bad then
                last := h.index.toNat
                first := if tail != 0 && last + 1 > tail then last + 1 - tail else 0
                wanted := last + 1 - first
                if tail != 0 then
                  have_ := 0
              if shreds[h.index.toNat]!.size == 0 && (last == Wire.bad || h.index.toNat >= first) then
                shreds := shreds.set! h.index.toNat p
                have_ := have_ + 1
        if (← Sys.nowMs) >= listenUntil then
          break
    for k in [0:peers.size] do
      if peers[k]!.state == 0 then
        peers := peers.set! k { peers[k]! with state := 2 }
  return (⟨shreds, last, have_, requests, pings, first, wanted⟩, peers)

/-- `fetchFrom` with nothing in hand. -/
def fetch (sock : UInt64) (seed pubkey : ByteArray) (peers : Array Peer) (slot : UInt64) (tail : Nat) (budgetMs : UInt64)
    : IO (Fetch × Array Peer) :=
  fetchFrom sock seed pubkey peers slot tail budgetMs (Array.emptyWithCapacity 0) Wire.bad

def magic : ByteArray := "LSBLOCK1".toUTF8

/-- A saved block: a tag, the leader's key, the parent's blockhash and last Merkle root, then the shreds. -/
def pack (r : Block.Report) (previous previousRoot : ByteArray) (shreds : Array ByteArray) : ByteArray := Id.run do
  let mut b := magic ++ r.leader ++ previous ++ previousRoot
  for p in shreds do
    b := b ++ p
  return b

def printReport (r : Block.Report) (previous : ByteArray) (elapsedMs : UInt64) : IO Unit := do
  IO.println s!"leader       {Base58.encode r.leader}"
  IO.println s!"parent       slot {r.parentSlot}{if r.linked then s!", blockhash {Base58.encode previous}" else " (could not be fetched: the first entry is not checked)"}"
  IO.println s!"shreds       {r.shreds} in {r.sets} sets: every Merkle path valid, every set signed by the leader and chained to the one before{if r.linked then ", the first to the parent block" else ""}"
  IO.println s!"entries      {r.entries} ({r.ticks} ticks) · {Fmt.thousands r.bytes.toUInt64} bytes"
  IO.println s!"history      {Fmt.thousands r.hashes} hashes recomputed: the chain is unbroken"
  IO.println s!"transactions {Fmt.thousands r.transactions.toUInt64} · {Fmt.thousands r.signatures.toUInt64} signatures, all valid"
  IO.println s!"blockhash    {Base58.encode r.blockhash}"
  if r.bankHash.size == 32 then
    IO.println s!"bank hash    {Base58.encode r.bankHash} (as the leader computed it; not recomputed here)"
  if r.producer != "" then
    IO.println s!"produced by  {r.producer}"
  IO.println s!"verified     in {elapsedMs} ms"

/-- Verifies a block saved with `--save`. -/
def fromFile (path : String) : IO Unit := do
  let b ← Sys.readFile path 0x4000000
  if b.size < 104 + Shred.dataPayload || b.extract 0 8 != magic || (b.size - 104) % Shred.dataPayload != 0 then
    RunProgram.fail s!"{path} is not a saved block"
  let mut shreds : Array ByteArray := Array.emptyWithCapacity ((b.size - 104) / Shred.dataPayload)
  for i in [0:(b.size - 104) / Shred.dataPayload] do
    shreds := shreds.push (b.extract (104 + Shred.dataPayload * i) (104 + Shred.dataPayload * (i + 1)))
  let t0 ← Sys.nowMs
  let r := Block.verify shreds (b.extract 8 40) 0 (b.extract 40 72) (b.extract 72 104)
  let t1 ← Sys.nowMs
  IO.println s!"slot         {r.slot} (from {path})"
  if r.error != "" then
    IO.println s!"result       INVALID: {r.error}"
    Sys.exit 1
  printReport r (b.extract 40 72) (t1 - t0)

def main : IO Unit := do
  let argc ← Sys.argc
  let mut slot : UInt64 := 0
  let mut save := ""
  let mut node := "127.0.0.1:9184"
  let mut want : UInt64 := 24
  let mut i := 2
  while i < argc do
    let a ← Sys.arg i
    if a == "--help" || a == "-h" then
      IO.print usage
      return
    if a == "--node" || a == "--peers" || a == "--save" || a == "--file" then
      if i + 1 >= argc then
        RunProgram.fail s!"{a} needs a value"
      let v ← Sys.arg (i + 1)
      if a == "--file" then
        fromFile v
        return
      if a == "--node" then
        node := v
      else if a == "--save" then
        save := v
      else
        want := number v
      i := i + 2
    else
      slot := number a
      if slot == 0 then
        RunProgram.fail s!"'{a}' is not a slot number"
      i := i + 1

  let (nodeIp, nodePort) := parseAddr node
  if nodeIp == 0 then
    RunProgram.fail "--node expects IP:PORT"
  let summary ← httpGet nodeIp nodePort "/summary.json"
  let listing ← httpGet nodeIp nodePort "/nodes.json"
  if summary.size == 0 || listing.size == 0 then
    RunProgram.fail s!"no leansol node answers at {node} (start one with --metrics, or name one with --node)"
  let tip := number (jsonField summary "tipSlot" 0)
  let shredVersion := jsonField summary "shredVersion" 0
  if slot == 0 then
    slot := tip - 24
  -- the nodes of the listing: every identity is a key the leader might be; those with a repair address can be asked
  let mut candidates := ByteArray.emptyWithCapacity (32 * 8192)
  let mut known : Array Peer := Array.emptyWithCapacity 4096
  let mut at_ := findAt listing "\"identity\": ".toUTF8 0
  while at_ < listing.size do
    let key := Base58.decode (jsonField listing "identity" at_)
    let repair := jsonField listing "repair" at_
    if key.size == 32 then
      candidates := candidates ++ key
      let (ip, port) := parseAddr repair
      if ip != 0 && port != 0 && jsonField listing "shredVersion" at_ == shredVersion then
        known := known.push ⟨key, ip, port, 0⟩
    at_ := findAt listing "\"identity\": ".toUTF8 (at_ + 1)
  if known.size == 0 then
    RunProgram.fail "the node knows no validator with a repair address yet; give it a minute"
  -- a random sample of them
  let seed ← IO.getRandomBytes 32
  let pubkey := Ed25519.publicKey seed
  let mut peers : Array Peer := Array.emptyWithCapacity want.toNat
  let stride := if known.size > want.toNat then known.size / want.toNat else 1
  let offset := (Wire.u64 seed 0).toNat % stride
  for k in [0:want.toNat] do
    if offset + k * stride < known.size then
      peers := peers.push known[offset + k * stride]!
  IO.println s!"slot         {slot} (the cluster is at {tip})"
  IO.println s!"asking       {peers.size} of {known.size} validators with a repair address; {candidates.size / 32} keys could be the leader"

  let sock ← Sys.udpSocket
  let _ ← Sys.bind sock 0 0
  Sys.setTimeout sock 20 20
  Sys.setRecvBuffer sock 8388608
  let t0 ← Sys.nowMs
  let (got, asked) ← fetch sock seed pubkey peers slot 0 12000
  let t1 ← Sys.nowMs
  let mut answered := 0
  for p in asked do
    if p.state == 1 then
      answered := answered + 1
  if got.last == Wire.bad then
    RunProgram.fail s!"nobody returned the end of slot {slot} ({got.requests} requests, {got.pings} pings answered): it may have been skipped, or is too old or too new"
  if !got.complete then
    RunProgram.fail s!"only {got.have_} of {got.last + 1} shreds arrived in time"
  IO.println s!"fetched      {got.have_} shreds in {t1 - t0} ms · {got.requests} requests · {answered} validators answered · {got.pings} pings answered"
  let shreds := slice got.shreds 0 (got.last + 1)

  -- the parent's blockhash, from the end of the parent block: its last batch of entries
  let first := Shred.parse shreds[0]!
  let parent := slot - first.parentOffset
  let (tail, _) ← fetch sock seed pubkey asked parent 64 6000
  let (previous, previousRoot) := ending tail
  let t2 ← Sys.nowMs
  let r := Block.verify shreds candidates Wire.bad previous previousRoot
  let t3 ← Sys.nowMs
  if r.error != "" then
    IO.println s!"result       INVALID: {r.error}"
    Sys.exit 1
  printReport r previous (t3 - t2)
  if save != "" then
    if !(← Sys.writeFileMode save (pack r previous previousRoot shreds) 0x1a4) then
      RunProgram.fail s!"cannot write {save}"
    IO.println s!"saved        {save}"

end RunBlock
