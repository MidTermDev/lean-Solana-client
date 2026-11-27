import Sys
import Fmt
import Net.Ip
import Encoding.Zstd
import Encoding.Tar
import Encoding.Base58
import Encoding.Hex
import Solana.Snapshot
import Solana.Accounts
import RunBlock

/-!
# `leansol snapshot` and `leansol account`

Loads a snapshot, the whole state of the chain at one slot, from a file or
straight from a validator, without ever holding the archive:

    bytes → Zstandard → tar → accounts → one of several processes, by address

Each of those processes keeps one shard of the accounts store: it files
every account it is sent, keeps only the newest version of each, and adds
that version's lattice hash to a running sum. When the stream ends the sums
are added together, and the result has to be the lattice hash the manifest
records and the hash the snapshot is named after, the one validators
announce. An account altered, missing or added changes it.
-/

namespace RunSnapshot

def usage : String :=
  "usage: leansol snapshot (--file ARCHIVE | --from HOST:PORT | --url URL) [options]\n" ++
  "       leansol snapshot --find [--nodes HOST:PORT]\n" ++
  "       leansol account ADDRESS [--accounts DIR] [--data FILE]\n" ++
  "\n" ++
  "  snapshot            load a snapshot into an accounts store, verifying every account against\n" ++
  "                      the snapshot's lattice hash\n" ++
  "    --file ARCHIVE    a snapshot archive on disk (snapshot-<slot>-<hash>.tar.zst)\n" ++
  "    --from HOST:PORT  a validator's RPC port: asks it for its newest full snapshot\n" ++
  "    --url URL         http://HOST:PORT/snapshot-<slot>-<hash>.tar.zst\n" ++
  "    --accounts DIR    where the store goes (default: accounts)\n" ++
  "    --workers N       processes filing accounts, and shards in the store (default 16)\n" ++
  "    --expect HASH     the snapshot hash to insist on (default: the one in the archive's name)\n" ++
  "    --replace         overwrite a store that is already in DIR\n" ++
  "    --peek            read the manifest, say what the snapshot holds and needs, and stop\n" ++
  "    --nodes HOST:PORT a running leansol node (default 127.0.0.1:9184): its view of gossip says\n" ++
  "                      how many validators announce the snapshot being loaded\n" ++
  "    --find            list the full snapshots validators announce in gossip, and who serves them\n" ++
  "  account ADDRESS     look an account up in a store\n"

def fail (message : String) : IO Unit := do
  IO.eprintln s!"leansol: {message}"
  Sys.exit 1

-- ------------------------------------------------------------------- sources

/-- A response's status, length and redirect target, and the start of its body. -/
structure Response where
  fd : UInt64
  status : Nat
  length : UInt64
  location : String
  body : ByteArray
  deriving Inhabited

def noResponse : Response := ⟨0, 0, 0, "", ByteArray.empty⟩

/-- The value of header `name` (lower case) in the header block `head`, or "". -/
def headerValue (head : ByteArray) (name : String) : String := Id.run do
  let mut lower := ByteArray.emptyWithCapacity head.size
  for c in head do
    lower := lower.push (if c >= 65 && c <= 90 then c + 32 else c)
  let key := s!"\r\n{name}:".toUTF8
  let at_ := RunBlock.findAt lower key 0
  if at_ == lower.size then
    return ""
  let mut start := at_ + key.size
  while start < head.size && head[start]! == 32 do
    start := start + 1
  let mut stop := start
  while stop < head.size && head[stop]! != 13 do
    stop := stop + 1
  return String.fromUTF8! (head.extract start stop)

/-- Sends a request (`GET`, or `HEAD` for the headers alone) and reads the response headers. `from_` asks for the body from that byte on. -/
def httpOpen (method : String) (ip : UInt32) (port : UInt16) (path : String) (from_ timeoutMs : UInt64) : IO Response := do
  let fd ← Sys.tcpSocket
  Sys.setTimeout fd 20 timeoutMs
  Sys.setTimeout fd 21 timeoutMs
  if Sys.isErr (← Sys.connect fd ip port) then
    Sys.close fd
    return noResponse
  let range := if from_ == 0 then "" else s!"Range: bytes={from_}-\r\n"
  let request := s!"{method} {path} HTTP/1.1\r\nHost: {Ip.toString ip}:{port}\r\nAccept: */*\r\nConnection: close\r\n{range}\r\n"
  if !(← Sys.sendAll fd request.toUTF8) then
    Sys.close fd
    return noResponse
  let mut head := ByteArray.emptyWithCapacity 65536
  let stop := "\r\n\r\n".toUTF8
  let mut at_ := 0
  repeat
    let chunk ← Sys.read fd 16384
    if chunk.size == 0 then
      Sys.close fd
      return noResponse
    head := head ++ chunk
    at_ := RunBlock.findAt head stop 0
    if at_ != head.size || head.size > 60000 then
      break
  if at_ == head.size || head.size < 12 then
    Sys.close fd
    return noResponse
  -- "HTTP/1.1 200 OK"
  let status := (head[9]!.toNat - 48) * 100 + (head[10]!.toNat - 48) * 10 + (head[11]!.toNat - 48)
  let headers := head.extract 0 (at_ + 2)
  return ⟨fd, status, RunBlock.number (headerValue headers "content-length"), headerValue headers "location", head.extract (at_ + 4) head.size⟩

/-- Where the bytes of the archive come from. -/
structure Source where
  http : Bool
  fd : UInt64
  ip : UInt32
  port : UInt16
  path : String
  /-- the archive's size, 0 if not known -/
  total : UInt64
  received : UInt64
  /-- bytes of the body that came with the headers -/
  early : ByteArray
  failures : Nat
  reconnects : Nat
  /-- after reconnecting to a server that starts the file over: bytes still to drop -/
  discard : UInt64
  error : String
  deriving Inhabited

/-- The next bytes of the archive; none when it has ended (or `error` is set).

A connection that drops is taken up again where it stopped. Some servers
honour a request for the rest of a file; a validator's does not and sends
the file from its start, so then what was already received is read again
and dropped. -/
def Source.next (s0 : Source) : IO (Source × ByteArray) := do
  let mut s := s0
  repeat
    let mut chunk := s.early
    if chunk.size != 0 then
      s := { s with early := ByteArray.empty }
    else
      chunk ← Sys.read s.fd 1048576
    if chunk.size != 0 then
      if s.discard == 0 then
        return ({ s with received := s.received + chunk.size.toUInt64, failures := 0 }, chunk)
      -- still catching up with where the last connection stopped
      if chunk.size.toUInt64 <= s.discard then
        s := { s with discard := s.discard - chunk.size.toUInt64 }
      else
        let fresh := chunk.extract s.discard.toNat chunk.size
        return ({ s with discard := 0, received := s.received + fresh.size.toUInt64, failures := 0 }, fresh)
    else
      if !s.http || s.total == 0 || s.received >= s.total then
        return (s, chunk)
      -- the connection ended early
      Sys.close s.fd
      if s.failures >= 10 then
        break
      IO.sleep 3000
      let r ← httpOpen "GET" s.ip s.port s.path s.received 30000
      if r.status == 206 && r.length == s.total - s.received then
        s := { s with fd := r.fd, early := r.body, discard := 0, failures := s.failures + 1, reconnects := s.reconnects + 1 }
      else if r.status == 200 && r.length == s.total then
        s := { s with fd := r.fd, early := r.body, discard := s.received, failures := s.failures + 1, reconnects := s.reconnects + 1 }
      else
        if r.fd != 0 then
          Sys.close r.fd
        -- (no descriptor: the next read fails, and another attempt follows)
        s := { s with fd := 0xFFFFFFFF, failures := s.failures + 1 }
  return ({ s with error := s!"the connection was lost at byte {s.received} of {s.total} and could not be resumed" }, ByteArray.empty)

/-- The last component of a path. -/
def baseName (path : String) : String := Id.run do
  let b := path.toUTF8
  let mut start := 0
  for i in [0:b.size] do
    if b[i]! == 47 then
      start := i + 1
  return String.fromUTF8! (b.extract start b.size)

/-- The slot and hash in an archive's name, `snapshot-<slot>-<hash>.tar.zst`; slot 0 and "" if it is not named so. -/
def nameParts (name : String) : UInt64 × String := Id.run do
  let b := name.toUTF8
  let front := "snapshot-".toUTF8
  if b.size < 20 || !(Wire.eqAt b 0 front 0 9) then
    return (0, "")
  let mut o := 9
  let mut slot : UInt64 := 0
  while o < b.size && b[o]! >= 48 && b[o]! <= 57 do
    slot := slot * 10 + (b[o]! - 48).toUInt64
    o := o + 1
  if o == 9 || o >= b.size || b[o]! != 45 then
    return (0, "")
  let mut stop := o + 1
  while stop < b.size && b[stop]! != 46 do
    stop := stop + 1
  return (slot, String.fromUTF8! (b.extract (o + 1) stop))

def sol (lamports : UInt64) : String := Id.run do
  let mut fraction := toString (lamports % 1000000000)
  while fraction.length < 9 do
    fraction := "0" ++ fraction
  return s!"{Fmt.thousands (lamports / 1000000000)}.{fraction}"

def size (bytes : UInt64) : String :=
  if bytes >= 10737418240 then s!"{Fmt.tenths (bytes * 10 / 1073741824)} GiB"
  else if bytes >= 10485760 then s!"{Fmt.tenths (bytes * 10 / 1048576)} MiB"
  else s!"{Fmt.thousands bytes} bytes"

-- -------------------------------------------------------------------- gossip

/-- How many times `needle` occurs in `b`. -/
def occurrences (b needle : ByteArray) : Nat := Id.run do
  let mut n := 0
  let mut o := RunBlock.findAt b needle 0
  while o < b.size do
    n := n + 1
    o := RunBlock.findAt b needle (o + needle.size)
  return n

/-- The node list of a running leansol node, or empty. -/
def nodeList (nodes : String) : IO ByteArray := do
  let (ip, port) := RunBlock.parseAddr nodes
  if ip == 0 then
    return ByteArray.empty
  RunBlock.httpGet ip port "/nodes.json"

/-- `leansol snapshot --find`: which full snapshots validators announce, and who serves them. -/
def find (nodes : String) : IO Unit := do
  let list ← nodeList nodes
  if list.size == 0 then
    fail s!"no leansol node answers at {nodes} (start one, or name another with --nodes)"
  let tip := RunBlock.number (RunBlock.jsonField list "tipSlot" 0)
  -- every node is one line of the list
  let mut names : Array String := #[]
  let mut counts : Array Nat := #[]
  let mut sources : Array String := #[]
  let mut announcing := 0
  let key := "\"fullSnapshot\": \"".toUTF8
  let mut o := RunBlock.findAt list key 0
  while o < list.size do
    let name := RunBlock.jsonField list "fullSnapshot" o
    -- the node's RPC address comes just before, on the same line
    let mut lineStart := o
    while lineStart > 0 && list[lineStart - 1]! != 10 do
      lineStart := lineStart - 1
    let rpcAt := RunBlock.findAt list "\"rpc\": \"".toUTF8 lineStart
    let rpc := if rpcAt < o then RunBlock.jsonField list "rpc" lineStart else ""
    announcing := announcing + 1
    let mut found := names.size
    for i in [0:names.size] do
      if names[i]! == name then
        found := i
    if found == names.size then
      names := names.push name
      counts := counts.push 1
      sources := sources.push rpc
    else
      counts := counts.set! found (counts[found]! + 1)
      if rpc != "" then
        sources := sources.set! found (if sources[found]! == "" then rpc else sources[found]! ++ " " ++ rpc)
    o := RunBlock.findAt list key (o + key.size)
  IO.println s!"{announcing} validators announce a full snapshot in gossip: {names.size} different ones. The chain is at slot {tip}."
  IO.println "Those that some validator offers over HTTP, newest first:\n"
  -- newest first, among those with a source
  let mut shown := 0
  let mut last : UInt64 := 0xFFFFFFFFFFFFFFFF
  while shown < 6 do
    let mut best := names.size
    let mut bestSlot : UInt64 := 0
    for i in [0:names.size] do
      let (slot, _) := nameParts s!"snapshot-{names[i]!}.tar.zst"
      if sources[i]! != "" && slot < last && slot >= bestSlot then
        best := i
        bestSlot := slot
    if best == names.size then
      break
    last := bestSlot
    shown := shown + 1
    let (_, hash) := nameParts s!"snapshot-{names[best]!}.tar.zst"
    IO.println s!"slot {bestSlot} ({Fmt.thousands (tip - bestSlot)} slots ago) · hash {hash} · announced by {counts[best]!} validators"
    -- ask a few of its sources what they would send (the headers only)
    let mut asked := 0
    let mut serving := 0
    let mut silent := 0
    for source in RunProgram.split sources[best]! 32 do
      let (ip, port) := RunBlock.parseAddr source
      let mut note := ""
      if ip != 0 && Ip.isPublic ip && asked < 12 && serving < 2 then
        asked := asked + 1
        let r ← httpOpen "HEAD" ip port "/snapshot.tar.bz2" 0 3000
        if r.fd != 0 then
          Sys.close r.fd
        if r.status == 303 || r.status == 302 || r.status == 301 || r.status == 307 then
          if baseName r.location == s!"snapshot-{names[best]!}.tar.zst" then
            let file ← httpOpen "HEAD" ip port r.location 0 3000
            if file.fd != 0 then
              Sys.close file.fd
            if file.status == 200 then
              serving := serving + 1
              note := s!"serves it, {size file.length}:\n      leansol snapshot --url http://{source}{r.location}"
            else
              note := s!"answers {file.status}"
          else
            note := s!"now serves another ({baseName r.location})"
        else if r.status != 0 then
          note := s!"answers {r.status}"
        else
          silent := silent + 1
      if note != "" then
        IO.println s!"    {source} {note}"
    if silent != 0 then
      IO.println s!"    ({silent} more advertise an RPC port that does not answer from here)"
  if shown == 0 then
    IO.println "  (none: no validator announcing a full snapshot advertises an RPC port)"

-- ------------------------------------------------------------------- workers

-- What each worker reports, in its own 4096 bytes of a shared page:
--   +0 accounts received   +8 distinct addresses   +16 holding lamports   +24 older versions replaced
--   +32 older versions that arrived late   +40 lamports   +48 bytes of data   +56 bytes in the log
--   +64 failed   +72 finished   +80 closed accounts (their newest version holds nothing)
--   +2048 the lattice hash of its accounts

/-- Files the accounts sent down `fd` into shard `id`, keeping the newest version of each and the lattice hash of what it keeps. -/
def worker (dir : String) (id : Nat) (seed fd page : UInt64) : IO Unit := do
  let mut shard ← Accounts.Shard.create dir id seed
  -- the end of the shard's log, not yet written to disk
  let mut pending := ByteArray.emptyWithCapacity 4300000
  let mut sum := LtHash.zero
  let mut rest := ByteArray.empty
  let mut received : UInt64 := 0
  let mut live : UInt64 := 0
  let mut closed : UInt64 := 0
  let mut replaced : UInt64 := 0
  let mut late : UInt64 := 0
  let mut lamports : UInt64 := 0
  let mut dataBytes : UInt64 := 0
  repeat
    let chunk ← Sys.read fd 1048576
    if chunk.size == 0 then
      break
    let buf := if rest.size == 0 then chunk else rest ++ chunk
    let mut o := 0
    repeat
      -- each account arrives as the slot of its file, then the record as the file had it
      let a := Snapshot.stored buf (o + 8) buf.size
      if !a.ok then
        break
      let slot := Wire.u64 buf o
      received := received + 1
      let (entry, loc) ← shard.locate pending buf a.pubkey
      if entry == 0 then
        Mem.store64 (page + 64) 1
        Sys.exit 1
      let mut keep := true
      if loc != Accounts.none_ then
        let old ← shard.recordAt pending loc
        let oldData := Accounts.recData old
        if old.size < Accounts.headerSize || oldData.size != Accounts.recDataLen old then
          Mem.store64 (page + 64) 1
          Sys.exit 1
        if slot >= Accounts.recSlot old then
          -- a newer version: what the old one contributed is taken back
          replaced := replaced + 1
          let had := Accounts.recLamports old
          if had != 0 then
            live := live - 1
            lamports := lamports - had
            dataBytes := dataBytes - (Accounts.recDataLen old).toUInt64
            sum := LtHash.mixAccount sum had oldData (Accounts.recExecutable old) (old.extract 32 64) (old.extract 0 32) true
          else
            closed := closed - 1
        else
          late := late + 1
          keep := false
      if keep then
        let r := Accounts.record buf a.pubkey a.owner a.lamports a.rentEpoch slot a.executable a.data a.dataLen
        shard ← shard.point entry (loc == Accounts.none_) (Accounts.Shard.keyOf r 0) (shard.flushed + pending.size.toUInt64)
        pending := pending ++ r
        if pending.size >= 4194304 then
          shard ← shard.flush pending
          pending := ByteArray.emptyWithCapacity 4300000
        if a.lamports != 0 then
          live := live + 1
          lamports := lamports + a.lamports
          dataBytes := dataBytes + a.dataLen.toUInt64
          sum := LtHash.mixStored sum buf a.lamports a.data a.dataLen a.executable a.owner a.pubkey false
        else
          closed := closed + 1
      o := a.data + a.dataLen
    rest := buf.extract o buf.size
    Mem.store64 page received
    Mem.store64 (page + 8) shard.used.toUInt64
    Mem.store64 (page + 16) live
    Mem.store64 (page + 56) (shard.flushed + pending.size.toUInt64)
    if shard.failed then
      Mem.store64 (page + 64) 1
  shard ← shard.close pending dir id
  Mem.store64 page received
  Mem.store64 (page + 8) shard.used.toUInt64
  Mem.store64 (page + 16) live
  Mem.store64 (page + 24) replaced
  Mem.store64 (page + 32) late
  Mem.store64 (page + 40) lamports
  Mem.store64 (page + 48) dataBytes
  Mem.store64 (page + 56) shard.flushed
  Mem.store64 (page + 80) closed
  for i in [0:256] do
    Mem.store64 (page + 2048 + 8 * i.toUInt64) sum[i]!
  if shard.failed || rest.size != 0 then
    Mem.store64 (page + 64) 1
  Mem.store64 (page + 72) 1

-- -------------------------------------------------------------------- report

def printManifest (m : Snapshot.Manifest) : IO Unit := do
  IO.println s!"slot         {m.slot} · block height {Fmt.thousands m.blockHeight} · epoch {m.epoch}"
  IO.println s!"bank hash    {Base58.encode m.hash}"
  IO.println s!"blockhash    {Base58.encode m.blockhash} ({m.blockhashes} recent ones kept)"
  IO.println s!"supply       {sol m.capitalization} SOL"
  IO.println s!"account data {size m.accountsDataLen}"
  let mut epochs := ""
  let mut voters := 0
  let mut staked : UInt64 := 0
  for e in m.epochStakes do
    epochs := if epochs == "" then toString e.epoch else s!"{epochs}, {e.epoch}"
    if e.epoch == m.epoch then
      voters := e.voters.size
      staked := e.total
  IO.println s!"stakes       {Fmt.thousands m.voteAccounts.toUInt64} vote accounts, {Fmt.thousands m.delegations.toUInt64} delegations · recorded for epochs {epochs}"
  if voters != 0 then
    IO.println s!"             this epoch: {Fmt.thousands voters.toUInt64} validators with stake, {sol staked} SOL in all"

/-- Writes one line over the last when the output is a terminal, a new line otherwise. -/
def progress (tty : Bool) (line : String) : IO Unit := do
  if tty then
    let _ ← Sys.write 2 s!"\r{line}   ".toUTF8
  else
    IO.eprintln line

-- ---------------------------------------------------------------------- main

def main : IO Unit := do
  let argc ← Sys.argc
  let mut file := ""
  let mut from_ := ""
  let mut url := ""
  let mut dir := "accounts"
  let mut workers := 16
  let mut expect := ""
  let mut replace := false
  let mut peek := false
  let mut nodes := "127.0.0.1:9184"
  let mut finding := false
  let mut i := 2
  while i < argc do
    let a ← Sys.arg i
    if a == "--replace" then
      replace := true
      i := i + 1
    else if a == "--peek" then
      peek := true
      i := i + 1
    else if a == "--find" then
      finding := true
      i := i + 1
    else if a == "--help" || a == "-h" then
      IO.print usage
      return
    else if i + 1 >= argc then
      fail s!"{a} needs a value\n{usage}"
    else
      let v ← Sys.arg (i + 1)
      if a == "--file" then
        file := v
      else if a == "--from" then
        from_ := v
      else if a == "--url" then
        url := v
      else if a == "--accounts" then
        dir := v
      else if a == "--expect" then
        expect := v
      else if a == "--nodes" then
        nodes := v
      else if a == "--workers" then
        workers := (RunBlock.number v).toNat
      else
        fail s!"unknown option {a}\n{usage}"
      i := i + 2
  if finding then
    find nodes
    return
  if (if file == "" then 0 else 1) + (if from_ == "" then 0 else 1) + (if url == "" then 0 else 1) != 1 then
    fail s!"give one of --file, --from and --url\n{usage}"
  if workers == 0 || workers > 64 then
    fail "--workers must be between 1 and 64"
  -- ---- open the source
  let mut src : Source := ⟨false, 0, 0, 0, "", 0, 0, ByteArray.empty, 0, 0, 0, ""⟩
  let mut name := ""
  if file != "" then
    let fd ← Sys.openFile file 0
    if Sys.isErr fd then
      fail s!"cannot open {file}"
    src := { src with fd := fd, total := ← Sys.fileSize fd }
    name := baseName file
  else
    let mut hostPort := from_
    let mut path := "/snapshot.tar.bz2"
    if url != "" then
      let u := url.toUTF8
      if u.size < 8 || !(Wire.eqAt u 0 "http://".toUTF8 0 7) then
        fail "--url must start with http://"
      let slash := RunBlock.findAt u "/".toUTF8 7
      hostPort := String.fromUTF8! (u.extract 7 slash)
      path := if slash == u.size then "/snapshot.tar.bz2" else String.fromUTF8! (u.extract slash u.size)
    let (ip, port) := RunBlock.parseAddr hostPort
    if ip == 0 || port == 0 then
      fail s!"'{hostPort}' is not an address and port (a numeric address is needed)"
    let mut r ← httpOpen "GET" ip port path 0 30000
    -- a validator answers the generic name with the name of its newest snapshot
    let mut hops := 0
    while (r.status == 301 || r.status == 302 || r.status == 303 || r.status == 307) && hops < 3 do
      Sys.close r.fd
      let to := r.location.toUTF8
      if to.size == 0 || to[0]! != 47 then
        fail s!"{hostPort} redirects to another host ({r.location}); pass that with --url if it is wanted"
      path := r.location
      r ← httpOpen "GET" ip port path 0 30000
      hops := hops + 1
    if r.status != 200 then
      fail (if r.status == 0 then s!"{hostPort} does not answer" else s!"{hostPort} answers {r.status} for {path}")
    src := { src with http := true, fd := r.fd, ip := ip, port := port, path := path, total := r.length, early := r.body }
    name := baseName path
  let (namedSlot, namedHash) := nameParts name
  if expect == "" then
    expect := namedHash
  -- what gossip says about this snapshot, if a node of ours is listening
  let mut announced := ""
  if namedSlot != 0 then
    let list ← nodeList nodes
    if list.size != 0 then
      let same := occurrences list s!"\"fullSnapshot\": \"{namedSlot}-{expect}\"".toUTF8
      let slotOnly := occurrences list s!"\"fullSnapshot\": \"{namedSlot}-".toUTF8
      announced := if slotOnly == 0 then s!"no validator in gossip announces a full snapshot at slot {namedSlot} (node at {nodes})"
        else if same == slotOnly then s!"{same} validators in gossip announce this snapshot, slot and hash; none announces another for the slot"
        else s!"{same} validators in gossip announce this snapshot; {slotOnly - same} ANNOUNCE ANOTHER HASH FOR THE SAME SLOT"
  IO.println s!"snapshot     {name}{if src.total != 0 then s!" · {size src.total}" else ""}{if src.http then s!" · from {Ip.toString src.ip}:{src.port}" else ""}"
  if announced != "" then
    IO.println s!"announced    {announced}"
  -- ---- the store and the processes that fill it
  if !peek then
    let existing ← Sys.readFile s!"{dir}/state.json" 65536
    if existing.size != 0 && !replace then
      fail s!"{dir} already holds a store (slot {RunBlock.jsonField existing "slot" 0}); pass --replace to overwrite it"
    Sys.mkdir dir
    Sys.unlink s!"{dir}/state.json"
  let page ← Sys.mmapShared (4096 * workers.toUInt64)
  let seedBytes ← IO.getRandomBytes 8
  let seed := Wire.u64 seedBytes 0
  let mut pipes : Array UInt64 := Array.emptyWithCapacity workers
  let mut outbox : Array ByteArray := Array.emptyWithCapacity workers
  if !peek then
    Sys.ignoreBrokenPipes
    let mut readEnds : Array UInt64 := Array.emptyWithCapacity workers
    for _ in [0:workers] do
      let (reading, writing) ← Sys.pipe
      Sys.setPipeSize writing 1048576
      readEnds := readEnds.push reading
      pipes := pipes.push writing
      outbox := outbox.push (ByteArray.emptyWithCapacity 1200000)
    for w in [0:workers] do
      let pid ← Sys.fork
      if pid == 0 then
        Sys.dieWithParent
        -- a worker keeps only its own pipe's reading end: while any writing end is open, no pipe ever ends
        for k in [0:workers] do
          Sys.close pipes[k]!
          if k != w then
            Sys.close readEnds[k]!
        Sys.close src.fd
        worker dir w seed readEnds[w]! (page + 4096 * w.toUInt64)
        Sys.exit 0
      if Sys.isErr pid then
        fail "cannot start a worker process"
    for fd in readEnds do
      Sys.close fd
  -- ---- the stream: bytes → Zstandard → tar → accounts
  let tty ← Sys.isTty 2
  let started ← Sys.nowMs
  let mut lastShown := started
  let mut d := Zstd.Decoder.create
  let mut buf := ByteArray.empty
  let mut o := 0
  -- 0 = at a header, 1 = inside an account file, 2 = waiting for all of a small file, 3 = skipping
  let mut mode := 0
  let mut slot : UInt64 := 0
  let mut remaining := 0
  let mut skip := 0
  let mut entryName := ""
  let mut entrySize := 0
  let mut files := 0
  let mut routed : UInt64 := 0
  let mut trailing := 0
  let mut manifest := Snapshot.Manifest.failed "the archive has no manifest"
  let mut version := ""
  let mut finished := false
  let mut error := ""
  let mut pipeBroken := false
  while !finished && error == "" do
    let (nextSrc, chunk) ← src.next
    src := nextSrc
    if chunk.size == 0 then
      break
    let (nextD, out) := d.feed chunk
    d := nextD
    if d.error != "" then
      error := s!"not a valid Zstandard stream: {d.error}"
      break
    -- what is left of the last round, then the new bytes
    if o == buf.size then
      buf := out
    else if o == 0 then
      buf := buf ++ out
    else
      buf := buf.extract o buf.size ++ out
    o := 0
    let mut waiting := false
    while !waiting && !finished && error == "" do
      if mode == 0 then
        if o + 512 > buf.size then
          waiting := true
        else
          let h := Tar.header buf o
          o := o + 512
          if h.kind == 0 then
            error := "the archive is damaged: a file header does not check out"
          else if h.kind == 3 then
            finished := true
          else if h.kind == 2 then
            mode := 3
            skip := Tar.padded h.size
          else
            match Snapshot.fileSlot h.name with
            | some s =>
              mode := 1
              slot := s
              remaining := h.size
              skip := Tar.padded h.size - h.size
              files := files + 1
            | none =>
              if h.size > 0x100000000 then
                error := s!"{h.name} is too large to be what it should be"
              mode := 2
              entryName := h.name
              entrySize := h.size
      else if mode == 1 then
        -- accounts, for as long as whole ones are here
        let fileEnd := o + remaining
        let limit := if fileEnd < buf.size then fileEnd else buf.size
        let a := Snapshot.stored buf o limit
        if a.ok then
          if !peek then
            let w := Accounts.shardOf buf a.pubkey workers
            let pending := outbox[w]!
            outbox := outbox.set! w ByteArray.empty
            let mut grown := Wire.putU64 pending slot
            grown := buf.copySlice o grown grown.size (a.data + a.dataLen - o)
            if grown.size >= 1048576 then
              if !(← Sys.writeFully pipes[w]! grown) then
                pipeBroken := true
              grown := ByteArray.emptyWithCapacity 1200000
            outbox := outbox.set! w grown
          routed := routed + 1
          let stop := if a.next < fileEnd then a.next else fileEnd
          remaining := remaining - (stop - o)
          o := stop
        else if a.dataLen == Wire.bad then
          error := s!"an account in the file of slot {slot} is larger than any account can be"
        else if limit == fileEnd then
          -- what is left of the file is less than an account
          trailing := trailing + remaining
          o := fileEnd
          remaining := 0
        else
          waiting := true
        if remaining == 0 && !waiting then
          mode := 3
      else if mode == 2 then
        if o + Tar.padded entrySize > buf.size then
          waiting := true
        else
          let content := buf.extract o (o + entrySize)
          o := o + Tar.padded entrySize
          mode := 0
          if entryName == "version" then
            version := String.fromUTF8! content
            if version != "1.2.0" then
              error := s!"snapshot format {version} is not one this client knows (1.2.0)"
          else if entryName == "snapshots/status_cache" then
            if !peek then
              let _ ← Sys.writeFileAtomic s!"{dir}/status_cache.bin" content
          else if entrySize >= 1024 && manifest.error != "" then
            manifest := Snapshot.parse content
            if manifest.error != "" then
              error := manifest.error
            else
              printManifest manifest
              if namedSlot != 0 && namedSlot != manifest.slot then
                error := s!"the archive is named for slot {namedSlot} but holds slot {manifest.slot}"
              if !peek then
                let _ ← Sys.writeFileAtomic s!"{dir}/manifest.bin" content
                -- the log needs the accounts' data and 96 bytes for each account
                let free ← Sys.freeSpace dir
                IO.println s!"disk         {size free} free in {dir} (the store takes 88 bytes per account and its data with the zeros squeezed out)"
              if peek then
                finished := true
      else
        let step := if buf.size - o < skip then buf.size - o else skip
        o := o + step
        skip := skip - step
        if skip == 0 then
          mode := 0
        else
          waiting := true
    -- how it is going
    let now ← Sys.nowMs
    if now - lastShown >= 2000 && error == "" then
      lastShown := now
      let mut failed := pipeBroken
      for w in [0:workers] do
        if (← Mem.load64 (page + 4096 * w.toUInt64 + 64)) != 0 then
          failed := true
      if failed then
        error := s!"a worker could not write to {dir} (is the disk full?)"
      let seconds := (now - started) / 1000 + 1
      let share := if src.total != 0 then s!" of {size src.total} ({src.received * 100 / src.total}%)" else ""
      progress tty s!"read {size src.received}{share} · {size (src.received / seconds)}/s · unpacked {size d.total.toUInt64} · {Fmt.thousands routed} accounts from {Fmt.thousands files.toUInt64} files"
  if tty then
    let _ ← Sys.write 2 "\r".toUTF8
  if error == "" && src.error != "" then
    error := src.error
  if error == "" && !finished && !peek then
    error := "the archive ends early"
  -- ---- let the workers finish
  if !peek then
    for w in [0:workers] do
      if outbox[w]!.size != 0 && error == "" then
        if !(← Sys.writeFully pipes[w]! outbox[w]!) then
          error := s!"a worker stopped early"
      Sys.close pipes[w]!
    let mut left := workers
    while left > 0 do
      let (pid, status) ← Sys.waitChild
      if pid == 0 then
        break
      left := left - 1
      if status != 0 && error == "" then
        error := s!"a worker process ended abnormally (status {status})"
  if error != "" then
    IO.println s!"result       FAILED: {error}"
    Sys.exit 1
  if peek then
    IO.println s!"lattice hash {Base58.encode (Blake3.hash manifest.ltHash)}{if expect != "" then (if Base58.encode (Blake3.hash manifest.ltHash) == expect then " (as the archive is named)" else s!" (the archive is named {expect}!)") else ""}"
    IO.println "result       manifest read; accounts not loaded (--peek)"
    return
  -- ---- add up what the workers found
  let mut sum := LtHash.zero
  let mut received : UInt64 := 0
  let mut distinct : UInt64 := 0
  let mut live : UInt64 := 0
  let mut replaced : UInt64 := 0
  let mut late : UInt64 := 0
  let mut lamports : UInt64 := 0
  let mut dataBytes : UInt64 := 0
  let mut logBytes : UInt64 := 0
  let mut closed : UInt64 := 0
  for w in [0:workers] do
    let p := page + 4096 * w.toUInt64
    if (← Mem.load64 (p + 64)) != 0 || (← Mem.load64 (p + 72)) != 1 then
      IO.println s!"result       FAILED: worker {w} did not finish its shard (is the disk full?)"
      Sys.exit 1
    received := received + (← Mem.load64 p)
    distinct := distinct + (← Mem.load64 (p + 8))
    live := live + (← Mem.load64 (p + 16))
    replaced := replaced + (← Mem.load64 (p + 24))
    late := late + (← Mem.load64 (p + 32))
    lamports := lamports + (← Mem.load64 (p + 40))
    dataBytes := dataBytes + (← Mem.load64 (p + 48))
    logBytes := logBytes + (← Mem.load64 (p + 56))
    closed := closed + (← Mem.load64 (p + 80))
    let mut part : Array UInt64 := Array.emptyWithCapacity 256
    for k in [0:256] do
      part := part.push (← Mem.load64 (p + 2048 + 8 * k.toUInt64))
    sum := LtHash.combine sum part false
  let finishedAt ← Sys.nowMs
  let checksum := Base58.encode (LtHash.checksum sum)
  IO.println s!"accounts     {Fmt.thousands received} in {Fmt.thousands files.toUInt64} files · {Fmt.thousands distinct} addresses · {Fmt.thousands live} hold lamports, {Fmt.thousands closed} are closed"
  IO.println s!"             {Fmt.thousands (replaced + late)} were older versions of an account that appears again, and were dropped"
  if trailing != 0 then
    IO.println s!"             {trailing} bytes at the ends of files were not accounts"
  IO.println s!"lattice hash {checksum}, from every account"
  -- every comparison is reported; the first that fails is the verdict
  let mut wrong := ""
  if manifest.ltHash.size != 2048 then
    wrong := "the manifest records no lattice hash to compare with"
  else if LtHash.bytes sum != manifest.ltHash then
    wrong := "the accounts are not the ones the manifest describes"
    IO.println s!"             ≠ the manifest's ({Base58.encode (Blake3.hash manifest.ltHash)})"
  else
    IO.println "             = the manifest's, all 2048 bytes"
  if expect != "" then
    if checksum != expect then
      IO.println s!"             ≠ the hash {if expect == namedHash then "the snapshot is named after" else "expected"} ({expect})"
      if wrong == "" then
        wrong := "this is not the snapshot expected"
    else
      IO.println s!"             = the hash {if expect == namedHash then "the snapshot is named after" else "expected"}"
  if lamports != manifest.capitalization then
    IO.println s!"lamports     {sol lamports} SOL in the accounts ≠ the supply the manifest records, {sol manifest.capitalization}"
    if wrong == "" then
      wrong := "the accounts do not hold the supply the manifest records"
  else
    IO.println s!"lamports     {sol lamports} SOL in the accounts = the supply the manifest records"
  if dataBytes != manifest.accountsDataLen then
    IO.println s!"data         {Fmt.thousands dataBytes} bytes (the manifest counts {Fmt.thousands manifest.accountsDataLen})"
  else
    IO.println s!"data         {Fmt.thousands dataBytes} bytes = the manifest's count"
  if wrong != "" then
    IO.println s!"result       INVALID: {wrong}"
    Sys.exit 1
  let state := "{\n" ++ s!"  \"slot\": {manifest.slot},\n  \"hash\": \"{checksum}\",\n  \"bankHash\": \"{Base58.encode manifest.hash}\",\n" ++
    s!"  \"format\": 2,\n  \"shards\": {workers},\n  \"seed\": \"{Hex.encode seedBytes}\",\n  \"accounts\": {live},\n  \"lamports\": {lamports},\n  \"logBytes\": {logBytes}\n" ++ "}\n"
  if !(← Sys.writeFileAtomic s!"{dir}/state.json" state.toUTF8) then
    IO.println s!"result       FAILED: cannot write {dir}/state.json"
    Sys.exit 1
  IO.println s!"store        {dir}: {workers} shards, {size logBytes}"
  IO.println s!"result       verified and stored in {Fmt.tenths ((finishedAt - started) / 100)} s{if src.reconnects != 0 then s!" ({src.reconnects} reconnections)" else ""}"

/-- `leansol account ADDRESS`: looks an account up in a store. -/
def account : IO Unit := do
  let argc ← Sys.argc
  let mut dir := "accounts"
  let mut address := ""
  let mut dataFile := ""
  let mut i := 2
  while i < argc do
    let a ← Sys.arg i
    if a == "--accounts" && i + 1 < argc then
      dir := ← Sys.arg (i + 1)
      i := i + 2
    else if a == "--data" && i + 1 < argc then
      dataFile := ← Sys.arg (i + 1)
      i := i + 2
    else
      address := a
      i := i + 1
  let key := Base58.decode address
  if key.size != 32 then
    fail s!"'{address}' is not an address\n{usage}"
  let state ← Sys.readFile s!"{dir}/state.json" 65536
  if state.size == 0 then
    fail s!"{dir} holds no store (load one with: leansol snapshot)"
  let shards := (RunBlock.number (RunBlock.jsonField state "shards" 0)).toNat
  -- (the seed is kept as sixteen hexadecimal digits: as a decimal number it may not fit what the number reader accepts)
  let seedBytes := Hex.decode (RunBlock.jsonField state "seed" 0)
  let seed := Wire.u64 seedBytes 0
  if shards == 0 || seedBytes.size != 8 then
    fail s!"{dir}/state.json is not readable"
  if RunBlock.jsonField state "format" 0 != "2" then
    fail s!"{dir} was written in another format of the store; load the snapshot again"
  let id := Accounts.shardOf key 0 shards
  let shard ← Accounts.Shard.openRead dir id seed
  if shard.failed then
    fail s!"cannot open shard {id} of {dir}"
  let (_, loc) ← shard.locate ByteArray.empty key 0
  if loc == Accounts.none_ then
    IO.println s!"{address}: no such account at slot {RunBlock.jsonField state "slot" 0}"
    Sys.exit 1
  let r ← shard.recordAt ByteArray.empty loc
  let data := Accounts.recData r
  let dataLen := Accounts.recDataLen r
  if r.size < Accounts.headerSize || data.size != dataLen then
    fail s!"the record of {address} in shard {id} is damaged"
  IO.println s!"address      {address}"
  IO.println s!"lamports     {Accounts.recLamports r} ({sol (Accounts.recLamports r)} SOL)"
  IO.println s!"owner        {Base58.encode (r.extract 32 64)}"
  IO.println s!"executable   {Accounts.recExecutable r}"
  IO.println s!"rent epoch   {Accounts.recRentEpoch r}"
  IO.println s!"data         {Fmt.thousands dataLen.toUInt64} bytes{if dataLen != 0 then s!" · sha256 {Hex.encode (Sha256.hash data)}" else ""}"
  if dataFile != "" then
    let _ ← Sys.writeFileAtomic dataFile data
  IO.println s!"last written slot {Accounts.recSlot r} (store of slot {RunBlock.jsonField state "slot" 0})"

end RunSnapshot
