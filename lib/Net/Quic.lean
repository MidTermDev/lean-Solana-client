import Net.Tls
import Crypto.Aes

/-!
# QUIC, as far as validators speak it to each other

Validators exchange their consensus votes as QUIC datagrams (RFC 9000, 9001,
9221): unreliable messages inside a connection whose two ends have proven
who they are by a TLS 1.3 handshake, each with its identity key. This file
is such a connection, without streams, which validators do not use here.

A UDP datagram holds one or more packets. A packet belongs to one of three
levels, each with its own keys and its own numbering: initial (keys anyone
can derive from the connection id; it carries the first two handshake
messages), handshake (keys from the secret just agreed; the rest of the
handshake), and application (everything after). A packet's payload is
sealed (AES-128-GCM) under a key, with the packet's number making each
sealing different; and the number itself and a few bits of the first byte
are masked with a second key and a sample of the sealed bytes. The payload
is frames: handshake bytes, acknowledgements, datagrams, and housekeeping.

A connection here is a value: a datagram goes in, the connection and the
datagrams to send in answer come out. Sockets and clocks are the caller's.
-/

namespace Quic

-- ------------------------------------------------------ numbers of variable length

/-- A number in 1, 2, 4 or 8 bytes: the first two bits say which. -/
def putVar (b : ByteArray) (v : UInt64) : ByteArray := Id.run do
  let width := if v < 64 then 1 else if v < 16384 then 2 else if v < 1073741824 then 4 else 8
  let tag : UInt64 := if width == 1 then 0 else if width == 2 then 0x40 else if width == 4 then 0x80 else 0xc0
  let mut out := b
  for i in [0:width] do
    let byte := (v >>> (8 * (width - 1 - i)).toUInt64) &&& 0xff
    out := out.push (if i == 0 then byte ||| tag else byte).toUInt8
  return out

/-- The number at `o` and where what follows it starts: past the end of `b` if it is cut short. -/
def varAt (b : ByteArray) (o : Nat) : UInt64 × Nat := Id.run do
  if o >= b.size then
    return (0, b.size + 1)
  let width := 1 <<< (b[o]! >>> 6).toNat
  if o + width > b.size then
    return (0, b.size + 1)
  let mut v := (b[o]! &&& 0x3f).toUInt64
  for i in [1:width] do
    v := (v <<< 8) ||| b[o + i]!.toUInt64
  return (v, o + width)

-- ------------------------------------------------------------------- keys and packets

/-- What protects one direction at one level: the cipher's round keys, the base of its nonces, and the round keys that mask headers. -/
structure Keys where
  key : ByteArray
  iv : ByteArray
  header : ByteArray
  deriving Inhabited

def noKeys : Keys := ⟨ByteArray.empty, ByteArray.empty, ByteArray.empty⟩

def keysOf (secret : ByteArray) : Keys :=
  ⟨Aes.roundKeys (Hkdf.expandLabel secret "quic key" ByteArray.empty 16), Hkdf.expandLabel secret "quic iv" ByteArray.empty 12,
    Aes.roundKeys (Hkdf.expandLabel secret "quic hp" ByteArray.empty 16)⟩

/-- The keys of the initial level, which only keep out who has not seen the first packet: from the
connection id the client first addressed the server by. -/
def initialKeys (id : ByteArray) (server : Bool) : Keys :=
  keysOf (Hkdf.expandLabel (Hkdf.extract (Hex.decode "38762cf7f55934b34d179ae6a4c80cadccbb7f0a") id)
    (if server then "server in" else "client in") ByteArray.empty 32)

def nonce (iv : ByteArray) (number : UInt64) : ByteArray := Id.run do
  let mut n := iv
  for i in [0:8] do
    n := n.set! (4 + i) (n[4 + i]! ^^^ (number >>> (56 - 8 * i).toUInt64).toUInt8)
  return n

def be32 (b : ByteArray) (v : UInt64) : ByteArray :=
  (((b.push (v >>> 24).toUInt8).push (v >>> 16).toUInt8).push (v >>> 8).toUInt8).push v.toUInt8

/-- The header of a packet of the initial (0) or handshake (1) level: the form, version 1, both
connection ids, the length of what follows, and the packet's number in four bytes. -/
def longHeader (level : Nat) (to from_ : ByteArray) (number : UInt64) (payload : Nat) : ByteArray :=
  let b := be32 (ByteArray.empty.push (if level == 0 then 0xc3 else 0xe3)) 1
  let ids := ((b.push to.size.toUInt8) ++ to).push from_.size.toUInt8 ++ from_
  be32 (putVar (if level == 0 then ids.push 0 else ids) (payload + 20).toUInt64) number

def shortHeader (to : ByteArray) (number : UInt64) : ByteArray := be32 ((ByteArray.empty.push 0x43) ++ to) number

/-- A packet: the header (ending in the four bytes of the number), the payload sealed with the header
vouched for, and then the number and the low bits of the first byte masked. -/
def protect (k : Keys) (header : ByteArray) (number : UInt64) (payload : ByteArray) : ByteArray := Id.run do
  let numberAt := header.size - 4
  let mut packet := header ++ Aes.shut k.key (nonce k.iv number) header payload
  let mask := Aes.encrypt k.header packet (numberAt + 4)
  packet := packet.set! 0 (packet[0]! ^^^ (mask[0]! &&& (if packet[0]! &&& 0x80 != 0 then 0x0f else 0x1f)))
  for i in [0:4] do
    packet := packet.set! (numberAt + i) (packet[numberAt + i]! ^^^ mask[1 + i]!)
  return packet

/-- A packet taken out of a datagram. `level` is 3 for a packet that cannot be read (no keys for it,
or it does not open); `next` is where the following packet starts. -/
structure Packet where
  level : Nat
  number : UInt64
  payload : ByteArray
  next : Nat
  /-- (initial and handshake packets) the sender's connection id -/
  source : ByteArray

/-- The packet at `o` in datagram `d`. `ownId` is the size of the connection id the other side addresses
this one by; `keys` and `expected` (one more than the highest number received) are per level. -/
def packetAt (d : ByteArray) (o ownId : Nat) (keys : Array Keys) (expected : Array UInt64) : Packet := Id.run do
  let unread : Packet := ⟨3, 0, ByteArray.empty, d.size, ByteArray.empty⟩
  if o >= d.size then
    return unread
  let first := d[o]!
  let long := first &&& 0x80 != 0
  let mut level := 2
  let mut numberAt := o + 1 + ownId
  let mut stop := d.size
  let mut source := ByteArray.empty
  if long then
    if o + 7 > d.size then
      return unread
    let toSize := d[o + 5]!.toNat
    if o + 7 + toSize > d.size then
      return unread
    let fromSize := d[o + 6 + toSize]!.toNat
    let mut p := o + 7 + toSize + fromSize
    source := d.extract (o + 7 + toSize) p
    let kind := (first >>> 4) &&& 3
    if kind == 0 then
      let (token, after) := varAt d p
      p := after + token.toNat
    let (length, after) := varAt d p
    if after > d.size || after + length.toNat > d.size || kind == 3 then
      return unread
    numberAt := after
    stop := after + length.toNat
    level := if kind == 0 then 0 else if kind == 2 then 1 else 3
  if level == 3 || keys[level]!.key.size == 0 || numberAt + 20 > stop then
    return { unread with next := stop }
  let k := keys[level]!
  let mask := Aes.encrypt k.header d (numberAt + 4)
  let opened := first ^^^ (mask[0]! &&& (if long then 0x0f else 0x1f))
  let width := (opened &&& 3).toNat + 1
  let mut header := (d.extract o (numberAt + width)).set! 0 opened
  let mut short : UInt64 := 0
  for i in [0:width] do
    let byte := d[numberAt + i]! ^^^ mask[1 + i]!
    header := header.set! (numberAt - o + i) byte
    short := (short <<< 8) ||| byte.toUInt64
  -- the full number is the one nearest the next expected whose low bytes are those sent
  let window : UInt64 := 1 <<< (8 * width).toUInt64
  let want := expected[level]!
  let near := (want &&& ~~~(window - 1)) ||| short
  let number := if near + window / 2 <= want then near + window
    else if near > want + window / 2 && near >= window then near - window else near
  match Aes.unshut k.key (nonce k.iv number) header (d.extract (numberAt + width) stop) with
  | none => return { unread with next := stop }
  | some payload => return ⟨level, number, payload, stop, source⟩

-- ------------------------------------------------------------------- what has arrived

/-- The numbers received, as ranges (highest, lowest), the highest range first, with `number` added. -/
def noted (seen : Array UInt64) (number : UInt64) : Array UInt64 := Id.run do
  if seen.size == 0 then
    return #[number, number]
  if number == seen[0]! + 1 then
    return seen.set! 0 number
  if number > seen[0]! then
    -- a gap: a new first range (and only so many are remembered)
    let mut out : Array UInt64 := #[number, number]
    for i in [0:(if seen.size > 30 then 30 else seen.size)] do
      out := out.push seen[i]!
    return out
  -- an old number: joined to the range it touches, or dropped (it is acknowledged late or not at all)
  let mut out := seen
  for r in [0:seen.size / 2] do
    if number + 1 == seen[2 * r + 1]! then
      out := out.set! (2 * r + 1) number
  return out

def hasSeen (seen : Array UInt64) (number : UInt64) : Bool := Id.run do
  for r in [0:seen.size / 2] do
    if number <= seen[2 * r]! && number >= seen[2 * r + 1]! then
      return true
  return false

/-- The frame that acknowledges those numbers (nothing if there are none). -/
def acknowledgement (seen : Array UInt64) : ByteArray := Id.run do
  if seen.size == 0 then
    return ByteArray.empty
  let mut b := putVar (putVar (putVar (putVar (ByteArray.empty.push 2) seen[0]!) 0) (seen.size / 2 - 1).toUInt64) (seen[0]! - seen[1]!)
  for r in [1:seen.size / 2] do
    b := putVar (putVar b (seen[2 * r - 1]! - seen[2 * r]! - 2)) (seen[2 * r]! - seen[2 * r + 1]!)
  return b

/-- One level of a connection. -/
structure Space where
  send : Keys
  recv : Keys
  /-- the number of the next packet sent, and one more than the highest received -/
  next : UInt64
  expected : UInt64
  seen : Array UInt64
  /-- something arrived that wants acknowledging -/
  owed : Bool
  /-- the handshake's bytes received at this level, in order; how many of them TLS has had; and pieces
  that came ahead of their turn (eight bytes of offset, then the bytes) -/
  inbound : ByteArray
  taken : Nat
  ahead : Array ByteArray
  /-- the handshake's bytes this side sends at this level, and how many of them have gone out -/
  outbound : ByteArray
  gone : Nat
  deriving Inhabited

def newSpace : Space :=
  ⟨noKeys, noKeys, 0, 0, Array.emptyWithCapacity 8, false, ByteArray.empty, 0, Array.emptyWithCapacity 2, ByteArray.empty, 0⟩

/-- Handshake bytes arriving at `offset`: appended if they are next (and any waiting pieces after them), kept if early. -/
def Space.arrived (s : Space) (offset : Nat) (data : ByteArray) : Space := Id.run do
  let mut inbound := s.inbound
  let mut ahead := s.ahead
  if offset > inbound.size then
    ahead := ahead.push (Fast.push64 ByteArray.empty offset.toUInt64 ++ data)
  else if offset + data.size > inbound.size then
    inbound := inbound ++ data.extract (inbound.size - offset) data.size
  for _ in [0:ahead.size] do
    for piece in ahead do
      let at_ := (Fast.le64 piece 0).toNat
      if at_ <= inbound.size && at_ + piece.size - 8 > inbound.size then
        inbound := inbound ++ piece.extract (8 + inbound.size - at_) piece.size
  return { s with inbound := inbound, ahead := ahead }

-- ------------------------------------------------------------------- a connection

/-- A parameter of the transport, as each side tells the other in its first handshake message. -/
def parameter (id : UInt64) (value : ByteArray) : ByteArray := putVar (putVar ByteArray.empty id) value.size.toUInt64 ++ value

/-- This side's parameters: idle for 30 seconds at most, datagrams of any size taken, no streams. A
server also repeats the id the client first addressed it by (`first`; empty for a client). -/
def parameters (ownId first : ByteArray) : ByteArray :=
  (if first.size == 0 then ByteArray.empty else parameter 0x00 first)
    ++ parameter 0x01 (putVar ByteArray.empty 30000) ++ parameter 0x03 (putVar ByteArray.empty 1452)
    ++ parameter 0x04 (putVar ByteArray.empty 1048576) ++ parameter 0x0f ownId ++ parameter 0x20 (putVar ByteArray.empty 65535)

/-- One end of a connection. -/
structure Conn where
  server : Bool
  spaces : Array Space
  /-- the connection ids: the one the other side is addressed by, and this side's own -/
  theirs : ByteArray
  ours : ByteArray
  tls : Tls.Session
  /-- this side's identity key: its seed and its public half -/
  seed : ByteArray
  identity : ByteArray
  /-- the handshake is complete and both sides know it; (server) the client is still to be told so -/
  established : Bool
  toConfirm : Bool
  closed : Bool
  /-- (when closed from this side) the other side is still to be told -/
  farewell : Bool
  error : String
  /-- datagrams received and not yet collected -/
  received : Array ByteArray
  /-- an answer owed to a probe of the path -/
  probe : ByteArray
  deriving Inhabited

def Conn.close (c : Conn) (why : String) : Conn :=
  if c.closed then c else { c with closed := true, farewell := true, error := why }

/-- A packet of `level` with these frames (must not be empty), numbered next. -/
def Conn.packet (c : Conn) (level : Nat) (frames : ByteArray) : Conn × ByteArray :=
  let s := c.spaces[level]!
  -- (enough bytes after the number for the header's mask to be drawn from)
  let payload := if frames.size < 4 then Fast.pushZeros frames (4 - frames.size) else frames
  let header := if level == 2 then shortHeader c.theirs s.next else longHeader level c.theirs c.ours s.next payload.size
  ({ c with spaces := c.spaces.set! level { s with next := s.next + 1 } }, protect s.send header s.next payload)

/-- The handshake bytes of `level` from `from_` on, as a frame. -/
def cryptoFrame (bytes : ByteArray) (from_ : Nat) : ByteArray :=
  putVar (putVar (ByteArray.empty.push 6) from_.toUInt64) (bytes.size - from_).toUInt64 ++ bytes.extract from_ bytes.size

/-- The first datagram a client sends: its hello in an initial packet, filled up to 1,200 bytes as the
first packets of a connection must be. -/
def Conn.opening (c : Conn) : Conn × ByteArray :=
  let hello := cryptoFrame c.spaces[0]!.outbound 0
  let header := longHeader 0 c.theirs c.ours 0 0
  let (d, packet) := c.packet 0 (Fast.pushZeros hello (1200 - header.size - 16 - hello.size))
  ({ d with spaces := d.spaces.set! 0 { d.spaces[0]! with gone := d.spaces[0]!.outbound.size } }, packet)

/-- A client's end of a new connection, and its first datagram. `random` and `secret` are 32 fresh
bytes each, `ownId` and `theirId` 8 fresh bytes each; `name` is the server's name and `protocol` what
is to be spoken over the connection. -/
def connect (random secret ownId theirId seed identity : ByteArray) (name protocol : String) : Conn × ByteArray :=
  let (tls, hello) := Tls.hello random secret name protocol (parameters ownId ByteArray.empty)
  let first := { newSpace with send := initialKeys theirId false, recv := initialKeys theirId true, outbound := hello }
  let c : Conn := ⟨false, #[first, newSpace, newSpace], theirId, ownId, tls, seed, identity, false, false, false, false, "", Array.emptyWithCapacity 8, ByteArray.empty⟩
  c.opening

/-- A server's end of a connection a client is opening with the datagram `d`, which is then to be
given to `receive`; none if `d` does not begin with a client's first packet. `random` and `secret` are
32 fresh bytes each, `ownId` 8. -/
def accept (d random secret ownId seed identity : ByteArray) (protocol : String) : Option Conn :=
  if d.size < 1200 || d[0]! &&& 0xf0 != 0xc0 || d[5]!.toNat < 8 || 7 + d[5]!.toNat > d.size then none
  else
    let first := d.extract 6 (6 + d[5]!.toNat)
    let space := { newSpace with send := initialKeys first true, recv := initialKeys first false }
    some ⟨true, #[space, newSpace, newSpace], ByteArray.empty, ownId, Tls.session true random secret protocol (parameters ownId first),
      seed, identity, false, false, false, false, "", Array.emptyWithCapacity 8, ByteArray.empty⟩

/-- Takes the frames of a packet that arrived at `level`. -/
def Conn.frames (c0 : Conn) (level : Nat) (payload : ByteArray) : Conn := Id.run do
  let mut c := c0
  let mut o := 0
  let mut wantsAnswer := false
  while o < payload.size && !c.closed do
    let kind := payload[o]!
    o := o + 1
    if kind == 0 then
      continue
    if kind == 2 || kind == 3 then
      -- an acknowledgement: the highest number, a delay, how many further ranges, the first range, the ranges
      let (_, a) := varAt payload o
      let (_, b) := varAt payload a
      let (ranges, d) := varAt payload b
      let (_, e) := varAt payload d
      o := e
      for _ in [0:(if ranges > 1000 then 1000 else ranges.toNat) * 2 + (if kind == 3 then 3 else 0)] do
        let (_, after) := varAt payload o
        o := after
      continue
    if kind == 0x1c || kind == 0x1d then
      -- the other side closes: an error code, (the frame at fault,) a reason
      let (code, a) := varAt payload o
      let (_, b) := if kind == 0x1c then varAt payload a else (0, a)
      let (size, d) := varAt payload b
      let mut reason := ByteArray.emptyWithCapacity size.toNat
      for i in [d:(if d + size.toNat < payload.size then d + size.toNat else payload.size)] do
        reason := reason.push (if payload[i]! >= 32 && payload[i]! < 127 then payload[i]! else 63)
      c := { c with closed := true, error := s!"closed by the other side, code {code}{if kind == 0x1d then " (application)" else ""}: {String.fromUTF8! reason}" }
      continue
    wantsAnswer := true
    if kind == 1 then
      continue
    if kind == 6 then
      let (offset, a) := varAt payload o
      let (size, b) := varAt payload a
      o := b + size.toNat
      if o <= payload.size then
        c := { c with spaces := c.spaces.set! level (c.spaces[level]!.arrived offset.toNat (payload.extract b o)) }
    else if kind == 7 then
      let (size, a) := varAt payload o
      o := a + size.toNat
    else if kind == 0x18 then
      -- another connection id to address them by: its sequence number, which to retire, the id, a reset token
      let (_, a) := varAt payload o
      let (_, b) := varAt payload a
      o := b + 1 + (if b < payload.size then payload[b]!.toNat else 0) + 16
    else if kind == 0x1a then
      c := { c with probe := payload.extract o (o + 8) }
      o := o + 8
    else if kind == 0x1b then
      o := o + 8
    else if kind == 0x1e then
      c := { c with established := true }
    else if kind == 0x30 then
      c := { c with received := c.received.push (payload.extract o payload.size) }
      o := payload.size
    else if kind == 0x31 then
      let (size, a) := varAt payload o
      o := a + size.toNat
      if o <= payload.size then
        c := { c with received := c.received.push (payload.extract a o) }
    else if kind == 0x10 || kind == 0x12 || kind == 0x13 || kind == 0x14 || kind == 0x16 || kind == 0x17 || kind == 0x19 then
      -- limits on data and streams, and ids retired: one number each
      let (_, a) := varAt payload o
      o := a
    else if kind == 0x11 || kind == 0x15 || kind == 0x05 then
      let (_, a) := varAt payload o
      let (_, b) := varAt payload a
      o := b
    else if kind == 0x04 then
      let (_, a) := varAt payload o
      let (_, b) := varAt payload a
      let (_, d) := varAt payload b
      o := d
    else if kind >= 0x08 && kind <= 0x0f then
      -- a stream's bytes: none are wanted, and they are passed over
      let (_, a) := varAt payload o
      let (_, b) := if kind &&& 4 != 0 then varAt payload a else (0, a)
      let (size, d) := if kind &&& 2 != 0 then varAt payload b else ((payload.size - b).toUInt64, b)
      o := d + size.toNat
    else
      c := c.close s!"a frame of an unknown kind, {kind}"
    if o > payload.size then
      c := c.close "a frame runs past the end of its packet"
  if wantsAnswer then
    c := { c with spaces := c.spaces.set! level { c.spaces[level]! with owed := true } }
  return c

/-- Hands TLS the handshake messages that have arrived whole at `level`, and takes from it the keys of
the next levels and what is to be sent. -/
def Conn.handshake (c0 : Conn) (level : Nat) : Conn := Id.run do
  let mut c := c0
  for _ in [0:16] do
    let s := c.spaces[level]!
    if c.closed || level == 2 || s.taken + 4 > s.inbound.size then
      return c
    let size := 4 + Tls.number s.inbound (s.taken + 1) 3
    if s.taken + size > s.inbound.size then
      return c
    let stage := c.tls.stage
    let (tls, early, late) := c.tls.take (s.inbound.extract s.taken (s.taken + size)) c.seed c.identity
    c := { c with tls := tls, spaces := c.spaces.set! level { s with taken := s.taken + size } }
    if tls.stage == 9 then
      return c.close tls.error
    let mine := if c.server then tls.serverHandshake else tls.clientHandshake
    let yours := if c.server then tls.clientHandshake else tls.serverHandshake
    if stage == 0 && tls.stage == 1 then
      let second := { c.spaces[1]! with send := keysOf mine, recv := keysOf yours, outbound := late }
      c := { c with spaces := (c.spaces.set! 0 { c.spaces[0]! with outbound := early }).set! 1 second }
      if c.server then
        -- (a server may speak at the last level at once, but listens there only when the client has proven itself)
        c := { c with spaces := c.spaces.set! 2 { c.spaces[2]! with send := keysOf tls.serverTraffic } }
    if tls.stage == 2 && c.server then
      c := { c with established := true, toConfirm := true, spaces := c.spaces.set! 2 { c.spaces[2]! with recv := keysOf tls.clientTraffic } }
    if tls.stage == 2 && !c.server then
      let last := { c.spaces[2]! with send := keysOf tls.clientTraffic, recv := keysOf tls.serverTraffic }
      c := { c with spaces := (c.spaces.set! 1 { c.spaces[1]! with outbound := late }).set! 2 last }
  return c

/-- What there is to send now, as one datagram or none: at each level an acknowledgement if one is
owed and any handshake bytes not yet sent; at the last also the server's word that the handshake is
done and an answer to a probe. A server's initial packet is filled up so that the datagram has 1,200
bytes, as the first packets of a connection must. -/
def Conn.flush (c0 : Conn) : Conn × Array ByteArray := Id.run do
  let mut c := c0
  let mut out := ByteArray.empty
  for step in [0:3] do
    -- (the initial level last, when it is known how much the others take)
    let level := if step == 2 then 0 else step + 1
    let s := c.spaces[level]!
    let more := s.gone < s.outbound.size
    if s.send.key.size != 0 && (level != 0 || (c.server && c.tls.stage == 1 && more))
        && (s.owed || more || (level == 2 && (c.probe.size == 8 || c.toConfirm))) then
      let mut frames := acknowledgement s.seen
      if more then
        frames := frames ++ cryptoFrame s.outbound s.gone
      if level == 2 && c.toConfirm then
        frames := frames.push 0x1e
        c := { c with toConfirm := false }
      if level == 2 && c.probe.size == 8 then
        frames := (frames.push 0x1b) ++ c.probe
        c := { c with probe := ByteArray.empty }
      if frames.size == 0 then
        frames := frames.push 1
      if level == 0 then
        let used := (longHeader 0 c.theirs c.ours 0 1200).size + frames.size + 16 + out.size
        frames := Fast.pushZeros frames (if used < 1200 then 1200 - used else 0)
      c := { c with spaces := c.spaces.set! level { s with owed := false, gone := s.outbound.size } }
      let (d, packet) := c.packet level frames
      c := d
      out := if level == 0 then packet ++ out else out ++ packet
  return (c, if out.size == 0 then Array.emptyWithCapacity 0 else #[out])

/-- A datagram arrives: the connection after it, and the datagrams to send in answer. -/
def Conn.receive (c0 : Conn) (d : ByteArray) : Conn × Array ByteArray := Id.run do
  let mut c := c0
  let mut o := 0
  for _ in [0:8] do
    if o < d.size && !c.closed then
      let keys := #[c.spaces[0]!.recv, c.spaces[1]!.recv, c.spaces[2]!.recv]
      let p := packetAt d o c.ours.size keys #[c.spaces[0]!.expected, c.spaces[1]!.expected, c.spaces[2]!.expected]
      o := if p.next > o then p.next else d.size
      if p.level < 3 && !(hasSeen c.spaces[p.level]!.seen p.number) then
        let s := c.spaces[p.level]!
        c := { c with spaces := c.spaces.set! p.level { s with seen := noted s.seen p.number, expected := if p.number + 1 > s.expected then p.number + 1 else s.expected } }
        -- (from its first packet on the server is addressed by the id it chose)
        if p.level < 2 && p.source.size != 0 then
          c := { c with theirs := p.source }
        c := (c.frames p.level p.payload).handshake p.level
  if c.closed then
    -- (closed here over something the other side sent: it is told so, once, with the code for a failed handshake)
    if !c.farewell then
      return (c, Array.emptyWithCapacity 0)
    let level := if c.spaces[2]!.send.key.size != 0 && c.established then 2 else if c.spaces[1]!.send.key.size != 0 then 1 else 0
    let (after, packet) := c.packet level (putVar (ByteArray.empty.push 0x1c) 0x128 ++ (ByteArray.empty.push 0).push 0)
    return ({ after with farewell := false }, #[packet])
  return c.flush

/-- When nothing has come for a while during the handshake: what was last sent is sent again, in new packets. -/
def Conn.again (c : Conn) : Conn × Array ByteArray :=
  if c.closed || c.established || (c.server && c.tls.stage != 1) then (c, Array.emptyWithCapacity 0)
  else if c.spaces[1]!.send.key.size == 0 then
    let (d, packet) := ({ c with spaces := c.spaces.set! 0 { c.spaces[0]! with gone := 0 } }).opening
    (d, #[packet])
  else ({ c with spaces := (c.spaces.set! 0 { c.spaces[0]! with gone := 0 }).set! 1 { c.spaces[1]! with gone := 0, owed := true } }).flush

/-- A datagram to send over an established connection, carrying `payload`. -/
def Conn.datagram (c : Conn) (payload : ByteArray) : Conn × ByteArray :=
  let s := c.spaces[2]!
  let d := { c with spaces := c.spaces.set! 2 { s with owed := false } }
  d.packet 2 (acknowledgement s.seen ++ putVar (ByteArray.empty.push 0x31) payload.size.toUInt64 ++ payload)

/-- A packet that keeps the connection alive, or one that ends it. -/
def Conn.ping (c : Conn) : Conn × ByteArray := c.packet 2 ((acknowledgement c.spaces[2]!.seen).push 1)

def Conn.goodbye (c : Conn) : Conn × ByteArray :=
  let level := if c.spaces[2]!.send.key.size != 0 then 2 else if c.spaces[1]!.send.key.size != 0 then 1 else 0
  ({ c with closed := true, error := "closed here" }).packet level ((((ByteArray.empty.push 0x1c).push 0).push 0).push 0)

end Quic
