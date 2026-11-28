import Crypto.Hkdf
import Crypto.X25519
import Crypto.Ed25519

/-!
# The TLS 1.3 handshake, as QUIC uses it

QUIC carries TLS's handshake messages itself and takes from TLS only the
keys. So this is the handshake and nothing else (RFC 8446): two sides agree
on a secret (X25519), each proves it holds the key in its certificate by
signing everything said so far (Ed25519), and each closes with a keyed hash
of the same. Every key comes from the agreed secret and a hash of the
messages up to some point (HKDF, SHA-256).

Only what Solana's validators use with each other is here: one cipher suite
(AES-128-GCM with SHA-256), one group, one kind of signature, and both sides
showing a certificate. A validator's certificate is a fixed form around its
identity key; nothing in it is checked but that key, which is what its
signature in the handshake proves.
-/

namespace Tls

def be16 (b : ByteArray) (v : Nat) : ByteArray := (b.push (v / 256).toUInt8).push (v % 256).toUInt8

/-- `body` behind its length, written in `width` bytes. -/
def framed (width : Nat) (body : ByteArray) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (body.size + width)
  for i in [0:width] do
    b := b.push (body.size >>> (8 * (width - 1 - i))).toUInt8
  return b ++ body

/-- A handshake message: its kind, its length in three bytes, its body. -/
def message (kind : UInt8) (body : ByteArray) : ByteArray := (ByteArray.empty.push kind) ++ framed 3 body

def extension (kind : Nat) (body : ByteArray) : ByteArray := be16 ByteArray.empty kind ++ framed 2 body

/-- The number in `width` bytes at `o`, most significant first; 0 past the end. -/
def number (b : ByteArray) (o width : Nat) : Nat := Id.run do
  let mut v := 0
  for i in [0:width] do
    v := v * 256 + (if o + i < b.size then b[o + i]!.toNat else 0)
  return v

/-- The body of the extension of this kind in a list of extensions (kind, length, body, ...), or empty. -/
def extensionIn (list : ByteArray) (kind : Nat) : ByteArray := Id.run do
  let mut o := 0
  while o + 4 <= list.size do
    let size := number list (o + 2) 2
    if number list o 2 == kind then
      return list.extract (o + 4) (o + 4 + size)
    o := o + 4 + size
  return ByteArray.empty

/-- A validator's certificate: a fixed X.509 form around its identity key. Its own signature is not
one; the key's holder is proven by the handshake. -/
def certificate (identity : ByteArray) : ByteArray :=
  Hex.decode ("3081f63081a9a003020102020801010101010101013005060" ++ "32b657030163114301206035504030c0b536f6c616e61206e6f6465"
    ++ "3020170d3730303130313030303030305a180f34303936303130313030303030305a3000302a300506032b6570032100")
  ++ identity
  ++ Hex.decode ("a329302730170603551d110101ff040d300b82096c6f63616c686f7374300c0603551d130101ff04023000300506032b6570034100"
    ++ "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff")

/-- The Ed25519 key a certificate holds: the 32 bytes after the header of a public key of that kind. -/
def keyIn (cert : ByteArray) : ByteArray := Id.run do
  let header := Hex.decode "302a300506032b6570032100"
  let mut found := ByteArray.empty
  for o in [0:cert.size] do
    if found.size == 0 && o + 44 <= cert.size && Fast.sameAt cert o header 0 12 then
      found := cert.extract (o + 12) (o + 44)
  return found

/-- What a certificate's holder signs: a fixed preamble, who is signing, and the hash of the handshake so far. -/
def toSign (server : Bool) (transcript : ByteArray) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 130
  for _ in [0:64] do
    b := b.push 0x20
  return (b ++ (if server then "TLS 1.3, server CertificateVerify" else "TLS 1.3, client CertificateVerify").toUTF8).push 0
    ++ Sha256.hash transcript

/-- A secret for a named purpose, bound to the handshake up to `transcript`. -/
def derive (secret : ByteArray) (label : String) (transcript : ByteArray) : ByteArray :=
  Hkdf.expandLabel secret label (Sha256.hash transcript) 32

/-- The keyed hash that closes a side's part of the handshake. -/
def finished (secret transcript : ByteArray) : ByteArray :=
  Hkdf.hmac (Hkdf.expandLabel secret "finished" ByteArray.empty 32) (Sha256.hash transcript)

def zeros32 : ByteArray := Fast.zeroed 32 32

/-- The secret both handshake keys come from: the agreed secret, mixed into the fixed start of the schedule. -/
def handshakeSecret (shared : ByteArray) : ByteArray :=
  Hkdf.extract (derive (Hkdf.extract zeros32 zeros32) "derived" ByteArray.empty) shared

/-- The secret the keys for everything after the handshake come from. -/
def masterSecret (handshake : ByteArray) : ByteArray :=
  Hkdf.extract (derive handshake "derived" ByteArray.empty) zeros32

/-- One side of a handshake in progress. `stage`: 0 before the first answer, 1 the keys of the
handshake are known, 2 it is complete, 9 it failed (`error` says how). -/
structure Session where
  server : Bool
  /-- 32 fresh bytes for the hello, 32 for the key agreement -/
  random : ByteArray
  secret : ByteArray
  /-- what is to be spoken over the connection, and this side's QUIC transport parameters -/
  protocol : String
  own : ByteArray
  transcript : ByteArray
  stage : Nat
  /-- the secrets that protect the rest of the handshake, client's and server's -/
  clientHandshake : ByteArray
  serverHandshake : ByteArray
  master : ByteArray
  /-- the secrets that protect everything after it -/
  clientTraffic : ByteArray
  serverTraffic : ByteArray
  /-- (client) the server asked for a certificate, with this context to echo -/
  asked : Bool
  context : ByteArray
  /-- the other side's identity key, once its signature has been checked -/
  peer : ByteArray
  /-- the other side's QUIC transport parameters -/
  parameters : ByteArray
  error : String
  deriving Inhabited

def Session.fail (s : Session) (why : String) : Session := { s with stage := 9, error := why }

/-- A session that has said nothing yet. -/
def session (server : Bool) (random secret : ByteArray) (protocol : String) (own : ByteArray) : Session :=
  ⟨server, random, secret, protocol, own, ByteArray.empty, 0, ByteArray.empty, ByteArray.empty, ByteArray.empty, ByteArray.empty,
    ByteArray.empty, false, ByteArray.empty, ByteArray.empty, ByteArray.empty, ""⟩

/-- The client's first message, and the session that sent it. `name` is the server's name. -/
def hello (random secret : ByteArray) (name protocol : String) (parameters : ByteArray) : Session × ByteArray :=
  let extensions := extension 0 (framed 2 ((ByteArray.empty.push 0) ++ framed 2 name.toUTF8))
    ++ extension 10 (framed 2 (be16 ByteArray.empty 0x001d))
    ++ extension 13 (framed 2 (be16 ByteArray.empty 0x0807))
    ++ extension 16 (framed 2 (framed 1 protocol.toUTF8))
    ++ extension 43 (framed 1 (be16 ByteArray.empty 0x0304))
    ++ extension 51 (framed 2 (be16 ByteArray.empty 0x001d ++ framed 2 (X25519.public_ secret)))
    ++ extension 57 parameters
  let body := be16 ByteArray.empty 0x0303 ++ random ++ (ByteArray.empty.push 0) ++ framed 2 (be16 ByteArray.empty 0x1301)
    ++ (ByteArray.empty.push 1).push 0 ++ framed 2 extensions
  let m := message 1 body
  ({ session false random secret protocol parameters with transcript := m }, m)

/-- Is `wanted` one of the items of `list`, each `width` bytes behind a length of `lengths` bytes (0: no length)? -/
def listed (list : ByteArray) (lengths : Nat) (wanted : ByteArray) : Bool := Id.run do
  let mut o := 0
  while o + lengths < list.size do
    let size := if lengths == 0 then wanted.size else number list o lengths
    if size == wanted.size && Fast.sameAt list (o + lengths) wanted 0 size then
      return true
    o := o + lengths + size
  return false

/-- A certificate message for `identity`, and the signature message that follows it, over `transcript` and the certificate. -/
def proof (server : Bool) (context transcript seed identity : ByteArray) : ByteArray :=
  let cert := message 11 (framed 1 context ++ framed 3 (framed 3 (certificate identity) ++ framed 2 ByteArray.empty))
  cert ++ message 15 (be16 ByteArray.empty 0x0807 ++ framed 2 (Ed25519.sign seed identity (toSign server (transcript ++ cert))))

/-- (server) Answers the client's hello: the server's own hello, which goes out at the initial level,
and everything else the server has to say, which goes out at the handshake's: the protocol and its
parameters, a request for the client's certificate, its own certificate and signature, its closing hash. -/
def Session.answer (s : Session) (m seed identity : ByteArray) : Session × ByteArray × ByteArray := Id.run do
  let nothing := ByteArray.empty
  let body := m.extract 4 m.size
  if m.size < 44 || m[0]! != 1 then
    return (s.fail "the client's first message is not a hello", nothing, nothing)
  let suitesAt := 35 + body[34]!.toNat
  let afterSuites := suitesAt + 2 + number body suitesAt 2
  let extensionsAt := afterSuites + 1 + (if afterSuites < body.size then body[afterSuites]!.toNat else 0)
  let extensions := body.extract (extensionsAt + 2) (extensionsAt + 2 + number body extensionsAt 2)
  -- its key share for the one group spoken here
  let shares := extensionIn extensions 51
  let mut theirs := ByteArray.empty
  let mut o := 2
  while o + 4 <= shares.size do
    let size := number shares (o + 2) 2
    if number shares o 2 == 0x001d && size == 32 then
      theirs := shares.extract (o + 4) (o + 36)
    o := o + 4 + size
  let protocols := extensionIn extensions 16
  if theirs.size != 32 || !(listed (body.extract (suitesAt + 2) afterSuites) 0 (be16 ByteArray.empty 0x1301))
      || !(listed (protocols.extract 2 protocols.size) 1 s.protocol.toUTF8) then
    return (s.fail "the client offers no cipher, group or protocol spoken here", nothing, nothing)
  let hello := message 2 (be16 ByteArray.empty 0x0303 ++ s.random ++ body.extract 34 suitesAt ++ be16 ByteArray.empty 0x1301
    ++ (ByteArray.empty.push 0) ++ framed 2 (extension 43 (be16 ByteArray.empty 0x0304)
      ++ extension 51 (be16 ByteArray.empty 0x001d ++ framed 2 (X25519.public_ s.secret))))
  let mut transcript := m ++ hello
  let hs := handshakeSecret (X25519.multiply s.secret theirs)
  let clientHandshake := derive hs "c hs traffic" transcript
  let serverHandshake := derive hs "s hs traffic" transcript
  let mut flight := message 8 (framed 2 (extension 16 (framed 2 (framed 1 s.protocol.toUTF8)) ++ extension 57 s.own))
    ++ message 13 ((ByteArray.empty.push 0) ++ framed 2 (extension 13 (framed 2 (be16 ByteArray.empty 0x0807))))
  flight := flight ++ proof true ByteArray.empty (transcript ++ flight) seed identity
  flight := flight ++ message 20 (finished serverHandshake (transcript ++ flight))
  transcript := transcript ++ flight
  let master := masterSecret hs
  return ({ s with transcript := transcript, stage := 1, clientHandshake := clientHandshake, serverHandshake := serverHandshake, master := master, clientTraffic := derive master "c ap traffic" transcript, serverTraffic := derive master "s ap traffic" transcript, parameters := extensionIn extensions 57 }, hello, flight)

/-- Takes one of the other side's messages, whole, in order. Returns what is to be sent in answer, at
the initial level and at the handshake's: for a client nothing until the server's part is complete,
then its certificate (if asked for), its signature and its closing hash; for a server its whole part
on the client's hello, and nothing after. `seed` and `identity` are this side's Ed25519 key. -/
def Session.take (s : Session) (m seed identity : ByteArray) : Session × ByteArray × ByteArray := Id.run do
  let nothing := ByteArray.empty
  if m.size < 4 || s.stage >= 2 then
    return (s.fail "a handshake message out of place", nothing, nothing)
  let kind := m[0]!
  let body := m.extract 4 m.size
  if s.server && s.stage == 0 then
    return s.answer m seed identity
  if s.stage == 0 then
    -- ServerHello: version, random, the session id echoed, the cipher suite, extensions with its key share
    if kind != 2 || body.size < 40 then
      return (s.fail "the server's first message is not a hello", nothing, nothing)
    let o := 35 + body[34]!.toNat
    let share := extensionIn (body.extract (o + 5) body.size) 51
    if number body o 2 != 0x1301 || number share 0 2 != 0x001d || share.size != 36 then
      return (s.fail "the server chose a cipher or a group that is not offered", nothing, nothing)
    let transcript := s.transcript ++ m
    let hs := handshakeSecret (X25519.multiply s.secret (share.extract 4 36))
    return ({ s with transcript := transcript, stage := 1, clientHandshake := derive hs "c hs traffic" transcript, serverHandshake := derive hs "s hs traffic" transcript, master := masterSecret hs }, nothing, nothing)
  if kind == 8 && !s.server then
    -- EncryptedExtensions: the protocol chosen and the server's transport parameters
    return ({ s with transcript := s.transcript ++ m, parameters := extensionIn (body.extract 2 body.size) 57 }, nothing, nothing)
  if kind == 13 && !s.server then
    -- CertificateRequest
    return ({ s with transcript := s.transcript ++ m, asked := true, context := body.extract 1 (1 + body[0]!.toNat) }, nothing, nothing)
  if kind == 11 then
    -- Certificate: a context, then a list whose first entry is the sender's own
    let o := 1 + body[0]!.toNat
    let cert := body.extract (o + 6) (o + 6 + number body (o + 3) 3)
    return ({ s with transcript := s.transcript ++ m, peer := keyIn cert }, nothing, nothing)
  if kind == 15 then
    -- CertificateVerify: the sender's signature of everything up to its certificate
    if number body 0 2 != 0x0807 || s.peer.size != 32
        || !(Ed25519.verify s.peer (body.extract 4 (4 + number body 2 2)) (toSign (!s.server) s.transcript)) then
      return (s.fail "the other side's signature does not hold", nothing, nothing)
    return ({ s with transcript := s.transcript ++ m }, nothing, nothing)
  if kind == 20 && s.server then
    -- the client's closing hash; it must have shown its certificate first
    if s.peer.size != 32 || body != finished s.clientHandshake s.transcript then
      return (s.fail "the client's closing hash does not fit, or it showed no certificate", nothing, nothing)
    return ({ s with stage := 2 }, nothing, nothing)
  if kind == 20 then
    if body != finished s.serverHandshake s.transcript then
      return (s.fail "the server's closing hash does not fit", nothing, nothing)
    let upTo := s.transcript ++ m
    let mut out := if s.asked then proof false s.context upTo seed identity else ByteArray.empty
    out := out ++ message 20 (finished s.clientHandshake (upTo ++ out))
    return ({ s with transcript := upTo ++ out, stage := 2, clientTraffic := derive s.master "c ap traffic" upTo, serverTraffic := derive s.master "s ap traffic" upTo }, nothing, out)
  return (s.fail s!"handshake message {kind} is not expected", nothing, nothing)

end Tls
