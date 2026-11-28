import Net.Quic
import Encoding.Hex
import Encoding.Base58

/-! The transport validators exchange votes over: QUIC datagrams inside a connection opened by a TLS 1.3
handshake in which each side proves its identity key.

First the ciphers under it, on published values (RFC 2104, 5869, 7748, FIPS 197, the GCM
specification's test case 4, and RFC 9001's keys for a first packet). Then two ends of a connection,
talking to each other in memory with fixed randomness: the handshake, datagrams both ways, and what
is refused. The same code completes this handshake with mainnet's validators (`leansol quic`). -/

def h (s : String) : ByteArray := Hex.decode s
def key (name : String) : ByteArray := Sha256.hash name.toUTF8
def short (b : ByteArray) : String := Hex.encode ((Sha256.hash b).extract 0 8)

/-- Gives each datagram of `mail` to `to`, and collects what it sends back. -/
def deliver (to : Quic.Conn) (mail : Array ByteArray) : Quic.Conn × Array ByteArray := Id.run do
  let mut c := to
  let mut back : Array ByteArray := Array.emptyWithCapacity 2
  for d in mail do
    let (after, answers) := c.receive d
    c := after
    for a in answers do
      back := back.push a
  return (c, back)

def sizes (mail : Array ByteArray) : String := Id.run do
  let mut s := ""
  for d in mail do
    s := s ++ s!" {d.size} bytes ({short d})"
  return if s == "" then " nothing" else s

def ranges (seen : Array UInt64) : String := Id.run do
  let mut s := ""
  for r in [0:seen.size / 2] do
    s := s ++ s!" {seen[2 * r + 1]!}-{seen[2 * r]!}"
  return s

def main : IO Unit := do
  IO.println s!"hmac          {Hex.encode (Hkdf.hmac "key".toUTF8 "The quick brown fox jumps over the lazy dog".toUTF8)}"
  let prk := Hkdf.extract (h "000102030405060708090a0b0c") (h "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b")
  IO.println s!"hkdf extract  {Hex.encode prk}"
  IO.println s!"hkdf expand   {Hex.encode (Hkdf.expand prk (h "f0f1f2f3f4f5f6f7f8f9") 32)}"
  IO.println s!"aes block     {Hex.encode (Aes.encrypt (Aes.roundKeys (h "000102030405060708090a0b0c0d0e0f")) (h "00112233445566778899aabbccddeeff") 0)}"
  let gk := Aes.roundKeys (h "feffe9928665731c6d6a8f9467308308")
  let nonce := h "cafebabefacedbaddecaf888"
  let extra := h "feedfacedeadbeeffeedfacedeadbeefabaddad2"
  let sealed := Aes.shut gk nonce extra (h "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39")
  IO.println s!"gcm sealed    {Hex.encode sealed}"
  IO.println s!"gcm opens: {(Aes.unshut gk nonce extra sealed).isSome}; with a bit of the text changed: {(Aes.unshut gk nonce extra (sealed.set! 3 (sealed[3]! ^^^ 1))).isSome}; of what it vouches for: {(Aes.unshut gk nonce (extra.set! 0 0) sealed).isSome}"
  IO.println s!"x25519        {Hex.encode (X25519.multiply (h "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4") (h "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"))}"
  let alice := h "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"
  let bob := h "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb"
  IO.println s!"two sides agree on {Hex.encode (X25519.multiply alice (X25519.public_ bob))}: {X25519.multiply alice (X25519.public_ bob) == X25519.multiply bob (X25519.public_ alice)}"
  let first := Quic.initialKeys (h "8394c8f03e515708") false
  IO.println s!"a first packet's keys: key {Hex.encode ((Hkdf.expandLabel (Hkdf.expandLabel (Hkdf.extract (h "38762cf7f55934b34d179ae6a4c80cadccbb7f0a") (h "8394c8f03e515708")) "client in" ByteArray.empty 32) "quic key" ByteArray.empty 16))}, iv {Hex.encode first.iv}"
  IO.println s!"numbers of variable length: {Hex.encode (Quic.putVar (Quic.putVar (Quic.putVar (Quic.putVar ByteArray.empty 37) 15293) 494878333) 151288809941952652)}, read back {(Quic.varAt (h "9d7f3e7d") 0).1}"
  IO.println s!"numbers received 0 1 2 5 6 9, then 4: {ranges (Quic.noted (Quic.noted (Quic.noted (Quic.noted (Quic.noted (Quic.noted (Quic.noted #[] 0) 1) 2) 5) 6) 9) 4)}"

  -- two validators, a connection from one to the other
  let clientSeed := key "a validator"
  let serverSeed := key "another validator"
  let client := Ed25519.publicKey clientSeed
  let server := Ed25519.publicKey serverSeed
  IO.println s!"client {Base58.encode client}, server {Base58.encode server}"
  IO.println s!"a certificate: {(Tls.certificate client).size} bytes ({short (Tls.certificate client)}), and the key in it is the client's: {Tls.keyIn (Tls.certificate client) == client}"
  let (c0, hello) := Quic.connect (key "r1") (key "r2") ((key "id1").extract 0 8) ((key "id2").extract 0 8) clientSeed client "10.0.0.2.8010.sol" "alpenglow-v1"
  IO.println s!"the client's first datagram: {hello.size} bytes ({short hello})"
  match Quic.accept hello (key "r3") (key "r4") ((key "id3").extract 0 8) serverSeed server "alpenglow-v1" with
  | none => IO.println "the server does not take it for the opening of a connection"
  | some s0 =>
    let (s1, m1) := deliver s0 #[hello]
    IO.println s!"the server answers:{sizes m1}; keys agreed: {s1.tls.stage == 1}"
    let (c1, m2) := deliver c0 m1
    IO.println s!"the client answers:{sizes m2}; its handshake is complete: {c1.tls.stage == 2}; the server is who it should be: {c1.tls.peer == server}"
    let (s2, m3) := deliver s1 m2
    IO.println s!"the server answers:{sizes m3}; complete: {s2.established}; the client is who it should be: {s2.tls.peer == client}"
    let (c2, m4) := deliver c1 m3
    IO.println s!"the client answers:{sizes m4}; the server has confirmed: {c2.established}"
    let (s3, m5) := deliver s2 m4
    IO.println s!"the server answers:{sizes m5}"
    -- datagrams both ways
    let (c3, vote) := c2.datagram "a vote".toUTF8
    let (s4, _) := deliver s3 #[vote]
    IO.println s!"a datagram to the server: {vote.size} bytes; it has {s4.received.size}: {String.fromUTF8! s4.received[0]!}"
    let (s5, reply) := s4.datagram "another".toUTF8
    let (c4, _) := deliver c3 #[reply]
    IO.println s!"one back: the client has {c4.received.size}: {String.fromUTF8! c4.received[0]!}"
    let (s6, _) := deliver s5 #[vote]
    IO.println s!"the same packet again: the server has {s6.received.size}"
    let (c5, second) := c4.datagram "a second vote".toUTF8
    let (s7, _) := deliver s6 #[second.set! 20 (second[20]! ^^^ 1)]
    let (s8, _) := deliver s7 #[second]
    IO.println s!"a packet with a bit changed: the server has {s7.received.size}; as sent: {s8.received.size}"
    let (c6, ping) := c5.ping
    let (s9, acks) := deliver s8 #[ping]
    IO.println s!"a ping is answered:{sizes acks}"
    let (_, bye) := c6.goodbye
    let (s10, _) := deliver s9 #[bye]
    IO.println s!"the client closes: {s10.closed}, {s10.error}"

    -- what is refused, and what is sent again
    match Quic.accept hello (key "r3") (key "r4") ((key "id3").extract 0 8) serverSeed server "solana-tpu" with
    | none => IO.println "no server"
    | some other =>
      let (refused, m) := deliver other #[hello]
      IO.println s!"a server that speaks something else: {refused.error};{sizes m}"
    IO.println s!"a datagram that opens nothing: {(Quic.accept (hello.extract 0 600) (key "r3") (key "r4") ((key "id3").extract 0 8) serverSeed server "alpenglow-v1").isSome}"
    let (lost, again) := c0.again
    let (s11, m6) := deliver s0 again
    let (c7, m7) := deliver lost m6
    let (s12, _) := deliver s11 m7
    IO.println s!"the first datagram lost and sent again:{sizes again}; then the handshake completes: {c7.tls.stage == 2 && s12.established}"
    let (s13, again2) := s1.again
    let (c8, m8) := deliver c0 again2
    let (s14, _) := deliver s13 m8
    IO.println s!"the server's answer lost and sent again:{sizes again2}; then the handshake completes: {c8.tls.stage == 2 && s14.established}"
