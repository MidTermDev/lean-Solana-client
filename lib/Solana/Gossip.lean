import Sys
import Crypto.Sha256
import Crypto.Ed25519
import Solana.Wire
import Solana.Crds

/-!
# The gossip protocol: messages this node sends

A gossip message is a bincode-encoded `Protocol` enum in one UDP datagram:

    0 PullRequest(CrdsFilter, CrdsValue)   "send me what I am missing"
    1 PullResponse(Pubkey, Vec<CrdsValue>)
    2 PushMessage(Pubkey, Vec<CrdsValue>)
    3 PruneMessage
    4 PingMessage(Ping)                    liveness / anti-spoofing challenge
    5 PongMessage(Pong)

To join, a node sends pull requests carrying its own signed `ContactInfo`
and a bloom filter of the record hashes it already holds. Peers first
challenge the sender's address with a ping; once it answers with the right
pong they start replying with the records the filter says are missing.
-/

namespace Gossip

open Wire

/-- The client id this implementation advertises in its version ("LN"). -/
def clientId : UInt64 := 0x4c4e

def versionMajor : UInt64 := 0
def versionMinor : UInt64 := 1
def versionPatch : UInt64 := 0

/-- Our `CrdsData::ContactInfo`: identity, software version, and one socket (gossip). -/
def contactInfo (pubkey : ByteArray) (wallclockMs outsetUs shredVersion : UInt64) (ip : UInt32)
    (port : UInt16) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 128
  b := putU32 b 11
  b := b ++ pubkey
  b := putVarint b wallclockMs
  b := putU64 b outsetUs
  b := putU16 b shredVersion
  b := putVarint b versionMajor
  b := putVarint b versionMinor
  b := putVarint b versionPatch
  b := putU32 b 0
  b := putU32 b 0
  b := putVarint b clientId
  -- one IPv4 address
  b := b.push 1
  b := putU32 b 0
  b := b.push (ip >>> 24).toUInt8
  b := b.push (ip >>> 16).toUInt8
  b := b.push (ip >>> 8).toUInt8
  b := b.push ip.toUInt8
  -- one socket: key 0 (gossip), address 0, port
  b := b.push 1
  b := b.push 0
  b := b.push 0
  b := putVarint b port.toUInt64
  -- no extensions
  b := b.push 0
  return b

/-- A `CrdsValue`: the signature over the data, then the data. -/
def signValue (seed pubkey data : ByteArray) : ByteArray :=
  Ed25519.sign seed pubkey data ++ data

/-- FNV-1a keyed by the bloom key: the hash function of Solana's bloom filters. -/
def fnv (data : ByteArray) (off len : Nat) (key : UInt64) : UInt64 := Id.run do
  let mut h := key
  for i in [off:off + len] do
    h := (h ^^^ data[i]!.toUInt64) * 0x100000001b3
  return h

def bloomBits : Nat := 6144
def bloomKeys : Nat := 3

def zeroBloom : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (bloomBits / 8)
  for _ in [0:bloomBits / 8] do
    b := b.push 0
  return b

/-- Marks the 32-byte hash at `hashes[off ..]` in the filter `bits`. -/
def bloomAdd (bits : ByteArray) (keys : Array UInt64) (hashes : ByteArray) (off : Nat) : ByteArray := Id.run do
  let mut out := bits
  for k in keys do
    let pos := (fnv hashes off 32 k % bloomBits.toUInt64).toNat
    out := out.set! (pos / 8) (out[pos / 8]! ||| ((1 : UInt8) <<< (pos % 8).toUInt8))
  return out

def popcount (bits : ByteArray) : UInt64 := Id.run do
  let mut n : UInt64 := 0
  for x in bits do
    let mut v := x
    while v != 0 do
      n := n + (v &&& 1).toUInt64
      v := v >>> 1
  return n

/-- `Protocol::PullRequest`: a bloom filter over the hashes we hold whose top
`maskBits` bits equal `partition`, plus our signed contact info. -/
def pullRequest (keys : Array UInt64) (bits : ByteArray) (partition : UInt64) (maskBits : UInt64)
    (signedContact : ByteArray) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 1200
  b := putU32 b 0
  -- Bloom { keys: Vec<u64>, bits: BitVec<u64>, num_bits_set: u64 }
  b := putU64 b keys.size.toUInt64
  for k in keys do
    b := putU64 b k
  b := b.push 1
  b := putU64 b (bits.size / 8).toUInt64
  b := b ++ bits
  b := putU64 b (bits.size * 8).toUInt64
  b := putU64 b (popcount bits)
  -- mask: the partition in the top bits, ones below
  let mask := (partition <<< (64 - maskBits)) ||| (0xFFFFFFFFFFFFFFFF >>> maskBits)
  b := putU64 b mask
  b := putU32 b maskBits
  return b ++ signedContact

/-- The response a ping demands: the hash of its token, signed. -/
def pong (seed pubkey token : ByteArray) : ByteArray :=
  let h := Sha256.hash ("SOLANA_PING_PONG".toUTF8 ++ token)
  (putU32 (ByteArray.emptyWithCapacity 132) 5 ++ pubkey ++ h) ++ Ed25519.sign seed pubkey h

/-- What an entrypoint's IP echo service tells us about ourselves. -/
structure Echo where
  ip : UInt32
  shredVersion : UInt64

/-- Asks an entrypoint (over TCP, on its gossip port) for our public IP
address and the cluster's shred version. Both are 0 on failure. -/
def ipEcho (ip : UInt32) (port : UInt16) : IO Echo := do
  let fd ← Sys.tcpSocket
  if Sys.isErr fd then
    return ⟨0, 0⟩
  Sys.setTimeout fd 20 3000
  Sys.setTimeout fd 21 3000
  let r ← Sys.connect fd ip port
  if Sys.isErr r then
    Sys.close fd
    return ⟨0, 0⟩
  -- 4 zero bytes, an empty IpEchoServerMessage (two [u16; 4]), newline
  let mut req := ByteArray.emptyWithCapacity 21
  for _ in [0:20] do
    req := req.push 0
  req := req.push 10
  let _ ← Sys.write fd req
  let mut resp := ByteArray.empty
  for _ in [0:8] do
    if resp.size >= 15 then
      break
    let chunk ← Sys.read fd 64
    if chunk.size == 0 then
      break
    resp := resp ++ chunk
  Sys.close fd
  -- 4 zero bytes, IpAddr (u32 tag + 4 bytes for IPv4), Option<u16> shred version
  if resp.size < 12 || u32 resp 4 != 0 then
    return ⟨0, 0⟩
  let me := ((u8 resp 8 <<< 24) ||| (u8 resp 9 <<< 16) ||| (u8 resp 10 <<< 8) ||| u8 resp 11).toUInt32
  let shred := if u8 resp 12 == 1 then u16 resp 13 else 0
  return ⟨me, shred⟩

end Gossip
