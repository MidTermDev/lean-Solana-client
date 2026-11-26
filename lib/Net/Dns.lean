import Sys
import Net.Ip
import Solana.Wire

/-!
# A tiny DNS stub resolver

Just enough DNS to turn `entrypoint.mainnet-beta.solana.com` into an IPv4
address: one A query over UDP to the system's nameserver, and a walk over
the answer section. No libc `getaddrinfo`, no resolver library.
-/

namespace Dns

/-- The first IPv4 `nameserver` in /etc/resolv.conf, or 1.1.1.1. -/
def nameserver : IO UInt32 := do
  let conf ← Sys.readFile "/etc/resolv.conf" 8192
  let key := "nameserver".toUTF8
  let mut lineStart := 0
  for i in [0:conf.size + 1] do
    if i == conf.size || conf[i]! == 10 then
      if Wire.eqAt conf lineStart key 0 key.size then
        let mut s := lineStart + key.size
        while s < i && (conf[s]! == 32 || conf[s]! == 9) do
          s := s + 1
        let mut e := s
        while e < i && conf[e]! != 32 && conf[e]! != 9 && conf[e]! != 13 do
          e := e + 1
        let ip := Ip.parseAt conf s e
        if ip != 0 then
          return ip
      lineStart := i + 1
  return 0x01010101

/-- The wire form of an A/IN query for `host`. -/
def query (host : String) (id : UInt16) : ByteArray := Id.run do
  let name := host.toUTF8
  let mut q := ByteArray.emptyWithCapacity 64
  q := q.push (id >>> 8).toUInt8
  q := q.push id.toUInt8
  -- flags: recursion desired; one question
  for x in #[(1 : UInt8), 0, 0, 1, 0, 0, 0, 0, 0, 0] do
    q := q.push x
  let mut start := 0
  for i in [0:name.size + 1] do
    if i == name.size || name[i]! == 46 then
      q := q.push (i - start).toUInt8
      for j in [start:i] do
        q := q.push name[j]!
      start := i + 1
  q := q.push 0
  for x in #[(0 : UInt8), 1, 0, 1] do
    q := q.push x
  return q

/-- Skips a (possibly compressed) domain name. -/
def skipName (b : ByteArray) (o : Nat) : Nat := Id.run do
  let mut p := o
  for _ in [0:128] do
    if p >= b.size then
      return Wire.bad
    let len := b[p]!
    if len == 0 then
      return p + 1
    if len &&& 0xC0 == 0xC0 then
      return Wire.adv b p 2
    p := p + 1 + len.toNat
  return Wire.bad

/-- The first A record in a response to query `id`, or 0. -/
def firstA (b : ByteArray) (id : UInt16) : UInt32 := Id.run do
  if b.size < 12 || b[0]! != (id >>> 8).toUInt8 || b[1]! != id.toUInt8 then
    return 0
  let qd := (b[4]!.toNat <<< 8) ||| b[5]!.toNat
  let an := (b[6]!.toNat <<< 8) ||| b[7]!.toNat
  let mut o := 12
  for _ in [0:qd] do
    o := Wire.adv b (skipName b o) 4
  for _ in [0:an] do
    o := skipName b o
    if !(Wire.ok (Wire.adv b o 10)) then
      return 0
    let ty := (b[o]!.toNat <<< 8) ||| b[o + 1]!.toNat
    let rdlen := (b[o + 8]!.toNat <<< 8) ||| b[o + 9]!.toNat
    let rdata := o + 10
    o := Wire.adv b rdata rdlen
    if !(Wire.ok o) then
      return 0
    if ty == 1 && rdlen == 4 then
      return (b[rdata]!.toUInt32 <<< 24) ||| (b[rdata + 1]!.toUInt32 <<< 16) |||
        (b[rdata + 2]!.toUInt32 <<< 8) ||| b[rdata + 3]!.toUInt32
  return 0

/-- Resolves a host name (or dotted-quad literal) to an IPv4 address; 0 on failure. -/
def resolve (host : String) : IO UInt32 := do
  let literal := Ip.parse host
  if literal != 0 then
    return literal
  let ns ← nameserver
  let fd ← Sys.udpSocket
  if Sys.isErr fd then
    return 0
  Sys.setTimeout fd 20 1500
  let rnd ← IO.getRandomBytes 2
  let id := (rnd[0]!.toUInt16 <<< 8) ||| rnd[1]!.toUInt16
  let mut answer : UInt32 := 0
  for _ in [0:3] do
    let _ ← Sys.sendTo fd ns 53 (query host id)
    let reply ← Sys.recvFrom fd 1500
    answer := firstA reply.data id
    if answer != 0 then
      break
  Sys.close fd
  return answer

end Dns
