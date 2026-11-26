import Solana.Crds
import Solana.Gossip

/-! The wire parsers face untrusted input, so they must never read out of
bounds or overflow, whatever the bytes. This feeds them thousands of random
buffers and randomly corrupted valid records. Under leanc a single bad index
would abort the test; under the official toolchain the digest below would
differ. Both must print the same thing. -/

def next (x : UInt64) : UInt64 :=
  let x := x ^^^ (x <<< 13)
  let x := x ^^^ (x >>> 7)
  x ^^^ (x <<< 17)

def main : IO Unit := do
  let mut rng : UInt64 := 0x243F6A8885A308D3
  let mut accepted := 0
  let mut rejected := 0
  let mut digest : UInt64 := 0
  -- 1. random bytes behind every record kind (and a few invalid kinds)
  for i in [0:6000] do
    rng := next rng
    let len := (rng % 400).toNat
    let mut b := Wire.putU32 (ByteArray.emptyWithCapacity 512) (i % 16).toUInt64
    for _ in [0:len] do
      rng := next rng
      -- mostly small values, so that length prefixes are often plausible
      let v : UInt64 := if rng % 4 == 0 then rng >>> 56 else (rng >>> 56) % 4
      b := b.push v.toUInt8
    let info := Crds.scan b 0
    if Wire.ok info.stop then
      accepted := accepted + 1
      digest := next (digest ^^^ info.stop.toUInt64 ^^^ (info.kind.toUInt64 <<< 32))
    else
      rejected := rejected + 1
  -- 2. a valid ContactInfo with random corruption and truncation
  let pubkey := Sha256.hash "fuzz".toUTF8
  let good := Gossip.contactInfo pubkey 1700000000000 1700000000000000 50093 0x08080808 8001
  let c0 := Crds.parseContact good 4
  IO.println s!"pristine: stop {c0.stop} of {good.size}, shred {c0.shredVersion}, client {c0.client}, port {c0.gossipPort}"
  for _ in [0:6000] do
    rng := next rng
    let mut b := good
    let flips := (rng % 4).toNat
    for _ in [0:flips] do
      rng := next rng
      let pos := (rng % b.size.toUInt64).toNat
      rng := next rng
      b := b.set! pos (rng >>> 56).toUInt8
    rng := next rng
    if rng % 3 == 0 then
      b := b.extract 0 (rng >>> 8 % b.size.toUInt64).toNat
    let info := Crds.scan b 0
    if Wire.ok info.stop then
      let c := Crds.parseContact b info.body
      accepted := accepted + 1
      digest := next (digest ^^^ c.stop.toUInt64 ^^^ c.wallclock ^^^ (c.gossipPort.toUInt64 <<< 40) ^^^ c.client)
    else
      rejected := rejected + 1
  -- 3. the varint reader on arbitrary bytes
  for _ in [0:4000] do
    rng := next rng
    let mut b := ByteArray.emptyWithCapacity 16
    for k in [0:(rng % 12).toNat] do
      b := b.push (rng >>> (k.toUInt64 * 5)).toUInt8
    digest := next (digest ^^^ Wire.varint b 0 ^^^ (Wire.varintLen b 0).toUInt64)
    if Wire.ok (Wire.skipVarint b 0) then
      accepted := accepted + 1
    else
      rejected := rejected + 1
  IO.println s!"accepted {accepted}, rejected {rejected}, digest {digest}"
