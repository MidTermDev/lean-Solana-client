import Fast
import Crypto.Sha256

/-!
# HMAC-SHA-256 and HKDF

A hash that needs a key (HMAC, RFC 2104), and the two steps that turn shared
secrets into as many keys as a protocol wants (HKDF, RFC 5869): `extract`
makes one good key out of whatever was agreed, `expand` makes named keys out
of that. TLS 1.3 and QUIC derive every key they use this way.
-/

namespace Hkdf

/-- The key, in a block of 64 bytes, each byte combined with `pad`. -/
def padded (key : ByteArray) (pad : UInt8) : ByteArray := Id.run do
  let short := if key.size > 64 then Sha256.hash key else key
  let mut b := ByteArray.emptyWithCapacity 64
  for i in [0:64] do
    b := b.push ((if i < short.size then short[i]! else 0) ^^^ pad)
  return b

/-- HMAC-SHA-256 of `message` under `key`: 32 bytes. -/
def hmac (key message : ByteArray) : ByteArray :=
  Sha256.hash (padded key 0x5c ++ Sha256.hash (padded key 0x36 ++ message))

/-- One key out of a secret and a salt. -/
def extract (salt secret : ByteArray) : ByteArray := hmac salt secret

/-- `length` bytes (up to 32) out of a key, for the purpose `info` names. -/
def expand (key info : ByteArray) (length : Nat) : ByteArray :=
  (hmac key (info.push 1)).extract 0 length

/-- The same as TLS 1.3 words it: the purpose is a label, prefixed "tls13 ", and a context. -/
def expandLabel (key : ByteArray) (label : String) (context : ByteArray) (length : Nat) : ByteArray :=
  let name := "tls13 ".toUTF8 ++ label.toUTF8
  expand key ((((Fast.push16 ByteArray.empty 0).set! 0 (length / 256).toUInt8).set! 1 (length % 256).toUInt8).push name.size.toUInt8
    ++ name ++ (ByteArray.empty.push context.size.toUInt8) ++ context) length

end Hkdf
