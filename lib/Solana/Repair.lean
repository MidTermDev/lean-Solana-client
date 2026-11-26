import Crypto.Sha256
import Crypto.Ed25519
import Solana.Wire

/-!
# Repair: asking a node for shreds

Shreds normally arrive unasked, relayed from node to node. A node that
missed some asks for them: a small signed request naming a slot and a shred
index, answered with that shred. Before answering a stranger a node sends a
ping, and expects the hash of its token signed back, as in gossip.

A request is: kind, signature, sender, recipient, time, nonce, slot, and
for the two "window" kinds a shred index. The signature covers everything
but itself. The answer is the shred with the request's nonce appended.
-/

namespace Repair

/-- A shred at exactly this index. -/
def windowIndex : UInt64 := 8
/-- The highest-indexed shred the node has at or after this index: how to learn where a block ends. -/
def highestWindowIndex : UInt64 := 9

def request (kind : UInt64) (seed pubkey recipient : ByteArray) (nowMs nonce slot index : UInt64) : ByteArray :=
  let head := Wire.putU32 (ByteArray.emptyWithCapacity 4) kind
  let body := Wire.putU64 (Wire.putU64 (Wire.putU32 (Wire.putU64 (pubkey ++ recipient) nowMs) nonce) slot) index
  head ++ Ed25519.sign seed pubkey (head ++ body) ++ body

/-- A ping is 132 bytes: kind 0, the sender, a 32-byte token, and the sender's signature of the token. -/
def isPing (p : ByteArray) : Bool :=
  p.size == 132 && Wire.u32 p 0 == 0 && Ed25519.verify (p.extract 4 36) (p.extract 68 132) (p.extract 36 68)

/-- The answer to a ping: the hash of its token, signed. -/
def pong (seed pubkey ping : ByteArray) : ByteArray :=
  let h := Sha256.hash ("SOLANA_PING_PONG".toUTF8 ++ ping.extract 36 68)
  (Wire.putU32 (ByteArray.emptyWithCapacity 132) 7 ++ pubkey ++ h) ++ Ed25519.sign seed pubkey h

end Repair
