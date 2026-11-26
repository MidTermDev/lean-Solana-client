import Crypto.Sha256
import Crypto.Sha512
import Encoding.Hex

/-! Hashes every message length from 0 to 300 bytes, so that each padding
case (length field fits / spills into an extra block) is exercised, and
folds the digests into one. The expected values come from Python's hashlib. -/

def main : IO Unit := do
  let mut msg := ByteArray.empty
  let mut acc256 := ByteArray.empty
  let mut acc512 := ByteArray.empty
  for i in [0:301] do
    acc256 := Sha256.hash (acc256 ++ Sha256.hash msg)
    acc512 := Sha512.hash (acc512 ++ Sha512.hash msg)
    msg := msg.push (i * 7 + 1).toUInt8
  IO.println (Hex.encode acc256)
  IO.println (Hex.encode acc512)
