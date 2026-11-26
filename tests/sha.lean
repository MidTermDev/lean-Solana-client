import Crypto.Sha256
import Crypto.Sha512
import Encoding.Hex

def million : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity 1000000
  for _ in [0:1000000] do
    b := b.push 97
  return b

def main : IO Unit := do
  IO.println (Hex.encode (Sha256.hash "abc".toUTF8))
  IO.println (Hex.encode (Sha256.hash "".toUTF8))
  IO.println (Hex.encode (Sha256.hash "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq".toUTF8))
  IO.println (Hex.encode (Sha512.hash "abc".toUTF8))
  IO.println (Hex.encode (Sha512.hash "".toUTF8))
  IO.println (Hex.encode (Sha256.hash million))
  IO.println (Hex.encode (Sha512.hash million))
  IO.println (Hex.encode (Hex.decode "00ff10AB"))
