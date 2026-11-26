/-! # Hexadecimal encoding -/

namespace Hex

def digit (n : UInt8) : UInt8 := if n < 10 then 48 + n else 87 + n

/-- Lower-case hex string of `b`. -/
def encode (b : ByteArray) : String := Id.run do
  let mut out := ByteArray.emptyWithCapacity (b.size * 2)
  for x in b do
    out := out.push (digit (x >>> 4))
    out := out.push (digit (x &&& 15))
  return String.fromUTF8! out

def value (c : UInt8) : UInt8 :=
  if c >= 48 && c <= 57 then c - 48
  else if c >= 97 && c <= 102 then c - 87
  else if c >= 65 && c <= 70 then c - 55
  else 0

/-- Decodes a hex string (no separators, even length). -/
def decode (s : String) : ByteArray := Id.run do
  let raw := s.toUTF8
  let mut out := ByteArray.emptyWithCapacity (raw.size / 2)
  for i in [0:raw.size / 2] do
    out := out.push ((value raw[2 * i]! <<< 4) ||| value raw[2 * i + 1]!)
  return out

end Hex
